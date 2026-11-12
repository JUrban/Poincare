(* ========================================================================= *)
(* pc_mfd_tube: the tubular neighbourhood of a compact embedded manifold     *)
(* f(M) in real^K.                                                           *)
(* MFD_TUBULAR_NEIGHBOURHOOD: unique nearest points within distance d,       *)
(* the smooth nearest-point projection with derivative mfd_tproj on f(M),    *)
(* its fibres, a Lipschitz bound for its derivative, and the smooth          *)
(* retraction onto M; MFD_EMBED_NORMAL_QUADRATIC: f(M) leaves its tangent    *)
(* spaces at most quadratically.  The nearest point is found in a chart by   *)
(* the inverse function theorem applied to Psi(y,z) = (J(y)^T (z - g y), z), *)
(* and the radius is made uniform by compactness.                            *)
(* ========================================================================= *)

needs "src/pc_mfd_embed.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* The normal condition, the first-order condition for nearest points, and   *)
(* the map Psi of the inverse function theorem.                              *)
(* ------------------------------------------------------------------------- *)

let GRGE_TPROJ_KERNEL = prove
 (`!top atlas (f:A->real^K) x w.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_immersion_into atlas f /\ x IN topspace top
        ==> (mfd_tproj atlas f x ** w = vec 0 <=>
             transp(mfd_emb_jac atlas f x) ** w = vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                 `x:A`] GRGE_EMB_JAC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o MATCH_MP GRGE_PROJ_PROPS) THEN
  REWRITE_TAC[GSYM mfd_tproj] THEN STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN
     `transp(mfd_emb_jac (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) x) ** w =
      (transp(mfd_emb_jac atlas f x) ** mfd_tproj atlas f x) ** w`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_RZERO];
    REWRITE_TAC[mfd_tproj; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]]);;

let GRGE_EMB_JAC_TRANSP_KERNEL = prove
 (`!top atlas (f:A->real^K) c x w.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_immersion_into atlas f /\ c IN atlas /\ x IN FST c /\
        transp(mfd_emb_jac atlas f x) ** w = vec 0
        ==> transp(matrix(frechet_derivative (f o chart_inv c) (at (SND c x)))) ** w =
            vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`; `x:A`] GRGE_EMB_JAC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; GSYM MATRIX_VECTOR_MUL_ASSOC;
                  MATRIX_VECTOR_MUL_RZERO]);;

let GRGE_NEAREST_FIRST_ORDER = prove
 (`!top atlas (f:A->real^K) x z.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_immersion_into atlas f /\ x IN topspace top /\
        (!x'. x' IN topspace top ==> dist(z,f x) <= dist(z,f x'))
        ==> transp(mfd_emb_jac atlas f x) ** (z - f x) = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MIN")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `D = frechet_derivative ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N)))
                           (at (SND c (x:A)))` THEN
  SUBGOAL_THEN
   `(((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) has_derivative D)
    (at (SND c (x:A)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(D:real^N->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_emb_jac (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) x =
    matrix(D:real^N->real^K)`
  SUBST1_TAC THENL [REWRITE_TAC[mfd_emb_jac] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\y:real^N. lift(norm((z:real^K) - ((f:A->real^K) o
                                       chart_inv (c:(A->bool)#(A->real^N))) y) pow 2)`;
    `(\w. &2 % lift(((z:real^K) - f(x:A)) dot w)) o
     (\h:real^N. vec 0 - (D:real^N->real^K) h)`;
    `SND(c:(A->bool)#(A->real^N)) (x:A)`;
    `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`] DIFFERENTIAL_ZERO_MAXMIN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\y:real^N. lift(norm((z:real^K) - ((f:A->real^K) o
                                           chart_inv (c:(A->bool)#(A->real^N))) y) pow 2)) =
        (\w. lift(norm w pow 2)) o (\y. z - (f o chart_inv c) y)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST; ETA_AX];
        ASM_SIMP_TAC[o_THM; HAS_DERIVATIVE_SQNORM_AT]];
      DISJ2_TAC THEN REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_THM] THEN
      X_GEN_TAC `p:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE; GSYM dist] THEN
      USE_THEN "MIN" MATCH_MP_TAC THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM
    `transp(matrix(D:real^N->real^K)) ** ((z:real^K) - f(x:A))`) THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  REWRITE_TAC[o_THM; DROP_CMUL; LIFT_DROP; DROP_VEC] THEN
  SUBGOAL_THEN `!h. (D:real^N->real^K) h = matrix D ** h` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[MATRIX_WORKS]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB_LZERO; DOT_RNEG] THEN
  ONCE_REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN
  REWRITE_TAC[REAL_ARITH `&2 * --x = &0 <=> x = &0`; DOT_EQ_0]);;

let GRGE_HAS_DERIVATIVE_FSTCART_COMPOSE = prove
 (`!(g:real^N->real^M) g' (p:real^(N,P)finite_sum).
        (g has_derivative g') (at (fstcart p))
        ==> ((\q. g(fstcart q)) has_derivative (\d. g'(fstcart d))) (at p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fstcart:real^(N,P)finite_sum->real^N`; `g:real^N->real^M`;
                 `fstcart:real^(N,P)finite_sum->real^N`; `g':real^N->real^M`;
                 `p:real^(N,P)finite_sum`] DIFF_CHAIN_AT) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_FSTCART; o_DEF]);;

let GRGE_TRANSP_MUL_INJ = prove
 (`!J:real^N^K. (!v. J ** v = vec 0 ==> v = vec 0)
                ==> !a. transp J ** (J ** a) = vec 0 ==> a = vec 0`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[GSYM DOT_EQ_0] THEN
  ONCE_REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_REWRITE_TAC[DOT_RZERO]);;

let GRGE_PSI_SMOOTH = prove
 (`!(g:real^N->real^K) V.
        open V /\ smooth_map_on V g
        ==> open {p:real^(N,K)finite_sum | fstcart p IN V} /\
            smooth_map_on {p:real^(N,K)finite_sum | fstcart p IN V}
              (\p. pastecart (transp(matrix(frechet_derivative g (at (fstcart p)))) **
                              (sndcart p - g(fstcart p)))
                             (sndcart p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on {p:real^(N,K)finite_sum | fstcart p IN V}
      (\p. (g:real^N->real^K)(fstcart p))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\p:real^(N,K)finite_sum. (g:real^N->real^K)(fstcart p)) = g o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SET_TAC[]; MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC GRGE_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGE_SMOOTH_TRANSP THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(vectorize:real^N^K->real^(K,N)finite_prod) o
      (\p:real^(N,K)finite_sum. matrix(frechet_derivative (g:real^N->real^K)
                                                         (at (fstcart p)))) =
      (vectorize o (\y. matrix(frechet_derivative g (at y)))) o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_SIMP_TAC[GRGE_SMOOTH_JACOBIAN] THEN CONJ_TAC THENL
     [SET_TAC[]; MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART]];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_SNDCART]]);;

let GRGE_PSI_DERIV = prove
 (`!(g:real^N->real^K) V y0.
        open V /\ smooth_map_on V g /\ y0 IN V
        ==> ((\p:real^(N,K)finite_sum.
                pastecart (transp(matrix(frechet_derivative g (at (fstcart p)))) **
                           (sndcart p - g(fstcart p)))
                          (sndcart p)) has_derivative
             (\d. pastecart (transp(matrix(frechet_derivative g (at y0))) **
                             (sndcart d - frechet_derivative g (at y0) (fstcart d)))
                            (sndcart d)))
            (at (pastecart y0 (g y0)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^K`; `V:real^N->bool`] GRGE_PSI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(pastecart (y0:real^N) ((g:real^N->real^K) y0)) IN
                {p:real^(N,K)finite_sum | fstcart p IN V}`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on {p:real^(N,K)finite_sum | fstcart p IN V}
      ((vectorize:real^K^N->real^(N,K)finite_prod) o
       (\p:real^(N,K)finite_sum.
          transp(matrix(frechet_derivative (g:real^N->real^K) (at (fstcart p))))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGE_SMOOTH_TRANSP THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(vectorize:real^N^K->real^(K,N)finite_prod) o
      (\p:real^(N,K)finite_sum. matrix(frechet_derivative (g:real^N->real^K)
                                                         (at (fstcart p)))) =
      (vectorize o (\y. matrix(frechet_derivative g (at y)))) o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_SIMP_TAC[GRGE_SMOOTH_JACOBIAN] THEN CONJ_TAC THENL
     [SET_TAC[]; MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((g:real^N->real^K) has_derivative frechet_derivative g (at y0)) (at y0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
  SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_SNDCART] THEN
  MP_TAC(ISPECL
   [`\(m:real^(N,K)finite_prod) (v:real^K). (matrify m:real^K^N) ** v`;
    `(vectorize:real^K^N->real^(N,K)finite_prod) o
     (\p:real^(N,K)finite_sum.
        transp(matrix(frechet_derivative (g:real^N->real^K) (at (fstcart p)))))`;
    `\p:real^(N,K)finite_sum. sndcart p - (g:real^N->real^K)(fstcart p)`;
    `frechet_derivative
      ((vectorize:real^K^N->real^(N,K)finite_prod) o
       (\p:real^(N,K)finite_sum.
          transp(matrix(frechet_derivative (g:real^N->real^K) (at (fstcart p))))))
      (at (pastecart (y0:real^N) ((g:real^N->real^K) y0)))`;
    `\d:real^(N,K)finite_sum.
       sndcart d - frechet_derivative (g:real^N->real^K) (at y0) (fstcart d)`;
    `pastecart (y0:real^N) ((g:real^N->real^K) y0)`] HAS_DERIVATIVE_BILINEAR_AT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GRGE_BILINEAR_MATRIFY_MUL] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{p:real^(N,K)finite_sum | fstcart p IN V}` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
      SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_SNDCART] THEN
      MATCH_MP_TAC GRGE_HAS_DERIVATIVE_FSTCART_COMPOSE THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; ETA_AX]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM; MATRIFY_VECTORIZE; FSTCART_PASTECART; SNDCART_PASTECART;
              VECTOR_SUB_REFL; MATRIX_VECTOR_MUL_RZERO; VECTOR_ADD_RID]);;

let GRGE_PSI_DET = prove
 (`!(g:real^N->real^K) V y0.
        open V /\ smooth_map_on V g /\ y0 IN V /\
        (!v. frechet_derivative g (at y0) v = vec 0 ==> v = vec 0)
        ==> ~(det(matrix(frechet_derivative
                (\p:real^(N,K)finite_sum.
                    pastecart (transp(matrix(frechet_derivative g (at (fstcart p)))) **
                               (sndcart p - g(fstcart p)))
                              (sndcart p))
                (at (pastecart y0 (g y0))))) = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^K`; `V:real^N->bool`; `y0:real^N`] GRGE_PSI_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  SUBGOAL_THEN `linear(frechet_derivative (g:real^N->real^K) (at y0))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE
       THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `J0 = matrix(frechet_derivative (g:real^N->real^K) (at y0))` THEN
  SUBGOAL_THEN `!h. frechet_derivative (g:real^N->real^K) (at y0) h = (J0:real^N^K) ** h`
  ASSUME_TAC THENL [EXPAND_TAC "J0" THEN ASM_SIMP_TAC[MATRIX_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `!v. (J0:real^N^K) ** v = vec 0 ==> v = vec 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `det(matrix(\d:real^(N,K)finite_sum.
                   pastecart (transp(J0:real^N^K) **
                              (sndcart d - frechet_derivative (g:real^N->real^K) (at y0)
                                                              (fstcart d)))
                             (sndcart d))) = &0` THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  REWRITE_TAC[PASTECART_EQ_VEC; NOT_EXISTS_THM] THEN
  X_GEN_TAC `d:real^(N,K)finite_sum` THEN
  ASM_CASES_TAC `sndcart(d:real^(N,K)finite_sum) = vec 0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_SUB_LZERO; MATRIX_VECTOR_MUL_RNEG; VECTOR_NEG_EQ_0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP GRGE_TRANSP_MUL_INJ
    (ASSUME `!v. (J0:real^N^K) ** v = vec 0 ==> v = vec 0`))) THEN
  DISCH_TAC THEN MP_TAC(ISPEC `d:real^(N,K)finite_sum` PASTECART_FST_SND) THEN
  ASM_REWRITE_TAC[PASTECART_VEC] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Local solution of the normal equation J(y)^T (z - g y) = 0 near           *)
(* (y0, g y0), with uniqueness, by the inverse function theorem for Psi.     *)
(* ------------------------------------------------------------------------- *)

let GRGE_LOCAL_IFT = prove
 (`!(g:real^N->real^K) V y0.
        open V /\ smooth_map_on V g /\ y0 IN V /\
        (!v. frechet_derivative g (at y0) v = vec 0 ==> v = vec 0)
        ==> ?r Y. &0 < r /\
                  smooth_map_on (ball(g y0,r)) (Y:real^K->real^N) /\
                  (!z. z IN ball(g y0,r)
                       ==> Y z IN V /\
                           transp(matrix(frechet_derivative g (at (Y z)))) **
                           (z - g(Y z)) = vec 0) /\
                  (!y z. y IN V /\ y IN ball(y0,r) /\ z IN ball(g y0,r) /\
                         transp(matrix(frechet_derivative g (at y))) ** (z - g y) = vec 0
                         ==> y = Y z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^K`; `V:real^N->bool`] GRGE_PSI_SMOOTH) THEN
  MP_TAC(ISPECL [`g:real^N->real^K`; `V:real^N->bool`; `y0:real^N`] GRGE_PSI_DET) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `Psi = \p:real^(N,K)finite_sum.
            pastecart (transp(matrix(frechet_derivative (g:real^N->real^K)
                                                        (at (fstcart p)))) **
                       (sndcart p - g(fstcart p)))
                      (sndcart p)` THEN
  DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(Psi:real^(N,K)finite_sum->real^(N,K)finite_sum)
      (pastecart y0 ((g:real^N->real^K) y0)) = pastecart (vec 0) (g y0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Psi" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_SUB_REFL;
                MATRIX_VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y z. (Psi:real^(N,K)finite_sum->real^(N,K)finite_sum) (pastecart y z) =
          pastecart (transp(matrix(frechet_derivative (g:real^N->real^K) (at y))) **
                     (z - g y)) z`
  ASSUME_TAC THENL
   [EXPAND_TAC "Psi" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Psi:real^(N,K)finite_sum->real^(N,K)finite_sum`;
                 `{p:real^(N,K)finite_sum | fstcart p IN V}`;
                 `pastecart (y0:real^N) ((g:real^N->real^K) y0)`]
                SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^(N,K)finite_sum->bool`
    (X_CHOOSE_THEN `u:real^(N,K)finite_sum->bool`
    (X_CHOOSE_THEN `G:real^(N,K)finite_sum->real^(N,K)finite_sum` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MP_TAC(ISPEC `t:real^(N,K)finite_sum->bool` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (y0:real^N) ((g:real^N->real^K) y0)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `u:real^(N,K)finite_sum->bool` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (vec 0) ((g:real^N->real^K)
      y0):real^(N,K)finite_sum`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!z. z IN ball((g:real^N->real^K) y0,min (r1 / &2) r2)
        ==> pastecart (vec 0) z IN (u:real^(N,K)finite_sum->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^K` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist; PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART_0] THEN
    ASM_REWRITE_TAC[GSYM dist];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y z. y IN ball(y0,min (r1 / &2) r2) /\
          z IN ball((g:real^N->real^K) y0,min (r1 / &2) r2)
          ==> pastecart y z IN (t:real^(N,K)finite_sum->bool)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^K`] THEN
    REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist; PASTECART_SUB] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm((y0:real^N) - y) + norm((g:real^N->real^K) y0 - z)` THEN
    REWRITE_TAC[NORM_PASTECART_LE] THEN
    UNDISCH_TAC `dist(y0:real^N,y) < r1 / &2` THEN
    UNDISCH_TAC `dist((g:real^N->real^K) y0,z) < r1 / &2` THEN
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (r1 / &2) r2` THEN
  EXISTS_TAC `\z:real^K. fstcart((G:real^(N,K)finite_sum->real^(N,K)finite_sum)
                                   (pastecart (vec 0) z))` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_HALF] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z:real^K. fstcart((G:real^(N,K)finite_sum->real^(N,K)finite_sum)
                            (pastecart (vec 0) z))) =
      fstcart o (G o (\z. pastecart (vec 0) z))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    REWRITE_TAC[OPEN_BALL; LINEAR_FSTCART] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `u:real^(N,K)finite_sum->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
      REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]];
    X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(G:real^(N,K)finite_sum->real^(N,K)finite_sum) (pastecart (vec 0) z) IN t`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `fstcart((G:real^(N,K)finite_sum->real^(N,K)finite_sum) (pastecart (vec 0) z)) IN V`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^(N,K)finite_sum->bool) SUBSET {p | fstcart p IN V}` THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(Psi:real^(N,K)finite_sum->real^(N,K)finite_sum)
        ((G:real^(N,K)finite_sum->real^(N,K)finite_sum) (pastecart (vec 0) z)) =
      pastecart (vec 0) z`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM PASTECART_FST_SND] THEN
    ASM_REWRITE_TAC[PASTECART_INJ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^K`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `pastecart (y:real^N) (z:real^K) IN t` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(Psi:real^(N,K)finite_sum->real^(N,K)finite_sum) (pastecart y z) =
      pastecart (vec 0) z`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(G:real^(N,K)finite_sum->real^(N,K)finite_sum) (pastecart (vec 0) z) =
      pastecart y z`
    (fun th -> REWRITE_TAC[th; FSTCART_PASTECART]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The local tube: near f x0 the nearest point exists, is unique, is given   *)
(* by the chart solution Y of the normal equation, and is characterized by   *)
(* the normal condition: the tangent projection at x kills z - f x.         *)
(* ------------------------------------------------------------------------- *)

let GRGE_EMBEDDING_CHART_NBHD = prove
 (`!top atlas (f:A->real^K) c x0 e.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_embedding (top,atlas) f /\ c IN atlas /\ x0 IN FST c /\ &0 < e
        ==> ?r. &0 < r /\
                !x. x IN topspace top /\ f x IN ball(f x0,r)
                    ==> x IN FST c /\ SND c x IN ball(SND c x0,e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_embedding] THEN STRIP_TAC THEN
  ABBREV_TAC
   `O = {p:A | p IN FST(c:(A->bool)#(A->real^N)) /\ SND c p IN ball(SND c (x0:A),e)}` THEN
  SUBGOAL_THEN `open_in top (O:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `SND (c:(A->bool)#(A->real^N)) (x0:A)`; `e:real`]
                  MFDC_CHART_BALL_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_OPEN_MAP) THEN
  REWRITE_TAC[open_map] THEN DISCH_THEN(MP_TAC o SPEC `O:A->bool`) THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM OPEN_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^K->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:A->real^K) x0 IN G` ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:A->real^K) x0 IN IMAGE f O` MP_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE]; ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `G:real^K->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:A->real^K) x0`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->real^K) x IN IMAGE f O` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x':A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x:A = x'` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_INJECTIVE_MAP) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `x':A`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  UNDISCH_TAC `(x':A) IN O` THEN EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM]);;

let GRGE_NORMAL_IN_CHART = prove
 (`!top atlas (f:A->real^K) c (Y:real^K->real^N) x0 r x z.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_immersion_into atlas f /\ c IN atlas /\
        (!y z. y IN IMAGE (SND c) (FST c) /\ y IN ball(SND c x0,r) /\
               z IN ball(f x0,r) /\
               transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
               (z - f(chart_inv c y)) = vec 0
               ==> y = Y z) /\
        x IN topspace top /\ x IN FST c /\ SND c x IN ball(SND c x0,r) /\
        z IN ball(f x0,r) /\
        mfd_tproj atlas f x ** (z - f x) = vec 0
        ==> SND c x = Y z /\ f x = f(chart_inv c (Y z))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "UNIQ") STRIP_ASSUME_TAC))))
        THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [USE_THEN "UNIQ" MATCH_MP_TAC THEN REMOVE_THEN "UNIQ" (K ALL_TAC) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    MATCH_MP_TAC GRGE_EMB_JAC_TRANSP_KERNEL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `x:A`; `(z:real^K) - f(x:A)`] GRGE_TPROJ_KERNEL) THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "UNIQ" (K ALL_TAC) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[]]);;

let GRGE_TUBE_LOCAL = prove
 (`!top atlas (f:A->real^K) x0.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top /\ mfd_embedding (top,atlas) f /\ x0 IN topspace top
        ==> ?r c (Y:real^K->real^N).
              &0 < r /\ c IN atlas /\ smooth_map_on (ball(f x0,r)) Y /\
              (!z. z IN ball(f x0,r)
                   ==> Y z IN IMAGE (SND c) (FST c) /\
                       closest_point (IMAGE f (topspace top)) z = f(chart_inv c (Y z)) /\
                       (!q. q IN IMAGE f (topspace top) /\
                            ~(q = closest_point (IMAGE f (topspace top)) z)
                            ==> dist(z,closest_point (IMAGE f (topspace top)) z) <
                                dist(z,q))) /\
              (!z x. z IN ball(f x0,r) /\ x IN topspace top /\ f x IN ball(f x0,r)
                     ==> (closest_point (IMAGE f (topspace top)) z = f x <=>
                          mfd_tproj atlas f x ** (z - f x) = vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_immersion_into (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_embedding]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (f:A->real^K) (topspace top))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM compact_space] THEN
    MATCH_MP_TAC GRGE_MFD_SMOOTH_CONTINUOUS THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_MESON_TAC[GRGE_IMMERSION_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closed(IMAGE (f:A->real^K) (topspace top)) /\ ~(IMAGE f (topspace top) = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `x0:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x0:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))`;
                 `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `SND(c:(A->bool)#(A->real^N)) (x0:A)`] GRGE_LOCAL_IFT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c (x0:A)) = x0`
  (fun th -> REWRITE_TAC[o_THM; th]) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `Y:real^K->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "EX") (LABEL_TAC "UNIQ")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`; `x0:A`; `r1:real`]
                GRGE_EMBEDDING_CHART_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NB"))) THEN
  SUBGOAL_THEN
   `!x z. x IN topspace top /\ (f:A->real^K) x IN ball(f x0,r3) /\ z IN ball(f x0,r1) /\
          mfd_tproj (atlas:((A->bool)#(A->real^N))->bool) f x ** (z - f x) = vec 0
          ==> f x = f(chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^K->real^N) z))`
  (LABEL_TAC "NORM") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "NB" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `c:(A->bool)#(A->real^N)`; `Y:real^K->real^N`;
                   `x0:A`; `r1:real`; `x:A`; `z:real^K`] GRGE_NORMAL_IN_CHART) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = min r1 r3 / &2` THEN
  SUBGOAL_THEN `&0 < r /\ &2 * r <= r3 /\ r <= r1 /\ r <= r3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z x. z IN ball((f:A->real^K) x0,r) /\ x IN topspace top /\
          (!x'. x' IN topspace top ==> dist(z,f x) <= dist(z,f x'))
          ==> f x = f(chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^K->real^N) z))`
  (LABEL_TAC "NEAR") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MIN")))
        THEN
    SUBGOAL_THEN `dist(z:real^K,f(x:A)) <= dist(z,f x0)` ASSUME_TAC THENL
     [USE_THEN "MIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "NORM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `dist(z:real^K,f(x:A)) <= dist(z,f x0)` THEN
      UNDISCH_TAC `(z:real^K) IN ball(f(x0:A),r)` THEN
      UNDISCH_TAC `&2 * r <= r3` THEN REWRITE_TAC[IN_BALL] THEN CONV_TAC NORM_ARITH;
      UNDISCH_TAC `(z:real^K) IN ball(f(x0:A),r)` THEN
      UNDISCH_TAC `r <= r1` THEN REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `f:A->real^K`; `x:A`; `(z:real^K) - f(x:A)`] GRGE_TPROJ_KERNEL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC GRGE_NEAREST_FIRST_ORDER THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ball((f:A->real^K) x0,r)
        ==> closest_point (IMAGE f (topspace top)) z =
            f(chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^K->real^N) z))`
  (LABEL_TAC "PI") THENL
   [X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`IMAGE (f:A->real^K) (topspace top)`; `z:real^K`]
                  CLOSEST_POINT_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "LE")) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `xs:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "NEAR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x':A` THEN DISCH_TAC THEN
    USE_THEN "LE" (MP_TAC o SPEC `(f:A->real^K) x'`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `c:(A->bool)#(A->real^N)`; `Y:real^K->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ball((f:A->real^K) x0,r) SUBSET ball(f x0,r1)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball((f:A->real^K) x0,r1)` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^K) IN ball(f(x0:A),r1)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "PI" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^K) IN
        ball(f(x0:A),r)`)]) THEN
    CONJ_TAC THENL
     [USE_THEN "EX" (MP_TAC o C MATCH_MP (ASSUME `(z:real^K) IN ball(f(x0:A),r1)`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `q:real^K` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `xq:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(q:real^K = f(chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^K->real^N)
        z)))` THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "NEAR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x':A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `dist(z:real^K,f(chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^K->real^N)
        z)))` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "PI" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(z:real^K) IN
        ball(f(x0:A),r)`))]) THEN
    MP_TAC(ISPECL [`IMAGE (f:A->real^K) (topspace top)`; `z:real^K`]
                  CLOSEST_POINT_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    MAP_EVERY X_GEN_TAC [`z:real^K`; `x:A`] THEN STRIP_TAC THEN
    USE_THEN "PI" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^K) IN
        ball(f(x0:A),r)`)]) THEN
    EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `f:A->real^K`; `x:A`; `(z:real^K) - f(x:A)`] GRGE_TPROJ_KERNEL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC GRGE_NEAREST_FIRST_ORDER THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x':A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      USE_THEN "PI" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(z:real^K) IN
          ball(f(x0:A),r)`))]) THEN
      MP_TAC(ISPECL [`IMAGE (f:A->real^K) (topspace top)`; `z:real^K`]
                    CLOSEST_POINT_EXISTS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE];
      DISCH_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "NORM" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC(SET_RULE `!s t x:real^K. s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `ball((f:A->real^K) x0,r)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* A uniform radius: every point of f(M) has a ball of radius 2 d inside one *)
(* of the local tubes (finite subcover, minimum of finitely many radii).     *)
(* ------------------------------------------------------------------------- *)

let GRGE_UNIFORM_BALLS = prove
 (`!top (f:A->real^K) R.
        compact_space top /\ continuous_map (top,euclidean) f /\
        (!x. x IN topspace top ==> &0 < R x)
        ==> ?d. &0 < d /\
                !x. x IN topspace top
                    ==> ?x0. x0 IN topspace top /\ ball(f x,d) SUBSET ball(f x0,R x0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RPOS")))
      THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (f:A->real^K) (topspace top))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM compact_space];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_HEINE_BOREL) THEN
  DISCH_THEN(MP_TAC o SPEC
    `IMAGE (\x0:A. ball((f:A->real^K) x0,R x0 / &2)) (topspace top)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_HALF] THEN USE_THEN "RPOS" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:(real^K->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\x0:A. ball((f:A->real^K) x0,R x0 / &2)`; `topspace top:A->bool`;
                 `ff:(real^K->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(t:A->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (f:A->real^K) (topspace top) SUBSET UNIONS ff` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; SUBSET_EMPTY; IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\x0:A. (R:A->real) x0 / &2) t` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "INFLE")) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `xm:A` (CONJUNCTS_THEN2 (LABEL_TAC "XM") ASSUME_TAC)) THEN
  EXISTS_TAC `inf (IMAGE (\x0:A. (R:A->real) x0 / &2) t)` THEN CONJ_TAC THENL
   [USE_THEN "XM" SUBST1_TAC THEN REWRITE_TAC[REAL_HALF] THEN
    USE_THEN "RPOS" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x0:A. x0 IN t /\ (f:A->real^K) x IN ball(f x0,R x0 / &2)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:A->real^K) (topspace top) SUBSET UNIONS ff` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `x0:A` THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `w:real^K` THEN DISCH_TAC THEN
  USE_THEN "INFLE" (MP_TAC o C MATCH_MP (ASSUME `(x0:A) IN t`)) THEN
  UNDISCH_TAC `(f:A->real^K) x IN ball(f x0,R x0 / &2)` THEN REWRITE_TAC[IN_BALL] THEN
  UNDISCH_TAC `dist((f:A->real^K) x,w) < inf (IMAGE (\x0:A. (R:A->real) x0 / &2) t)` THEN
  CONV_TAC NORM_ARITH);;

let GRGE_TUBE_OPEN = prove
 (`!(S:real^K->bool) e. open {z | ?p. p IN S /\ dist(z,p) < e}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL; IN_ELIM_THM; SUBSET; IN_BALL] THEN
  X_GEN_TAC `z:real^K` THEN DISCH_THEN(X_CHOOSE_THEN `p:real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e - dist(z:real^K,p)` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  X_GEN_TAC `w:real^K` THEN DISCH_TAC THEN EXISTS_TAC `p:real^K` THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `dist(z:real^K,w) < e - dist(z,p)` THEN
  CONV_TAC NORM_ARITH);;

let GRGE_TUBE_UNIFORM = prove
 (`!top atlas (f:A->real^K).
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top /\ mfd_embedding (top,atlas) f
        ==> ?d. &0 < d /\
                !x. x IN topspace top
                    ==> ?B c (Y:real^K->real^N).
                          open B /\ ball(f x,&2 * d) SUBSET B /\ c IN atlas /\
                          smooth_map_on B Y /\
                          (!z. z IN B
                               ==> Y z IN IMAGE (SND c) (FST c) /\
                                   closest_point (IMAGE f (topspace top)) z =
                                   f(chart_inv c (Y z)) /\
                                   (!q. q IN IMAGE f (topspace top) /\
                                        ~(q = closest_point (IMAGE f (topspace top)) z)
                                        ==> dist(z,closest_point (IMAGE f (topspace top))
                                            z) <
                                            dist(z,q))) /\
                          (!z x'. z IN B /\ x' IN topspace top /\ f x' IN B
                                  ==> (closest_point (IMAGE f (topspace top)) z = f x' <=>
                                       mfd_tproj atlas f x' ** (z - f x') = vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`] GRGE_TUBE_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:A->real` (X_CHOOSE_THEN `C:A->(A->bool)#(A->real^N)`
    (X_CHOOSE_THEN `YY:A->real^K->real^N` (LABEL_TAC "LOC")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `f:A->real^K`; `R:A->real`] GRGE_UNIFORM_BALLS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGE_MFD_SMOOTH_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GRGE_IMMERSION_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
      ASM_MESON_TAC[mfd_embedding];
      GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "LOC" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UB"))) THEN
  EXISTS_TAC `d0 / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  USE_THEN "UB" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN
  USE_THEN "LOC" (MP_TAC o C MATCH_MP (ASSUME `(x0:A) IN topspace top`)) THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ball((f:A->real^K) x0,R x0)`; `(C:A->(A->bool)#(A->real^N)) x0`;
                        `(YY:A->real^K->real^N) x0`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; REAL_ARITH `&2 * d0 / &2 = d0`]);;

(* ------------------------------------------------------------------------- *)
(* The derivative of the nearest-point map on f(M) is the tangent           *)
(* projection; a Lipschitz bound for derivatives of smooth maps on compact  *)
(* sets; norms of complementary projections.                                *)
(* ------------------------------------------------------------------------- *)

let GRGE_TUBE_DERIV = prove
 (`!top atlas (f:A->real^K) d x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_immersion_into atlas f /\ x IN topspace top /\ &0 < d /\
        closest_point (IMAGE f (topspace top)) differentiable (at (f x)) /\
        (!z. dist(z,f x) < d
             ==> (closest_point (IMAGE f (topspace top)) z = f x <=>
                  mfd_tproj atlas f x ** (z - f x) = vec 0))
        ==> (closest_point (IMAGE f (topspace top)) has_derivative
             (\v. mfd_tproj atlas f x ** v)) (at (f x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FIB")))))) THEN
  ABBREV_TAC
   `L = frechet_derivative (closest_point (IMAGE (f:A->real^K) (topspace top)))
                           (at (f(x:A)))` THEN
  SUBGOAL_THEN
   `(closest_point (IMAGE (f:A->real^K) (topspace top)) has_derivative L) (at (f(x:A)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(L:real^K->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `D = frechet_derivative ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N)))
                           (at (SND c (x:A)))` THEN
  SUBGOAL_THEN
   `(((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) has_derivative D)
    (at (SND c (x:A)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `x:A`] MFD_TPROJ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "RANGE")))) THEN
  SUBGOAL_THEN `!w. (L:real^K->real^K) ((D:real^N->real^K) w) = D w` (LABEL_TAC "TAN") THENL
   [SUBGOAL_THEN `(L:real^K->real^K) o (D:real^N->real^K) = D` MP_TAC THENL
     [ALL_TAC; REWRITE_TAC[FUN_EQ_THM; o_THM]] THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `closest_point (IMAGE (f:A->real^K) (topspace top)) o
                ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N)))` THEN
    EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) (x:A)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[o_THM];
      MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      EXISTS_TAC `(f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))` THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CLOSEST_POINT_SELF THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. mfd_tproj (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) x ** v = vec 0
        ==> (L:real^K->real^K) v = vec 0`
  (LABEL_TAC "NOR") THENL
   [X_GEN_TAC `v:real^K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`closest_point (IMAGE (f:A->real^K) (topspace top)) o
       (\t:real^1. f(x:A) + drop t % (v:real^K))`;
      `(L:real^K->real^K) o (\t:real^1. drop t % (v:real^K))`;
      `\t:real^1. vec 0:real^K`; `vec 0:real^1`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`\t:real^1. f(x:A):real^K`; `\t:real^1. vec 0:real^K`;
                         `\t:real^1. drop t % (v:real^K)`;
                         `\t:real^1. drop t % (v:real^K)`;
                         `at(vec 0:real^1)`] HAS_DERIVATIVE_ADD) THEN
          REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN
          DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
          REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; VECTOR_ADD_RDISTRIB;
                      VECTOR_MUL_ASSOC];
          ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID]];
        MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
        EXISTS_TAC `(\t:real^1. f(x:A)):real^1->real^K` THEN
        EXISTS_TAC `ball(vec 0:real^1,d / (norm(v:real^K) + &1))` THEN
        REWRITE_TAC[OPEN_BALL; HAS_DERIVATIVE_CONST; CENTRE_IN_BALL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
          MP_TAC(ISPEC `v:real^K` NORM_POS_LE) THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_BALL; DIST_0; o_THM] THEN DISCH_TAC THEN
        CONV_TAC SYM_CONV THEN
        USE_THEN "FIB" (MP_TAC o SPEC `f(x:A) + drop t % (v:real^K)`) THEN
        REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`; MATRIX_VECTOR_MUL_RMUL] THEN
        ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[NORM_ARITH `dist(a + b:real^N,a) = norm b`; NORM_MUL; GSYM NORM_1] THEN
        SUBGOAL_THEN `&0 < norm(v:real^K) + &1` ASSUME_TAC THENL
         [MP_TAC(ISPEC `v:real^K` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `norm(t:real^1) * (norm(v:real^K) + &1)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
          ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]]];
      DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
      REWRITE_TAC[o_THM; LIFT_DROP; VECTOR_MUL_LID]];
    ALL_TAC] THEN
  UNDISCH_TAC
   `(closest_point (IMAGE (f:A->real^K) (topspace top)) has_derivative L) (at (f(x:A)))`
       THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^K` THEN
  SUBGOAL_THEN
   `(v:real^K) = mfd_tproj (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) x ** v +
                 (v - mfd_tproj atlas f x ** v)`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_ADD] THEN
  SUBGOAL_THEN
   `(L:real^K->real^K) (v - mfd_tproj (atlas:((A->bool)#(A->real^N))->bool)
                                      (f:A->real^K) x ** v) = vec 0`
  SUBST1_TAC THENL
   [USE_THEN "NOR" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_ASSOC;
                    VECTOR_SUB_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_RID] THEN
  USE_THEN "RANGE" (MP_TAC o fst o EQ_IMP_RULE o SPEC
    `mfd_tproj (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) x ** v`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` SUBST1_TAC) THEN
  USE_THEN "TAN" (fun th -> REWRITE_TAC[th]));;

let GRGE_ONORM_LE_VECTORIZE_LINEAR = prove
 (`!lf:real^M->real^N. linear lf ==> onorm lf <= norm(vectorize(matrix lf))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `matrix(lf:real^M->real^N)` ONORM_LE_NORM_VECTORIZE) THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN REWRITE_TAC[ETA_AX]);;

let GRGE_SMOOTH_DERIV_LIPSCHITZ = prove
 (`!s k (h:real^M->real^N).
        open s /\ smooth_map_on s h /\ compact k /\ k SUBSET s
        ==> ?B. &0 <= B /\
                !x y. segment[x,y] SUBSET k
                      ==> onorm(\v. frechet_derivative h (at x) v -
                                    frechet_derivative h (at y) v) <= B * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `Q = (vectorize:real^M^N->real^(N,M)finite_prod) o
        (\z. matrix(frechet_derivative (h:real^M->real^N) (at z)))` THEN
  SUBGOAL_THEN `smooth_map_on s (Q:real^M->real^(N,M)finite_prod)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC GRGE_SMOOTH_JACOBIAN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on s
     ((vectorize:real^M^(N,M)finite_prod->real^((N,M)finite_prod,M)finite_prod) o
      (\z. matrix(frechet_derivative (Q:real^M->real^(N,M)finite_prod) (at z))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGE_SMOOTH_JACOBIAN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `bounded(IMAGE
     ((vectorize:real^M^(N,M)finite_prod->real^((N,M)finite_prod,M)finite_prod) o
      (\z. matrix(frechet_derivative (Q:real^M->real^(N,M)finite_prod) (at z)))) k)`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BND"))) THEN
  EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^M) IN k /\ (y:real^M) IN k` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^M`; `y:real^M`] ENDS_IN_SEGMENT) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^M. z IN segment[x,y]
               ==> z IN k /\ z IN s /\
                   (Q:real^M->real^(N,M)finite_prod) differentiable (at z)`
  (LABEL_TAC "ZP") THENL
   [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^M) IN k /\ z IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((Q:real^M->real^(N,M)finite_prod) x - Q y) <= B * norm(x - y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Q:real^M->real^(N,M)finite_prod`;
                   `\z. frechet_derivative (Q:real^M->real^(N,M)finite_prod) (at z)`;
                   `segment[x:real^M,y]`; `B:real`] DIFFERENTIABLE_BOUND) THEN
    REWRITE_TAC[CONVEX_SEGMENT] THEN ANTS_TAC THENL
     [ALL_TAC;
      DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN
      REWRITE_TAC[ENDS_IN_SEGMENT]] THEN
    CONJ_TAC THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    USE_THEN "ZP" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(z:real^M) IN segment[x,y]`)) THEN
    REWRITE_TAC[] THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((vectorize:real^M^(N,M)finite_prod->
                       real^((N,M)finite_prod,M)finite_prod)
                       (matrix(frechet_derivative (Q:real^M->real^(N,M)finite_prod)
                                                  (at z))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC GRGE_ONORM_LE_VECTORIZE_LINEAR THEN
        MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
        USE_THEN "BND" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (h:real^M->real^N) (at x)) /\
    linear(frechet_derivative h (at y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((Q:real^M->real^(N,M)finite_prod) x - Q y)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `matrix(frechet_derivative (h:real^M->real^N) (at x)) -
                matrix(frechet_derivative h (at y))` ONORM_LE_NORM_VECTORIZE) THEN
  EXPAND_TAC "Q" THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_WORKS; o_THM; VECTORIZE_SUB]);;

let GRGE_SMOOTH_TAYLOR1 = prove
 (`!s k (h:real^M->real^N).
        open s /\ smooth_map_on s h /\ compact k /\ k SUBSET s
        ==> ?B. &0 <= B /\
                !x y. segment[x,y] SUBSET k
                      ==> norm(h y - h x - frechet_derivative h (at x) (y - x)) <=
                          B * norm(y - x) pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GRGE_SMOOTH_DERIV_LIPSCHITZ) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIP"))) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `(x:real^M) IN k /\ (y:real^M) IN k` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^M`; `y:real^M`] ENDS_IN_SEGMENT) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (h:real^M->real^N) (at x))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z:real^M. (h:real^M->real^N) z - frechet_derivative h (at x) z`;
    `\z:real^M. (\v. frechet_derivative (h:real^M->real^N) (at z) v -
                     frechet_derivative h (at x) v)`;
    `segment[x:real^M,y]`; `B * norm(y - x:real^M)`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_SEGMENT] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; ETA_AX] THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * norm(z - x:real^M)` THEN
      CONJ_TAC THENL
       [USE_THEN "LIP" MATCH_MP_TAC THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `segment[x:real^M,y]` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
        ASM_REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`x:real^M`; `y:real^M`; `z:real^M`] DIST_IN_CLOSED_SEGMENT) THEN
        ASM_REWRITE_TAC[dist] THEN NORM_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:real^M`; `x:real^M`]) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT] THEN
  SUBGOAL_THEN
   `(h:real^M->real^N) y - h x - frechet_derivative h (at x) (y - x) =
    (h y - frechet_derivative h (at x) y) - (h x - frechet_derivative h (at x) x)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[LINEAR_SUB] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC]);;

let GRGE_PROJ_COMPL_NORM_LE = prove
 (`!(P:real^K^K) w. transp P = P /\ P ** P = P ==> norm((mat 1 - P) ** w) <= norm w`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID; NORM_LE] THEN
  SUBGOAL_THEN `((P:real^K^K) ** w) dot (P ** w) = w dot (P ** w)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(P:real^K^K) ** w`; `w:real^K`] DOT_SYM) THEN
  MP_TAC(ISPEC `(P:real^K^K) ** w` DOT_POS_LE) THEN
  ASM_REWRITE_TAC[DOT_LSUB; DOT_RSUB] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The smooth retraction locally, and MFD_TUBULAR_NEIGHBOURHOOD.             *)
(* ------------------------------------------------------------------------- *)

let GRGE_EMB_INV_LEFT = prove
 (`!top atlas (f:A->real^K) x.
        mfd_embedding (top,atlas:((A->bool)#(A->real^N))->bool) f /\ x IN topspace top
        ==> mfd_emb_inv top f (f x) = x`,
  REWRITE_TAC[mfd_embedding] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_INJECTIVE_MAP) THEN
  DISCH_TAC THEN REWRITE_TAC[mfd_emb_inv] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let GRGE_OPEN_SET_CHART_INV = prove
 (`!(U:real^K->bool) y. y IN U ==> chart_inv (U,(\x:real^K. x)) y = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_inv; FST; SND] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]);;

let GRGE_TUBE_RETRACT_LOCAL = prove
 (`!top atlas (f:A->real^K) B c (Y:real^K->real^N) c' W z1.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_embedding (top,atlas) f /\
        open B /\ c IN atlas /\ smooth_map_on B Y /\
        (!z. z IN B
             ==> Y z IN IMAGE (SND c) (FST c) /\
                 closest_point (IMAGE f (topspace top)) z = f(chart_inv c (Y z))) /\
        c' IN atlas /\ open W /\ z1 IN B /\ z1 IN W /\
        mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z1) IN FST c'
        ==> ?N. open N /\ z1 IN N /\
                N SUBSET {z | z IN W /\
                              mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z)
                              IN FST c'} /\
                smooth_map_on N
                  (\z. SND c' (mfd_emb_inv top f
                                 (closest_point (IMAGE f (topspace top)) z)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "LOC") STRIP_ASSUME_TAC))))))
        THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN B
        ==> mfd_emb_inv top (f:A->real^K) (closest_point (IMAGE f (topspace top)) z) =
            chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^K->real^N) z)`
  (LABEL_TAC "FINV") THENL
   [X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o C MATCH_MP (ASSUME `(z:real^K) IN B`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC
   `O = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST(c':(A->bool)#(A->real^N)))`
       THEN
  SUBGOAL_THEN `open(O:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN B /\ (Y:real^K->real^N) z IN O
        ==> chart_inv (c:(A->bool)#(A->real^N)) (Y z) IN FST c INTER
            FST(c':(A->bool)#(A->real^N))`
  (LABEL_TAC "INO") THENL
   [X_GEN_TAC `z:real^K` THEN EXPAND_TAC "O" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(p:A) IN FST(c:(A->bool)#(A->real^N)) INTER FST(c':(A->bool)#(A->real^N))`
        THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  EXISTS_TAC `{z | z IN B INTER W /\ (Y:real^K->real^N) z IN O}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_SIMP_TAC[OPEN_INTER] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `B:real^K->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; INTER_SUBSET];
    REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "O" THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^K->real^N) z1)` THEN
    USE_THEN "LOC" (MP_TAC o C MATCH_MP (ASSUME `(z1:real^K) IN B`)) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[IN_INTER] THEN
    USE_THEN "FINV" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(z1:real^K) IN B`))])
        THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `z:real^K` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "FINV" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^K) IN B`)]) THEN
    USE_THEN "INO" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `(z:real^K) IN B`) (ASSUME `(Y:real^K->real^N) z IN O`))) THEN
    SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `chart_trans (c:(A->bool)#(A->real^N)) (c':(A->bool)#(A->real^N)) o
              (Y:real^K->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_SIMP_TAC[OPEN_INTER] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `B:real^K->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; INTER_SUBSET];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `z:real^K` THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM; chart_trans] THEN
    USE_THEN "FINV" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^K) IN B`)]);
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_SIMP_TAC[OPEN_INTER] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `B:real^K->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; INTER_SUBSET];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `B:real^K->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    EXPAND_TAC "O" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`]
                  CHART_TRANS_SMOOTH) THEN
    ASM_REWRITE_TAC[PAIR]]);;

let MFD_TUBULAR_NEIGHBOURHOOD = prove
 (`!top atlas (f:A->real^K).
     hausdorff_space top /\
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     compact_space top /\ mfd_embedding (top,atlas) f
     ==> ?d. &0 < d /\
             (!z p. p IN IMAGE f (topspace top) /\ dist(z,p) < d
                    ==> closest_point (IMAGE f (topspace top)) z IN IMAGE f (topspace top)
                        /\
                        !q. q IN IMAGE f (topspace top) /\
                            ~(q = closest_point (IMAGE f (topspace top)) z)
                            ==> dist(z,closest_point (IMAGE f (topspace top)) z) <
                                dist(z,q)) /\
             smooth_map_on {z | ?p. p IN IMAGE f (topspace top) /\ dist(z,p) < d}
                           (closest_point (IMAGE f (topspace top))) /\
             (!x. x IN topspace top
                  ==> (closest_point (IMAGE f (topspace top)) has_derivative
                       (\v. mfd_tproj atlas f x ** v)) (at (f x))) /\
             (!x z. x IN topspace top /\ dist(z,f x) < d
                    ==> (closest_point (IMAGE f (topspace top)) z = f x <=>
                         mfd_tproj atlas f x ** (z - f x) = vec 0)) /\
             (?C. &0 <= C /\
                  !x z. x IN topspace top /\ dist(z,f x) < d /\
                        closest_point (IMAGE f (topspace top)) z = f x
                        ==> onorm(\v. frechet_derivative
                                        (closest_point (IMAGE f (topspace top))) (at z) v -
                                      mfd_tproj atlas f x ** v) <= C * dist(z,f x)) /\
             mfd_smooth_map
               (open_set_atlas {z | ?p. p IN IMAGE f (topspace top) /\ dist(z,p) < d})
               atlas {z | ?p. p IN IMAGE f (topspace top) /\ dist(z,p) < d}
               (\z. mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z))`,
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
                 `f:A->real^K`] GRGE_TUBE_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UNI"))) THEN
  SUBGOAL_THEN
   `!z. (?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < &2 * d)
        ==> ?B c (Y:real^K->real^N).
              open B /\ z IN B /\ c IN atlas /\ smooth_map_on B Y /\
              (!z. z IN B
                   ==> Y z IN IMAGE (SND c) (FST c) /\
                       closest_point (IMAGE f (topspace top)) z = f(chart_inv c (Y z)) /\
                       (!q. q IN IMAGE f (topspace top) /\
                            ~(q = closest_point (IMAGE f (topspace top)) z)
                            ==> dist(z,closest_point (IMAGE f (topspace top)) z) <
                                dist(z,q)))`
  (LABEL_TAC "LOCZ") THENL
   [X_GEN_TAC `z:real^K` THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^K`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE])
                       ASSUME_TAC)) THEN
    USE_THEN "UNI" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real^K->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `Y:real^K->real^N` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`B:real^K->bool`; `c:(A->bool)#(A->real^N)`;
                          `Y:real^K->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball((f:A->real^K) x,&2 * d) SUBSET B` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on {z | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < &2 * d}
                  (closest_point (IMAGE f (topspace top)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[GRGE_TUBE_OPEN; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^K` THEN
    DISCH_THEN(fun th -> USE_THEN "LOCZ" (MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real^K->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `Y:real^K->real^N` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `B:real^K->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) o
                (Y:real^K->real^N)` THEN
    ASM_SIMP_TAC[o_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MFDM_CHART];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)` THEN
      REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z. x IN topspace top /\ dist(z,(f:A->real^K) x) < &2 * d
          ==> (closest_point (IMAGE f (topspace top)) z = f x <=>
               mfd_tproj (atlas:((A->bool)#(A->real^N))->bool) f x ** (z - f x) = vec 0)`
  (LABEL_TAC "FIB2") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "UNI" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real^K->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `Y:real^K->real^N` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball((f:A->real^K) x,&2 * d) SUBSET B` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[DIST_SYM; DIST_REFL; REAL_ARITH `&0 < d ==> &0 < &2 * d`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> (closest_point (IMAGE (f:A->real^K) (topspace top)) has_derivative
             (\v. mfd_tproj (atlas:((A->bool)#(A->real^N))->bool) f x ** v)) (at (f x))`
  (LABEL_TAC "DER") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC GRGE_TUBE_DERIV THEN
    EXISTS_TAC `&2 * d` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC
       `{z | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < &2 * d}` THEN
      ASM_REWRITE_TAC[GRGE_TUBE_OPEN; IN_ELIM_THM] THEN
      EXISTS_TAC `(f:A->real^K) x` THEN ASM_SIMP_TAC[FUN_IN_IMAGE; DIST_REFL] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN USE_THEN "FIB2" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:real^K`; `p:real^K`] THEN STRIP_TAC THEN
    USE_THEN "LOCZ" (MP_TAC o SPEC `z:real^K`) THEN ANTS_TAC THENL
     [EXISTS_TAC `p:real^K` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real^K->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `Y:real^K->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BP")))))))) THEN
    USE_THEN "BP" (MP_TAC o C MATCH_MP (ASSUME `(z:real^K) IN B`)) THEN STRIP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC
     `{z | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < &2 * d}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^K` THEN DISCH_THEN(X_CHOOSE_THEN `p:real^K` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `p:real^K` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(z:real^K,p) < d` THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
    USE_THEN "DER" ACCEPT_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "FIB2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(z:real^K,(f:A->real^K) x) < d` THEN UNDISCH_TAC `&0 < d` THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL
     [`{z | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < &2 * d}`;
      `{p + w | p IN IMAGE (f:A->real^K) (topspace top) /\ w IN cball(vec 0:real^K,d)}`;
      `closest_point (IMAGE (f:A->real^K) (topspace top))`]
     GRGE_SMOOTH_DERIV_LIPSCHITZ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GRGE_TUBE_OPEN] THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
        REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM; IN_CBALL_0] THEN
        MAP_EVERY X_GEN_TAC [`p:real^K`; `w:real^K`] THEN STRIP_TAC THEN
        EXISTS_TAC `p:real^K` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[NORM_ARITH `dist(p + w:real^N,p) = norm w`] THEN
        UNDISCH_TAC `norm(w:real^K) <= d` THEN UNDISCH_TAC `&0 < d` THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIP"))) THEN
    EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `z:real^K`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!v. mfd_tproj (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) x ** v =
          frechet_derivative (closest_point (IMAGE f (topspace top))) (at (f x)) v`
    (fun th -> REWRITE_TAC[th]) THENL
     [USE_THEN "DER" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[dist] THEN USE_THEN "LIP" MATCH_MP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball((f:A->real^K) x,d)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
      ASM_REWRITE_TAC[CONVEX_BALL; CENTRE_IN_BALL; IN_BALL] THEN
      REWRITE_TAC[DIST_REFL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; IN_CBALL_0] THEN
      X_GEN_TAC `u:real^K` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`(f:A->real^K) x`; `u - (f:A->real^K) x`] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
      CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
      UNDISCH_TAC `dist((f:A->real^K) x,u) < d` THEN REWRITE_TAC[dist] THEN
      NORM_ARITH_TAC];
    REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
    MAP_EVERY X_GEN_TAC [`c0:(real^K->bool)#(real^K->real^K)`;
                         `c':(A->bool)#(A->real^N)`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    REWRITE_TAC[FST; SND; IMAGE_ID; INTER_IDEMPOT] THEN
    ABBREV_TAC `Td = {z | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d}`
        THEN
    SUBGOAL_THEN `open(Td:real^K->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "Td" THEN REWRITE_TAC[GRGE_TUBE_OPEN]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!z1. z1 IN {z | z IN Td /\
                      mfd_emb_inv top (f:A->real^K) (closest_point (IMAGE f (topspace top))
                          z)
                      IN FST(c':(A->bool)#(A->real^N))}
           ==> ?N. open N /\ z1 IN N /\
                   N SUBSET {z | z IN Td /\
                                 mfd_emb_inv top f (closest_point (IMAGE f (topspace top))
                                     z)
                                 IN FST c'} /\
                   smooth_map_on N
                     (\z. SND c' (mfd_emb_inv top f
                                    (closest_point (IMAGE f (topspace top)) z)))`
    (LABEL_TAC "NB") THENL
     [X_GEN_TAC `z1:real^K` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      USE_THEN "LOCZ" (MP_TAC o SPEC `z1:real^K`) THEN ANTS_TAC THENL
       [UNDISCH_TAC `(z1:real^K) IN Td` THEN EXPAND_TAC "Td" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `p:real^K` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `p:real^K` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `dist(z1:real^K,p) < d` THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real^K->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)`
        (X_CHOOSE_THEN `Y:real^K->real^N` STRIP_ASSUME_TAC))) THEN
      MATCH_MP_TAC GRGE_TUBE_RETRACT_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `B:real^K->bool`;
                            `c:(A->bool)#(A->real^N)`; `Y:real^K->real^N`] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z. SND(c':(A->bool)#(A->real^N))
                       (mfd_emb_inv top (f:A->real^K)
                          (closest_point (IMAGE f (topspace top)) z))` THEN
    SUBGOAL_THEN
     `open {z | z IN Td /\
                mfd_emb_inv top (f:A->real^K) (closest_point (IMAGE f (topspace top)) z)
                IN FST(c':(A->bool)#(A->real^N))}`
    ASSUME_TAC THENL
     [GEN_REWRITE_TAC I [OPEN_SUBOPEN] THEN X_GEN_TAC `z1:real^K` THEN DISCH_TAC THEN
      USE_THEN "NB" (MP_TAC o C MATCH_MP (ASSUME
       `(z1:real^K) IN {z | z IN Td /\
                           mfd_emb_inv top (f:A->real^K)
                             (closest_point (IMAGE f (topspace top)) z)
                           IN FST(c':(A->bool)#(A->real^N))}`)) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[GRGE_OPEN_SET_CHART_INV];
      MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `z1:real^K` THEN DISCH_TAC THEN
      USE_THEN "NB" (MP_TAC o C MATCH_MP (ASSUME
       `(z1:real^K) IN {z | z IN Td /\
                           mfd_emb_inv top (f:A->real^K)
                             (closest_point (IMAGE f (topspace top)) z)
                           IN FST(c':(A->bool)#(A->real^N))}`)) THEN
      MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* MFD_EMBED_NORMAL_QUADRATIC: f(M) leaves its tangent spaces at most        *)
(* quadratically (Colding-Minicozzi (C.17)), from the Taylor bound for the   *)
(* nearest-point map near f(M) and the trivial bound far from the diagonal. *)
(* ------------------------------------------------------------------------- *)

let MFD_EMBED_NORMAL_QUADRATIC = prove
 (`!top atlas (f:A->real^K).
     hausdorff_space top /\
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     compact_space top /\ mfd_embedding (top,atlas) f
     ==> ?C. &0 <= C /\
             !x y. x IN topspace top /\ y IN topspace top
                   ==> norm((mat 1 - mfd_tproj atlas f x) ** (f y - f x)) <=
                       C * norm(f y - f x) pow 2`,
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
                 `f:A->real^K`] MFD_TUBULAR_NEIGHBOURHOOD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "DER") (K ALL_TAC)))))) THEN
  MP_TAC(ISPECL
   [`{z | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d}`;
    `{p + w | p IN IMAGE (f:A->real^K) (topspace top) /\ w IN cball(vec 0:real^K,d / &2)}`;
    `closest_point (IMAGE (f:A->real^K) (topspace top))`] GRGE_SMOOTH_TAYLOR1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GRGE_TUBE_OPEN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM; IN_CBALL_0] THEN
      MAP_EVERY X_GEN_TAC [`p:real^K`; `w:real^K`] THEN STRIP_TAC THEN
      EXISTS_TAC `p:real^K` THEN
      ASM_REWRITE_TAC[NORM_ARITH `dist(p + w:real^N,p) = norm w`] THEN
      UNDISCH_TAC `norm(w:real^K) <= d / &2` THEN UNDISCH_TAC `&0 < d` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TAY"))) THEN
  EXISTS_TAC `max B (inv(d / &2))` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 <= B` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `x:A`] MFD_TPROJ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN
   `closest_point (IMAGE (f:A->real^K) (topspace top)) (f y) = f y /\
    closest_point (IMAGE f (topspace top)) (f x) = f x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSEST_POINT_SELF THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (closest_point (IMAGE (f:A->real^K) (topspace top))) (at (f x)) =
    (\v. mfd_tproj (atlas:((A->bool)#(A->real^N))->bool) f x ** v)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    USE_THEN "DER" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= norm((f:A->real^K) y - f x) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  ASM_CASES_TAC `norm((f:A->real^K) y - f x) < d / &2` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * norm((f:A->real^K) y - f x) pow 2` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
    USE_THEN "TAY" (MP_TAC o SPECL [`(f:A->real^K) x`; `(f:A->real^K) y`]) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball((f:A->real^K) x,d / &2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
        ASM_REWRITE_TAC[CONVEX_BALL; CENTRE_IN_BALL; IN_BALL; DIST_REFL] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[dist];
        REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; IN_CBALL_0] THEN
        X_GEN_TAC `u:real^K` THEN DISCH_TAC THEN
        MAP_EVERY EXISTS_TAC [`(f:A->real^K) x`; `u - (f:A->real^K) x`] THEN
        ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
        CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
        UNDISCH_TAC `dist((f:A->real^K) x,u) < d / &2` THEN REWRITE_TAC[dist] THEN
        NORM_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((f:A->real^K) y - f x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GRGE_PROJ_COMPL_NORM_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(d / &2) * norm((f:A->real^K) y - f x) pow 2` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `&1 <= inv(d / &2) * norm((f:A->real^K) y - f x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(d / &2) * (d / &2)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]);;

