(* ========================================================================= *)
(* Unit pc_cmc_xfer (for pc_cm_compactness): transfer of energies, areas and *)
(* G-trace densities between maps of S^2 and their standard planar chart     *)
(* pictures, invariance under rotations, and invariance of the planar        *)
(* quantities under planar similarities.  Headlines CMCX_XFER and CMCX_SIM   *)
(* prove the statements CMC_XFER_STATEMENT and CMC_SIM_STATEMENT of          *)
(* pc_cmc_defs.                                                              *)
(*                                                                           *)
(* Route: the trace density of a jet scales under a frame J with J^T J =     *)
(* diag(m,m,1) (CMCX_TDENS_FRAME), which moves the shell integrand of        *)
(* cm_strace to the slab chart wan_nch and then to the plane, as CMR_S2_GLOC *)
(* does for the energy; rotations act by Gram conjugation; similarities      *)
(* through the affine transport of pc_cmr_scale.                             *)
(* ========================================================================= *)

needs "src/pc_cmc_defs.ml";;
needs "src/pc_cmc_dens.ml";;
needs "src/pc_cmr_scale.ml";;
needs "src/pc_cmw_reg.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* 3x3 algebra of e2 and its polarization: orthogonal invariance,            *)
(* homogeneity, and the frame lemma for the trace density.                   *)
(* ========================================================================= *)

let CMCX_E2_ORTH = prove
 (`!(O:real^3^3) (M:real^3^3) (N:real^3^3).
     orthogonal_matrix O
     ==> p4_e2(transp O ** M ** O) = p4_e2 M /\
         p4_e2_pol (transp O ** M ** O) (transp O ** N ** O) = p4_e2_pol M N`,
  REPEAT GEN_TAC THEN REWRITE_TAC[orthogonal_matrix] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!Z:real^3^3. (O:real^3^3) ** transp O ** Z = Z` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X:real^3^3. trace(transp (O:real^3^3) ** X ** O) = trace X`
   ASSUME_TAC THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[TRACE_MUL_SYM] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(X:real^3^3) (Y:real^3^3).
      (transp (O:real^3^3) ** X ** O) ** (transp O ** Y ** O) =
      transp O ** (X ** Y) ** O`
   ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p4_e2; p4_e2_pol]);;

let CMCX_E2_CMUL = prove
 (`!c (M:real^3^3) (N:real^3^3).
     p4_e2(c %% M) = c pow 2 * p4_e2 M /\
     p4_e2_pol (c %% M) (c %% N) = c pow 2 * p4_e2_pol M N`,
  REWRITE_TAC[p4_e2; p4_e2_pol; TRACE_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL;
              MATRIX_CMUL_ASSOC] THEN
  REAL_ARITH_TAC);;

(* Diagonal 3x3 matrices diag(s,s,t).                                         *)

let cmcx_dg = new_definition
 `cmcx_dg (s:real) (t:real) =
    (lambda i j. if i = j then (if i = 3 then t else s) else &0):real^3^3`;;

let CMCX_DG_FACTS = prove
 (`!s t s' t'.
     transp(cmcx_dg s t) = cmcx_dg s t /\
     cmcx_dg s t ** cmcx_dg s' t' = cmcx_dg (s * s') (t * t') /\
     cmcx_dg (&1) (&1) = mat 1 /\
     cmcx_dg s t ** basis 3 = t % basis 3`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; cmcx_dg; transp; matrix_mul;
              matrix_vector_mul; mat; basis; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3] THEN REAL_ARITH_TAC);;

let CMCX_DG_SCALE = prove
 (`!s (X:real^3^3).
     transp X = X /\ X ** basis 3 = vec 0
     ==> cmcx_dg s (&1) ** X ** cmcx_dg s (&1) = (s * s) %% X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(X:real^3^3)$1$3 = &0 /\ X$2$3 = &0 /\ X$3$3 = &0`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(X:real^3^3) ** basis 3 = vec 0` THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DIMINDEX_3; ARITH; CART_EQ; FORALL_3; column;
             LAMBDA_BETA; VEC_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(X:real^3^3)$3$1 = &0 /\ X$3$2 = &0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `transp(X:real^3^3) = X` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    SIMP_TAC[transp; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; cmcx_dg; matrix_mul;
              MATRIX_CMUL_COMPONENT] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CMCX_TRANSP_MUL_COLS = prove
 (`!(J:real^3^3) i j.
     1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
     ==> (transp J ** J)$i$j = (J ** basis i) dot (J ** basis j)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DIMINDEX_3; matrix_mul; transp; LAMBDA_BETA;
               dot; column] THEN
  REWRITE_TAC[DIMINDEX_3] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA; DIMINDEX_3]);;

(* The frame lemma: for a 3x3 frame J with J^T J = diag(m,m,1), m > 0, and  *)
(* jets x, y with cmw_jx y = cmw_jx x ** J whose third column vanishes,     *)
(* the e2 of the Gram matrix scales by m^2 and the trace density by m.      *)

let CMCX_TDENS_FRAME = prove
 (`!(G:real^K->real^K^K) (Q:real^K->real^K^K) (p:real^K)
    (x:real^(K,(K,K)finite_sum)finite_sum) (y:real^(K,(K,K)finite_sum)finite_sum)
    (J:real^3^3) m.
     transp(G p) = G p /\ transp(Q p) = Q p /\ &0 < m /\
     (J ** basis 1) dot (J ** basis 1) = m /\ (J ** basis 2) dot (J ** basis 2) = m /\
     (J ** basis 3) dot (J ** basis 3) = &1 /\ (J ** basis 1) dot (J ** basis 2) = &0 /\
     (J ** basis 1) dot (J ** basis 3) = &0 /\ (J ** basis 2) dot (J ** basis 3) = &0 /\
     cmw_jx y = cmw_jx x ** J /\ cmw_c3 y 3 = vec 0
     ==> p4_e2(transp(cmw_jx y) ** G p ** cmw_jx y) =
         m pow 2 * p4_e2(transp(cmw_jx x) ** G p ** cmw_jx x) /\
         cmw_tdens G Q p y = m * cmw_tdens G Q p x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `transp J ** (J:real^3^3) = cmcx_dg m (&1)` ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    SIMP_TAC[CMCX_TRANSP_MUL_COLS; ARITH] THEN
    REWRITE_TAC[cmcx_dg] THEN SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
    REPEAT CONJ_TAC THEN ASM_MESON_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt m /\ sqrt m * sqrt m = m` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `L = cmcx_dg (sqrt m) (&1)` THEN
  ABBREV_TAC `Li = cmcx_dg (inv(sqrt m)) (&1)` THEN
  SUBGOAL_THEN `(Li:real^3^3) ** L = mat 1 /\ transp L = (L:real^3^3) /\
                transp Li = (Li:real^3^3) /\ Li ** basis 3 = basis 3`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `cmcx_dg (sqrt m) (&1) = (L:real^3^3)`); SYM(ASSUME `cmcx_dg (inv(sqrt m)) (&1) = (Li:real^3^3)`)] THEN
    REWRITE_TAC[CMCX_DG_FACTS; VECTOR_MUL_LID; REAL_MUL_LID] THEN
    SUBGOAL_THEN `inv(sqrt m) * sqrt m = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[CMCX_DG_FACTS]];
    ALL_TAC] THEN
  ABBREV_TAC `Om = (J:real^3^3) ** (Li:real^3^3)` THEN
  SUBGOAL_THEN `orthogonal_matrix (Om:real^3^3) /\ (J:real^3^3) = Om ** (L:real^3^3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ORTHOGONAL_MATRIX] THEN EXPAND_TAC "Om" THEN
      SUBGOAL_THEN
       `transp((J:real^3^3) ** (Li:real^3^3)) ** (J ** Li) =
        transp Li ** (transp J ** J) ** Li`
       SUBST1_TAC THENL [REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SYM(ASSUME `cmcx_dg (inv(sqrt m)) (&1) = (Li:real^3^3)`)] THEN REWRITE_TAC[CMCX_DG_FACTS] THEN
      REWRITE_TAC[REAL_MUL_LID] THEN
      SUBGOAL_THEN `inv(sqrt m) * m * inv(sqrt m) = &1` SUBST1_TAC THENL
       [UNDISCH_TAC `sqrt m * sqrt m = m` THEN UNDISCH_TAC `&0 < sqrt m` THEN
        CONV_TAC REAL_FIELD;
        REWRITE_TAC[CMCX_DG_FACTS]];
      EXPAND_TAC "Om" THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
      ASM_REWRITE_TAC[MATRIX_MUL_RID]];
    ALL_TAC] THEN
  ABBREV_TAC `D = cmw_jx (x:real^(K,(K,K)finite_sum)finite_sum)` THEN
  SUBGOAL_THEN `(D:real^3^K) ** ((J:real^3^3) ** basis 3) = vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(D:real^3^K) ** (J:real^3^3) =
                  cmw_jx (y:real^(K,(K,K)finite_sum)finite_sum)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[CMW_JX_COL; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A:real^K^K.
      transp A = A
      ==> transp(cmw_jx (y:real^(K,(K,K)finite_sum)finite_sum)) ** A ** cmw_jx y =
          m %% (transp (Om:real^3^3) ** (transp (D:real^3^K) ** A ** D) ** Om) /\
          p4_e2(transp(cmw_jx y) ** A ** cmw_jx y) =
          m pow 2 * p4_e2(transp D ** A ** D)`
   ASSUME_TAC THENL
   [X_GEN_TAC `A:real^K^K` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `transp(cmw_jx (y:real^(K,(K,K)finite_sum)finite_sum)) ** (A:real^K^K) ** cmw_jx y =
      m %% (transp (Om:real^3^3) ** (transp (D:real^3^K) ** A ** D) ** Om)`
     ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `transp((D:real^3^K) ** ((Om:real^3^3) ** (L:real^3^3))) ** (A:real^K^K) **
        D ** (Om ** L) =
        L ** (transp Om ** (transp D ** A ** D) ** Om) ** L`
       SUBST1_TAC THENL
       [ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]; ALL_TAC] THEN
      UNDISCH_TAC `sqrt m * sqrt m = m` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[SYM(ASSUME `cmcx_dg (sqrt m) (&1) = (L:real^3^3)`)] THEN MATCH_MP_TAC CMCX_DG_SCALE THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC];
        REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
        SUBGOAL_THEN `(Om:real^3^3) ** basis 3 = (J:real^3^3) ** basis 3` SUBST1_TAC THENL
         [EXPAND_TAC "Om" THEN ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC];
          ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[CMCX_E2_CMUL; CMCX_E2_ORTH];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(G:real^K->real^K^K) p`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(Q:real^K->real^K^K) p`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[cmw_tdens] THEN
  ASM_SIMP_TAC[CMCX_E2_CMUL; CMCX_E2_ORTH] THEN
  ABBREV_TAC `e = p4_e2(transp (D:real^3^K) ** (G:real^K->real^K^K) p ** D)` THEN
  ABBREV_TAC `q = p4_e2_pol (transp (D:real^3^K) ** (G:real^K->real^K^K) p ** D)
                             (transp D ** (Q:real^K->real^K^K) p ** D)` THEN
  ASM_CASES_TAC `e = &0` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `~(m pow 2 * e = &0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SQRT_MUL] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `~(sqrt e = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[SQRT_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < m` THEN CONV_TAC REAL_FIELD);;


(* ========================================================================= *)
(* Jets, the slab chart, and the transfer of a frame-covariant density from  *)
(* the shell to the plane (the pattern of CMR_S2_GLOC).                      *)
(* ========================================================================= *)

let CMCX_JX_MUL = prove
 (`!(d:real^(K,(K,K)finite_sum)finite_sum) (a:real^3).
     cmw_jx d ** a = vsum(1..3) (\j. a$j % cmw_c3 d j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_VECTOR_COLUMN; DIMINDEX_3] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[transp; cmw_jx; LAMBDA_BETA; DIMINDEX_3]);;

let CMCX_JX_EQ = prove
 (`!(x:real^(K,(K,K)finite_sum)finite_sum) (y:real^(K,(K,K)finite_sum)finite_sum)
    (J:real^3^3).
     (!i. 1 <= i /\ i <= 3 ==> cmw_c3 y i = cmw_jx x ** (J ** basis i))
     ==> cmw_jx y = cmw_jx x ** J`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `((cmw_jx (x:real^(K,(K,K)finite_sum)finite_sum) ** (J:real^3^3))$k)$i =
                ((cmw_jx x ** J) ** basis i)$k`
   SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DIMINDEX_3; column; LAMBDA_BETA];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th (CONJ
    (ASSUME `1 <= i`) (ASSUME `i <= 3`)))]) THEN
  REWRITE_TAC[cmw_jx] THEN ASM_SIMP_TAC[LAMBDA_BETA; DIMINDEX_3]);;

let CMCX_C3_PASTE = prove
 (`!(a:real^K) b c.
     cmw_c3 (pastecart a (pastecart b c)) 1 = a /\
     cmw_c3 (pastecart a (pastecart b c)) 2 = b /\
     cmw_c3 (pastecart a (pastecart b c)) 3 = c`,
  REWRITE_TAC[cmw_c3; FSTCART_PASTECART; SNDCART_PASTECART; ARITH_EQ]);;

(* The shell is the cone over the chart image up to the null north ray.     *)

let CMCX_SHELL_CONE = prove
 (`cmr_cone (IMAGE stereo2_n_inv (:real^2)) SUBSET wan_shell /\
   negligible (wan_shell DIFF cmr_cone (IMAGE stereo2_n_inv (:real^2)))`,
  CONJ_TAC THENL
   [REWRITE_TAC[cmr_cone; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `cmr_cone {basis 3:real^3}` THEN
  REWRITE_TAC[CMR_CONE_POINT_NEGLIGIBLE] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; cmr_cone; IN_ELIM_THM; IN_SING; IN_IMAGE; IN_UNIV] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC STEX_STEREO2_N_CHART THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(norm z) % (z:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN
    UNDISCH_TAC `(z:real^3) IN wan_shell` THEN REWRITE_TAC[wan_shell; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `inv(norm z) % (z:real^3) = basis 3` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((z:real^3) IN wan_shell /\
                 (?x:real^2. inv(norm z) % z = stereo2_n_inv x))` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `stereo2_n(inv(norm z) % (z:real^3))` THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_DELETE]);;

(* The slab identity at one point: a frame-covariant density of the shell   *)
(* jet at wan_nch x, times wan_nchj x, is the density of the slab jet.      *)

let CMCX_SLAB_POINT = prove
 (`!(Phi:real^K->real^(K,(K,K)finite_sum)finite_sum->real) (u:real^3->real^K)
    (a1:real^K) (a2:real^K) x.
     (!p x y (J:real^3^3) m.
        &0 < m /\
        (J ** basis 1) dot (J ** basis 1) = m /\ (J ** basis 2) dot (J ** basis 2) = m /\
        (J ** basis 3) dot (J ** basis 3) = &1 /\ (J ** basis 1) dot (J ** basis 2) = &0 /\
        (J ** basis 1) dot (J ** basis 3) = &0 /\ (J ** basis 2) dot (J ** basis 3) = &0 /\
        cmw_jx y = cmw_jx x ** J /\ cmw_c3 y 3 = vec 0
        ==> Phi p y = m * Phi p x) /\
     &0 < x$3 /\
     wan_s2h u 1 x = a1 /\ wan_s2h u 2 x = a2 /\ wan_s2h u 3 x = vec 0
     ==> wan_nchj x * Phi (wan_rext u (wan_nch x)) (cmw_pk wan_shell (wan_rext u) (wan_nch x)) =
         Phi (u(stereo2_n_inv(vector[x$1; x$2]))) (cmc_j3 a1 a2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "frame") STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[WAN_REXT_NCH] THEN
  ABBREV_TAC `J = matrix(frechet_derivative wan_nch (at (x:real^3)))` THEN
  SUBGOAL_THEN `!i. (J:real^3^3) ** basis i = frechet_derivative wan_nch (at x) (basis i)`
   ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "J" THEN SIMP_TAC[MATRIX_WORKS; WAN_NCH_FACTS];
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real^3` WAN_NCH_ORTHO_HYP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real^3` WAN_NCHJ_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN USE_THEN "frame" MATCH_MP_TAC THEN
  EXISTS_TAC `J:real^3^3` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[cmc_j3; CMCX_C3_PASTE] THEN
  MATCH_MP_TAC CMCX_JX_EQ THEN
  REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[CMCX_C3_PASTE; CMCX_JX_MUL] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    let t = concl th in is_eq t && is_comb(lhs t) &&
      (try fst(dest_const(fst(strip_comb(lhs t)))) = "wan_s2h" with _ -> false)))) THEN
  REWRITE_TAC[wan_s2h] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CMW_C3_PK]);;

(* The transfer: the shell integral of a frame-covariant density of the jet  *)
(* of wan_rext u is 3/2 times the planar integral of the density of the      *)
(* planar jet of u o stereo2_n_inv (given planar integrability).            *)

let CMCX_CHART_DENS = prove
 (`!(Phi:real^K->real^(K,(K,K)finite_sum)finite_sum->real) (u:real^3->real^K).
     wan_s2_w12 u /\
     (!p x y (J:real^3^3) m.
        &0 < m /\
        (J ** basis 1) dot (J ** basis 1) = m /\ (J ** basis 2) dot (J ** basis 2) = m /\
        (J ** basis 3) dot (J ** basis 3) = &1 /\ (J ** basis 1) dot (J ** basis 2) = &0 /\
        (J ** basis 1) dot (J ** basis 3) = &0 /\ (J ** basis 2) dot (J ** basis 3) = &0 /\
        cmw_jx y = cmw_jx x ** J /\ cmw_c3 y 3 = vec 0
        ==> Phi p y = m * Phi p x) /\
     (\y. lift(Phi (u(stereo2_n_inv y))
                   (cmc_j3 (wan_wd (:real^2) 1 (\y. u(stereo2_n_inv y)) y)
                           (wan_wd (:real^2) 2 (\y. u(stereo2_n_inv y)) y))))
       absolutely_integrable_on (:real^2)
     ==> (\z. lift(Phi (wan_rext u z) (cmw_pk wan_shell (wan_rext u) z)))
           absolutely_integrable_on wan_shell /\
         integral wan_shell
           (\z. lift(Phi (wan_rext u z) (cmw_pk wan_shell (wan_rext u) z))) =
         &3 / &2 % integral (:real^2)
           (\y. lift(Phi (u(stereo2_n_inv y))
                         (cmc_j3 (wan_wd (:real^2) 1 (\y. u(stereo2_n_inv y)) y)
                                 (wan_wd (:real^2) 2 (\y. u(stereo2_n_inv y)) y))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "frame") ASSUME_TAC)) THEN
  MP_TAC(SPECL [`&1 / &2`; `&2`] WAN_SLAB_PSI) THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 < &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^1->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `v = \i (y:real^2). integral (:real^1)
          (\r. (psi:real^1->real) r %
               wan_s2h (u:real^3->real^K) i (vector[y$1; y$2; drop r]))` THEN
  SUBGOAL_THEN
   `wan_lloc (:real^2) (\y. (u:real^3->real^K)(stereo2_n_inv y)) /\
    !i. i = 1 \/ i = 2
        ==> wan_wpd (:real^2) i (\y. u(stereo2_n_inv y)) ((v:num->real^2->real^K) i) /\
            wan_lloc (:real^2) (v i) /\
            negligible {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                                   ~(wan_s2h u i x = v i (vector[x$1; x$2]))}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`u:real^3->real^K`; `psi:real^1->real`; `1`] WAN_S2_A_SLICE_I) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`u:real^3->real^K`; `psi:real^1->real`; `i:num`] WAN_S2_A_SLICE_I) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM wan_s2h] THEN
    EXPAND_TAC "v" THEN REWRITE_TAC[VECTOR_2] THEN
    REWRITE_TAC[wan_wpd] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `u:real^3->real^K` WAN_S2_A_VERT) THEN
  ASM_REWRITE_TAC[GSYM wan_s2h] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `v:num->real^2->real^K`] WAN_S2_A_ENERGY) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  (* planar: the chosen weak partials are the v i a.e. *)
  SUBGOAL_THEN
   `!i. i = 1 \/ i = 2
        ==> negligible {y | ~(wan_wd (:real^2) i (\y. (u:real^3->real^K)(stereo2_n_inv y)) y =
                              (v:num->real^2->real^K) i y)}`
   ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC CMC_WD_EQ_AE THEN
    REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `Fp = \y:real^2. lift((Phi:real^K->real^(K,(K,K)finite_sum)finite_sum->real)
                          ((u:real^3->real^K)(stereo2_n_inv y))
                          (cmc_j3 ((v:num->real^2->real^K) 1 y) (v 2 y)))` THEN
  SUBGOAL_THEN
   `(Fp:real^2->real^1) absolutely_integrable_on (:real^2) /\
    integral (:real^2) Fp =
    integral (:real^2)
      (\y. lift((Phi:real^K->real^(K,(K,K)finite_sum)finite_sum->real)
                 (u(stereo2_n_inv y))
                 (cmc_j3 (wan_wd (:real^2) 1 (\y. (u:real^3->real^K)(stereo2_n_inv y)) y)
                         (wan_wd (:real^2) 2 (\y. u(stereo2_n_inv y)) y))))`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[ABSOLUTELY_INTEGRABLE_SPIKE; INTEGRAL_SPIKE]
     `!N f g. negligible N /\ (!x. x IN (:real^2) DIFF N ==> f x = g x) /\
              g absolutely_integrable_on (:real^2)
              ==> (f:real^2->real^1) absolutely_integrable_on (:real^2) /\
                  integral (:real^2) f = integral (:real^2) g`) THEN
    EXISTS_TAC `{y | ~(wan_wd (:real^2) 1 (\y. (u:real^3->real^K)(stereo2_n_inv y)) y =
                       (v:num->real^2->real^K) 1 y)} UNION
                {y | ~(wan_wd (:real^2) 2 (\y. u(stereo2_n_inv y)) y = v 2 y)}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[];
      X_GEN_TAC `y:real^2` THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
      STRIP_TAC THEN EXPAND_TAC "Fp" THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* the slab *)
  MP_TAC(ISPEC `Fp:real^2->real^1` CMR_SLAB_PROJ) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `q = \z:real^3. if z IN cmr_cone (IMAGE stereo2_n_inv (:real^2))
                   then lift((Phi:real^K->real^(K,(K,K)finite_sum)finite_sum->real)
                               (wan_rext (u:real^3->real^K) z)
                               (cmw_pk wan_shell (wan_rext u) z))
                   else vec 0` THEN
  ABBREV_TAC `N3 = {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                    ~(wan_s2h (u:real^3->real^K) 1 x = (v:num->real^2->real^K) 1 (vector[x$1; x$2]))} UNION
                   {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                    ~(wan_s2h u 2 x = v 2 (vector[x$1; x$2]))} UNION
                   {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                    ~(wan_s2h u 3 x = vec 0)}` THEN
  SUBGOAL_THEN `negligible (N3:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N3" THEN REPEAT(MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} DIFF N3
               ==> wan_nchj x % (q:real^3->real^1)(wan_nch x) =
                   (Fp:real^2->real^1)(vector[x$1; x$2])`
   ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN EXPAND_TAC "N3" THEN
    REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `wan_s2h (u:real^3->real^K) 1 x = (v:num->real^2->real^K) 1 (vector[x$1; x$2]) /\
      wan_s2h u 2 x = v 2 (vector[x$1; x$2]) /\ wan_s2h u 3 x = vec 0`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "q" THEN
    MP_TAC(SPEC `(:real^2)` CMR_CONE_STEREO) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN EXPAND_TAC "Fp" THEN
    REWRITE_TAC[LIFT_EQ] THEN MATCH_MP_TAC CMCX_SLAB_POINT THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. wan_nchj x % (q:real^3->real^1)(wan_nch x)) absolutely_integrable_on
      {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
    integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} (\x. wan_nchj x % q(wan_nch x)) =
    integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} (\x. (Fp:real^2->real^1)(vector[x$1; x$2]))`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `\x:real^3. (Fp:real^2->real^1)(vector[x$1; x$2])` THEN
      EXISTS_TAC `N3:real^3->bool` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `N3:real^3->bool` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `q:real^3->real^1` WAN_NCH_COV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* back to the cone and the shell *)
  MP_TAC(SPEC `(:real^2)` CMR_CONE_STEREO) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `(\z. lift((Phi:real^K->real^(K,(K,K)finite_sum)finite_sum->real)
               (wan_rext (u:real^3->real^K) z) (cmw_pk wan_shell (wan_rext u) z)))
    absolutely_integrable_on cmr_cone (IMAGE stereo2_n_inv (:real^2)) /\
    integral (cmr_cone (IMAGE stereo2_n_inv (:real^2)))
      (\z. lift(Phi (wan_rext u z) (cmw_pk wan_shell (wan_rext u) z))) =
    integral {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}
      (q:real^3->real^1)`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN EXISTS_TAC `q:real^3->real^1` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "q" THEN SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `{z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMR_CONE_STEREO_OPEN; OPEN_UNIV];
      EXPAND_TAC "q" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_RESTRICT THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC CMCX_SHELL_CONE THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `negligible((wan_shell DIFF cmr_cone (IMAGE stereo2_n_inv (:real^2))) UNION
               (cmr_cone (IMAGE stereo2_n_inv (:real^2)) DIFF wan_shell))`
   ASSUME_TAC THENL
   [SUBGOAL_THEN `cmr_cone (IMAGE stereo2_n_inv (:real^2)) DIFF wan_shell = {}`
     SUBST1_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[UNION_EMPTY]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE_SET) THEN
    EXISTS_TAC `cmr_cone (IMAGE stereo2_n_inv (:real^2))` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `integral (cmr_cone (IMAGE stereo2_n_inv (:real^2)))
      (\z. lift((Phi:real^K->real^(K,(K,K)finite_sum)finite_sum->real)
                 (wan_rext (u:real^3->real^K) z) (cmw_pk wan_shell (wan_rext u) z)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* XFER part 1, maps of S^2 in the standard chart: the class cmc_pmap, the   *)
(* energy, the trace and the area.                                           *)
(* ========================================================================= *)

(* A copy of CMR_TARGET_GCOND (pc_cmr_crit), which this unit does not load. *)

let CMCX_TARGET_GCOND = prove
 (`!S (G:real^K->real^K^K) d. cm_target S G d ==> ?Lam. &0 <= Lam /\ CMR_GCOND G Lam`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_target; CMR_GCOND] THEN STRIP_TAC THEN
  EXISTS_TAC `Lam:real` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * norm(v:real^K) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC]);;

let CMCX_TARGET_G = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> compact S /\
         smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
         ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
         (!z. transp(G z) = G z) /\ (!z v. &0 <= v dot (G z ** v))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` MP_TAC o MATCH_MP CMCX_TARGET_GCOND) THEN
  REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `cm_target (S:real^K->bool) (G:real^K->real^K^K) d` THEN
  SIMP_TAC[cm_target]);;

(* The chart picture of a map of S^2 is in cmc_pmap.                         *)

let CMCX_PMAP_CHART = prove
 (`!S (u:real^3->real^K).
     cm_smap S u ==> cmc_pmap S (\y. u(stereo2_n_inv y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_smap; cmc_pmap] THEN STRIP_TAC THEN
  MP_TAC STEX_STEREO2_N_CHART THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. stereo2_n_inv y IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`stereo2_n_inv`; `u:real^3->real^K`; `(:real^2)`]
      CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM SET_TAC[]];
    ASM_SIMP_TAC[];
    MP_TAC(ISPEC `(:K)` WAN_S2_STEREO) THEN REWRITE_TAC[WAN_S2_STEREO_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^3->real^K` o CONJUNCT1) THEN
    ASM_SIMP_TAC[]]);;

(* The energy (CMR_SEN_CHART with the identity rotation).                    *)

let CMCX_SEN_CHART = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K).
     cm_target S G d /\ cm_smap S u
     ==> cm_sen G u = wan_gdir (:real^2) G (\y. u(stereo2_n_inv y)) / &2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP CMCX_TARGET_GCOND) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `mat 1:real^3^3`; `Lam:real`]
    CMR_SEN_CHART) THEN
  ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID] THEN ANTS_TAC THENL
   [UNDISCH_TAC `cm_smap S (u:real^3->real^K)` THEN SIMP_TAC[cm_smap]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[cm_capmap; MATRIX_VECTOR_MUL_LID]);;

(* The two densities (trace and area) are frame-covariant.                   *)

let CMCX_FRAME_TDENS = prove
 (`!(G:real^K->real^K^K) (Q:real^K->real^K^K).
     (!z. transp(G z) = G z) /\ (!z. transp(Q z) = Q z)
     ==> !p x y (J:real^3^3) m.
           &0 < m /\
           (J ** basis 1) dot (J ** basis 1) = m /\ (J ** basis 2) dot (J ** basis 2) = m /\
           (J ** basis 3) dot (J ** basis 3) = &1 /\ (J ** basis 1) dot (J ** basis 2) = &0 /\
           (J ** basis 1) dot (J ** basis 3) = &0 /\ (J ** basis 2) dot (J ** basis 3) = &0 /\
           cmw_jx y = cmw_jx x ** J /\ cmw_c3 y 3 = vec 0
           ==> cmw_tdens G Q p y = m * cmw_tdens G Q p x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Q:real^K->real^K^K`; `p:real^K`;
                 `x:real^(K,(K,K)finite_sum)finite_sum`;
                 `y:real^(K,(K,K)finite_sum)finite_sum`; `J:real^3^3`; `m:real`]
    CMCX_TDENS_FRAME) THEN
  ASM_SIMP_TAC[]);;

let CMCX_FRAME_ADENS = prove
 (`!(G:real^K->real^K^K).
     (!z. transp(G z) = G z)
     ==> !p x y (J:real^3^3) m.
           &0 < m /\
           (J ** basis 1) dot (J ** basis 1) = m /\ (J ** basis 2) dot (J ** basis 2) = m /\
           (J ** basis 3) dot (J ** basis 3) = &1 /\ (J ** basis 1) dot (J ** basis 2) = &0 /\
           (J ** basis 1) dot (J ** basis 3) = &0 /\ (J ** basis 2) dot (J ** basis 3) = &0 /\
           cmw_jx y = cmw_jx x ** J /\ cmw_c3 y 3 = vec 0
           ==> (\p x. sqrt(p4_e2(transp(cmw_jx x) ** G p ** cmw_jx x))) p y =
               m * (\p x. sqrt(p4_e2(transp(cmw_jx x) ** G p ** cmw_jx x))) p x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `G:real^K->real^K^K`; `p:real^K`;
                 `x:real^(K,(K,K)finite_sum)finite_sum`;
                 `y:real^(K,(K,K)finite_sum)finite_sum`; `J:real^3^3`; `m:real`]
    CMCX_TDENS_FRAME) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[SQRT_MUL] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]);;

(* The trace: cm_strace in the chart, and integrability on the shell.       *)

let CMCX_STRACE_CHART = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (u:real^3->real^K).
     cm_target S G d /\ cm_smap S u /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     (!z. transp(Q z) = Q z)
     ==> (\z. lift(cmw_tdens G Q (wan_rext u z) (cmw_pk wan_shell (wan_rext u) z)))
           absolutely_integrable_on wan_shell /\
         cm_strace G Q u = cmc_ptr G Q (:real^2) (\y. u(stereo2_n_inv y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMCX_TARGET_G) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMCX_PMAP_CHART) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`]
    CMC_PTR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real` (MP_TAC o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPECL [`\y. (u:real^3->real^K)(stereo2_n_inv y)`; `(:real^2)`]) THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THEN
  DISCH_THEN(LABEL_TAC "pint" o CONJUNCT1) THEN
  MP_TAC(ISPECL [`cmw_tdens (G:real^K->real^K^K) (Q:real^K->real^K^K)`;
                 `u:real^3->real^K`] CMCX_CHART_DENS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `cm_smap S (u:real^3->real^K)` THEN SIMP_TAC[cm_smap];
      MATCH_MP_TAC CMCX_FRAME_TDENS THEN ASM_REWRITE_TAC[];
      USE_THEN "pint" MP_TAC THEN REWRITE_TAC[CMC_TDEN_3]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. lift(if p4_e2(cm_wgram wan_shell (G:real^K->real^K^K) (wan_rext (u:real^3->real^K)) z) = &0
              then &0
              else p4_e2_pol (cm_wgram wan_shell G (wan_rext u) z)
                             (cm_wgram wan_shell (Q:real^K->real^K^K) (wan_rext u) z) /
                   sqrt(p4_e2(cm_wgram wan_shell G (wan_rext u) z)))) =
    (\z. lift(cmw_tdens G Q (wan_rext u z) (cmw_pk wan_shell (wan_rext u) z)))`
   ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; cmw_tdens; CMW_WGRAM_PK]; ALL_TAC] THEN
  ASM_REWRITE_TAC[cm_strace; cmc_ptr] THEN
  REWRITE_TAC[CMC_TDEN_3; DROP_CMUL] THEN
  ABBREV_TAC
   `I0 = drop(integral (:real^2)
           (\y. lift(cmw_tdens (G:real^K->real^K^K) (Q:real^K->real^K^K)
                      ((u:real^3->real^K)(stereo2_n_inv y))
                      (cmc_j3 (wan_wd (:real^2) 1 (\y. u(stereo2_n_inv y)) y)
                              (wan_wd (:real^2) 2 (\y. u(stereo2_n_inv y)) y)))))` THEN
  REAL_ARITH_TAC);;

(* The area: cm_sarea in the chart is half the planar G-trace of G.         *)

let CMCX_LIFT_HALF = prove
 (`!x. lift(x / &2) = inv(&2) % lift x`,
  REWRITE_TAC[real_div; GSYM LIFT_CMUL] THEN REWRITE_TAC[REAL_MUL_SYM]);;

let CMCX_SAREA_CHART = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K).
     cm_target S G d /\ cm_smap S u
     ==> (\z. lift(sqrt(p4_e2(cm_wgram wan_shell G (wan_rext u) z))))
           absolutely_integrable_on wan_shell /\
         cm_sarea G u = cmc_ptr G G (:real^2) (\y. u(stereo2_n_inv y)) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMCX_TARGET_G) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMCX_PMAP_CHART) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `G:real^K->real^K^K`]
    CMC_PTR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real` (MP_TAC o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPECL [`\y. (u:real^3->real^K)(stereo2_n_inv y)`; `(:real^2)`]) THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THEN
  DISCH_THEN(LABEL_TAC "pint" o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!y. sqrt(p4_e2(transp(cmw_jx (cmc_j3 (wan_wd (:real^2) 1 (\y. (u:real^3->real^K)(stereo2_n_inv y)) y)
                                          (wan_wd (:real^2) 2 (\y. u(stereo2_n_inv y)) y))) **
                   (G:real^K->real^K^K)(u(stereo2_n_inv y)) **
                   cmw_jx (cmc_j3 (wan_wd (:real^2) 1 (\y. u(stereo2_n_inv y)) y)
                                  (wan_wd (:real^2) 2 (\y. u(stereo2_n_inv y)) y)))) =
        cmc_tden G G (\y. u(stereo2_n_inv y)) y / &2`
   ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `G:real^K->real^K^K`;
                   `\y. (u:real^3->real^K)(stereo2_n_inv y)`; `y:real^2`] CMC_TDEN_3) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2(BETA_RULE th)))]) THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `\y. (u:real^3->real^K)(stereo2_n_inv y)`;
                   `y:real^2`] CMC_GRAM_PSD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p x. sqrt(p4_e2(transp(cmw_jx x) ** (G:real^K->real^K^K) p ** cmw_jx x))`;
                 `u:real^3->real^K`] CMCX_CHART_DENS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `cm_smap S (u:real^3->real^K)` THEN SIMP_TAC[cm_smap];
      MATCH_MP_TAC CMCX_FRAME_ADENS THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[CMCX_LIFT_HALF] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN
      USE_THEN "pint" MP_TAC THEN REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[cm_sarea; cmc_ptr] THEN
  SUBGOAL_THEN
   `(\z. lift(sqrt(p4_e2(cm_wgram wan_shell (G:real^K->real^K^K) (wan_rext (u:real^3->real^K)) z)))) =
    (\z. lift((\p x. sqrt(p4_e2(transp(cmw_jx x) ** G p ** cmw_jx x)))
               (wan_rext u z) (cmw_pk wan_shell (wan_rext u) z)))`
   SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; CMW_WGRAM_PK]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CMCX_LIFT_HALF] THEN
  SUBGOAL_THEN
   `integral (:real^2)
      (\y. inv(&2) % lift(cmc_tden (G:real^K->real^K^K) G
                                   (\y. (u:real^3->real^K)(stereo2_n_inv y)) y)) =
    inv(&2) % integral (:real^2) (\y. lift(cmc_tden G G (\y. u(stereo2_n_inv y)) y))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    USE_THEN "pint" MP_TAC THEN REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[DROP_CMUL] THEN
  ABBREV_TAC `I0 = drop(integral (:real^2)
                 (\y. lift(cmc_tden (G:real^K->real^K^K) G
                             (\y. (u:real^3->real^K)(stereo2_n_inv y)) y)))` THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* XFER part 2, rotations of S^2: the Gram matrices of the rotated map are   *)
(* conjugated by the rotation, so energy, area and trace are invariant       *)
(* (linear change of variables on the shell).                                *)
(* ========================================================================= *)

let CMCX_TDENS_ORTH = prove
 (`!(G:real^K->real^K^K) (Q:real^K->real^K^K) p
    (x:real^(K,(K,K)finite_sum)finite_sum) (y:real^(K,(K,K)finite_sum)finite_sum)
    (O:real^3^3).
     orthogonal_matrix O /\ cmw_jx y = cmw_jx x ** O
     ==> cmw_tdens G Q p y = cmw_tdens G Q p x /\
         p4_e2(transp(cmw_jx y) ** G p ** cmw_jx y) =
         p4_e2(transp(cmw_jx x) ** G p ** cmw_jx x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cmw_tdens] THEN
  SUBGOAL_THEN
   `!A:real^K^K. transp(cmw_jx (y:real^(K,(K,K)finite_sum)finite_sum)) ** A ** cmw_jx y =
                 transp O ** (transp(cmw_jx (x:real^(K,(K,K)finite_sum)finite_sum)) **
                              A ** cmw_jx x) ** O`
   (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[CMCX_E2_ORTH]);;

(* The jet of the rotated map, a.e. on the shell.                            *)

let CMCX_ROT_JET = prove
 (`!(u:real^3->real^K) (R:real^3^3).
     orthogonal_matrix R /\ wan_s2_w12 u
     ==> ?N. negligible N /\
             !z. z IN wan_shell DIFF N
                 ==> wan_rext (\y. u(R ** y)) z = wan_rext u (R ** z) /\
                     cmw_jx (cmw_pk wan_shell (wan_rext (\y. u(R ** y))) z) =
                     cmw_jx (cmw_pk wan_shell (wan_rext u) (R ** z)) ** R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`R:real^3^3`; `u:real^3->real^K`] CMR_ROT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "WPD")) THEN
  EXISTS_TAC
   `UNIONS {{z | z IN wan_shell /\
                 ~(wan_wd wan_shell i (wan_rext (\y. (u:real^3->real^K)(R ** y))) z =
                   vsum(1..3) (\j. ((R:real^3^3) ** basis i)$j %
                                   wan_wd wan_shell j (wan_rext u) (R ** z)))} | i IN 1..3}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC WAN_WD_UNIQUE THEN
    REWRITE_TAC[CMT_SHELL_OPEN; DIMINDEX_3] THEN ASM_REWRITE_TAC[GSYM wan_s2_w12] THEN
    USE_THEN "WPD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; IN_NUMSEG] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[CMR_ROT_REXT] THEN
  MATCH_MP_TAC CMCX_JX_EQ THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMW_C3_PK; CMCX_JX_MUL] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum(1..3) (\j. ((R:real^3^3) ** basis i)$j %
                              wan_wd wan_shell j (wan_rext (u:real^3->real^K)) (R ** z))` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMW_C3_PK]);;

(* Any density of the jet that is invariant under orthogonal frames has an   *)
(* invariant shell integral under rotations.                                 *)

let CMCX_ROT_DENS = prove
 (`!(Phi:real^K->real^(K,(K,K)finite_sum)finite_sum->real) (u:real^3->real^K)
    (R:real^3^3).
     orthogonal_matrix R /\ wan_s2_w12 u /\
     (!p x y (O:real^3^3). orthogonal_matrix O /\ cmw_jx y = cmw_jx x ** O
                           ==> Phi p y = Phi p x) /\
     (\z. lift(Phi (wan_rext u z) (cmw_pk wan_shell (wan_rext u) z)))
       absolutely_integrable_on wan_shell
     ==> (\z. lift(Phi (wan_rext (\y. u(R ** y)) z)
                       (cmw_pk wan_shell (wan_rext (\y. u(R ** y))) z)))
           absolutely_integrable_on wan_shell /\
         integral wan_shell
           (\z. lift(Phi (wan_rext (\y. u(R ** y)) z)
                         (cmw_pk wan_shell (wan_rext (\y. u(R ** y))) z))) =
         integral wan_shell (\z. lift(Phi (wan_rext u z) (cmw_pk wan_shell (wan_rext u) z)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inv") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `R:real^3^3`] CMCX_ROT_JET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `f = \z. lift((Phi:real^K->real^(K,(K,K)finite_sum)finite_sum->real)
                  (wan_rext (u:real^3->real^K) z) (cmw_pk wan_shell (wan_rext u) z))` THEN
  SUBGOAL_THEN
   `!z. z IN wan_shell DIFF N
        ==> (f:real^3->real^1)((R:real^3^3) ** z) =
            lift((Phi:real^K->real^(K,(K,K)finite_sum)finite_sum->real)
                  (wan_rext (\y. (u:real^3->real^K)(R ** y)) z)
                  (cmw_pk wan_shell (wan_rext (\y. u(R ** y))) z))`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[LIFT_EQ] THEN
    ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN USE_THEN "inv" MATCH_MP_TAC THEN
    EXISTS_TAC `R:real^3^3` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\z. (R:real^3^3) ** z) wan_shell = wan_shell` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN
    ASM_SIMP_TAC[CMR_ROT_SHELL] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `transp(R:real^3^3) ** w` THEN CONJ_TAC THENL
     [UNDISCH_TAC `orthogonal_matrix(R:real^3^3)` THEN
      SIMP_TAC[orthogonal_matrix; MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
      ASM_SIMP_TAC[CMR_ROT_SHELL; ORTHOGONAL_MATRIX_TRANSP]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^1`; `\z. (R:real^3^3) ** z`; `wan_shell`;
                 `integral wan_shell (f:real^3->real^1)`]
    HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_LINEAR) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  SUBGOAL_THEN `abs(det(R:real^3^3)) = &1` SUBST1_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
    EXISTS_TAC `\z. (f:real^3->real^1)((R:real^3^3) ** z)` THEN
    EXISTS_TAC `N:real^3->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral wan_shell (\z. (f:real^3->real^1)((R:real^3^3) ** z))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `N:real^3->bool` THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* The shell integrands of cm_strace and cm_sarea as jet densities.          *)

let CMCX_STRACE_PHI = prove
 (`!(G:real^K->real^K^K) (Q:real^K->real^K^K) (u:real^3->real^K).
     cm_strace G Q u =
     &2 / &3 * drop(integral wan_shell
                     (\z. lift(cmw_tdens G Q (wan_rext u z)
                                         (cmw_pk wan_shell (wan_rext u) z))))`,
  REWRITE_TAC[cm_strace; cmw_tdens; CMW_WGRAM_PK]);;

let CMCX_SAREA_PHI = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K).
     cm_sarea G u =
     &2 / &3 * drop(integral wan_shell
                     (\z. lift((\p x. sqrt(p4_e2(transp(cmw_jx x) ** G p ** cmw_jx x)))
                               (wan_rext u z) (cmw_pk wan_shell (wan_rext u) z))))`,
  REWRITE_TAC[cm_sarea; CMW_WGRAM_PK]);;

let CMCX_SPHERE_ROT = prove
 (`!(R:real^3^3).
     orthogonal_matrix R
     ==> IMAGE (\y. R ** y) (sphere(vec 0,&1)) = sphere(vec 0,&1) /\
         cmr_cone (sphere(vec 0,&1)) = wan_shell`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE; IN_SPHERE_0] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `transp(R:real^3^3) ** w` THEN CONJ_TAC THENL
     [UNDISCH_TAC `orthogonal_matrix(R:real^3^3)` THEN
      SIMP_TAC[orthogonal_matrix; MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
      ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM; ORTHOGONAL_MATRIX_TRANSP]];
    REWRITE_TAC[cmr_cone; EXTENSION; IN_ELIM_THM; IN_SPHERE_0] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THEN SIMP_TAC[] THEN
    REWRITE_TAC[wan_shell; IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC]);;

(* XFER part 2.                                                              *)

let CMCX_ROT_XFER = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) (R:real^3^3).
     cm_target S G d /\ orthogonal_matrix R /\ cm_smap S u
     ==> cm_smap S (\y. u(R ** y)) /\
         cm_sen G (\y. u(R ** y)) = cm_sen G u /\
         cm_sarea G (\y. u(R ** y)) = cm_sarea G u /\
         !Q:real^K->real^K^K.
            smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
            (!z. transp(Q z) = Q z)
            ==> cm_strace G Q (\y. u(R ** y)) = cm_strace G Q u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMCX_TARGET_G) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP CMCX_TARGET_GCOND) THEN
  MP_TAC(ISPEC `R:real^3^3` CMCX_SPHERE_ROT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_s2_w12 (u:real^3->real^K)` ASSUME_TAC THENL
   [UNDISCH_TAC `cm_smap S (u:real^3->real^K)` THEN SIMP_TAC[cm_smap]; ALL_TAC] THEN
  SUBGOAL_THEN `cm_smap S (\y. (u:real^3->real^K)((R:real^3^3) ** y))` ASSUME_TAC THENL
   [UNDISCH_TAC `cm_smap S (u:real^3->real^K)` THEN REWRITE_TAC[cm_smap] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`\y:real^3. (R:real^3^3) ** y`; `u:real^3->real^K`;
                     `sphere(vec 0:real^3,&1)`] CONTINUOUS_ON_COMPOSE) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; MATRIX_VECTOR_MUL_LINEAR];
      MP_TAC(ISPECL [`R:real^3^3`; `u:real^3->real^K`] CMR_ROT_FACTS) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
      ASM_SIMP_TAC[IN_SPHERE_0; ORTHOGONAL_MATRIX_NORM]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `wan_s2_w12 (\y. (u:real^3->real^K)((R:real^3^3) ** y))` ASSUME_TAC THENL
   [UNDISCH_TAC `cm_smap S (\y. (u:real^3->real^K)((R:real^3^3) ** y))` THEN
    SIMP_TAC[cm_smap];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `CMR_GCOND (G:real^K->real^K^K) Lam` THEN
    REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_DENS) THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `\y. (u:real^3->real^K)((R:real^3^3) ** y)`;
                   `Lam:real`] CMR_SEN_DENS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `R:real^3^3`; `Lam:real`;
                   `sphere(vec 0:real^3,&1)`] CMR_ROT_SEN) THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMT_SHELL_OPEN];
    REWRITE_TAC[CMCX_SAREA_PHI] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\p x. sqrt(p4_e2(transp(cmw_jx x) ** (G:real^K->real^K^K) p ** cmw_jx x))`;
                   `u:real^3->real^K`; `R:real^3^3`] CMCX_ROT_DENS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC
         [`p:real^K`; `x:real^(K,(K,K)finite_sum)finite_sum`;
          `y:real^(K,(K,K)finite_sum)finite_sum`; `O:real^3^3`] THEN
        STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
        MP_TAC(ISPECL [`G:real^K->real^K^K`; `G:real^K->real^K^K`; `p:real^K`;
                       `x:real^(K,(K,K)finite_sum)finite_sum`;
                       `y:real^(K,(K,K)finite_sum)finite_sum`; `O:real^3^3`]
          CMCX_TDENS_ORTH) THEN
        ASM_SIMP_TAC[];
        MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                       `u:real^3->real^K`] CMCX_SAREA_CHART) THEN
        ASM_REWRITE_TAC[CMW_WGRAM_PK] THEN SIMP_TAC[]];
      SIMP_TAC[]];
    X_GEN_TAC `Q:real^K->real^K^K` THEN STRIP_TAC THEN
    REWRITE_TAC[CMCX_STRACE_PHI] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`cmw_tdens (G:real^K->real^K^K) (Q:real^K->real^K^K)`;
                   `u:real^3->real^K`; `R:real^3^3`] CMCX_ROT_DENS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC
         [`p:real^K`; `x:real^(K,(K,K)finite_sum)finite_sum`;
          `y:real^(K,(K,K)finite_sum)finite_sum`; `O:real^3^3`] THEN
        STRIP_TAC THEN
        MP_TAC(ISPECL [`G:real^K->real^K^K`; `Q:real^K->real^K^K`; `p:real^K`;
                       `x:real^(K,(K,K)finite_sum)finite_sum`;
                       `y:real^(K,(K,K)finite_sum)finite_sum`; `O:real^3^3`]
          CMCX_TDENS_ORTH) THEN
        ASM_SIMP_TAC[];
        MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                       `Q:real^K->real^K^K`; `u:real^3->real^K`] CMCX_STRACE_CHART) THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]];
      SIMP_TAC[]]]);;


(* ========================================================================= *)
(* XFER part 3, harmonic spheres are invariant under rotations.              *)
(* ========================================================================= *)

let CMCX_REXT_ROT_SMOOTH = prove
 (`!(R:real^3^3) (u:real^3->real^K).
     orthogonal_matrix R /\ smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u)
     ==> smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (\y. u(R ** y)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_rext (\y. (u:real^3->real^K)((R:real^3^3) ** y)) =
                wan_rext u o (\z. R ** z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[CMR_ROT_REXT]; ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^3 | ~(z = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{z:real^3 | ~(z = a)} = (:real^3) DELETE a`] THEN
    SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM];
    MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `\x:real^3. x`; `\z:real^3. (R:real^3^3) ** z`]
      SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR; o_DEF]]);;

(* For small e the projected variations are maps of S^2 into S.             *)

let CMCX_VAR_SMAP = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) (phi:real^3->real^K).
     cm_target S G d /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
     (!y. y IN sphere(vec 0,&1) ==> u y IN S) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi)
     ==> ?del. &0 < del /\
               !e. abs e < del ==> cm_smap S (\y. closest_point S (u y + e % phi y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `open {z:real^3 | ~(z = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{z:real^3 | ~(z = a)} = (:real^3) DELETE a`] THEN
    SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(f:real^3->real^K). smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext f)
                         ==> f continuous_on sphere(vec 0,&1)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `wan_rext (f:real^3->real^K)` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0; wan_rext] THEN SIMP_TAC[REAL_INV_1; VECTOR_MUL_LID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN
      MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. &0 < B /\ !y. y IN sphere(vec 0:real^3,&1)
                                   ==> norm((phi:real^3->real^K) y) <= B`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`phi:real^3->real^K`; `sphere(vec 0:real^3,&1)`]
      COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_SIMP_TAC[COMPACT_SPHERE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  EXISTS_TAC `d / B` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!y. y IN sphere(vec 0:real^3,&1)
        ==> (u:real^3->real^K) y + e % (phi:real^3->real^K) y IN cm_tube S d`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN
    EXISTS_TAC `(u:real^3->real^K) y` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[dist; VECTOR_ARITH `(a + b) - a:real^N = b`; NORM_MUL] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs e * B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_ABS_POS];
      UNDISCH_TAC `abs e < d / B` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ]];
    ALL_TAC] THEN
  REWRITE_TAC[cm_smap] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\y. (u:real^3->real^K) y + e % (phi:real^3->real^K) y`;
                   `closest_point (S:real^K->bool)`; `sphere(vec 0:real^3,&1)`]
      CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN ASM SET_TAC[]];
    REWRITE_TAC[wan_s2_w12] THEN MATCH_MP_TAC CMW_REXT_C1_W12 THEN
    SUBGOAL_THEN
     `smooth_map_on {z:real^3 | ~(z = vec 0)}
        (wan_rext (\y. closest_point S ((u:real^3->real^K) y + e % (phi:real^3->real^K) y)))`
     (fun th -> REWRITE_TAC[REWRITE_RULE[smooth_map_on] th]) THEN
    SUBGOAL_THEN
     `wan_rext (\y. closest_point S ((u:real^3->real^K) y + e % (phi:real^3->real^K) y)) =
      closest_point S o (\z. wan_rext u z + e % wan_rext phi z)`
     SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; wan_rext]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; wan_rext] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[ETA_AX]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

let CMCX_SHARM_ROT = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) (R:real^3^3).
     cm_target S G d /\ orthogonal_matrix R /\ cm_sharmonic S G u
     ==> cm_sharmonic S G (\y. u(R ** y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_sharmonic] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMCX_REXT_ROT_SMOOTH] THEN
  SUBGOAL_THEN `!y. y IN sphere(vec 0,&1) ==> (R:real^3^3) ** y IN sphere(vec 0,&1) /\
                                              transp R ** y IN sphere(vec 0,&1)`
   ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM; ORTHOGONAL_MATRIX_TRANSP];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. (R:real^3^3) ** transp R ** y = y /\ transp R ** R ** y = y`
   ASSUME_TAC THENL
   [UNDISCH_TAC `orthogonal_matrix(R:real^3^3)` THEN
    SIMP_TAC[orthogonal_matrix; MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `c:real^K` THEN DISCH_TAC THEN
    UNDISCH_TAC `~(?c. !y. y IN sphere(vec 0,&1) ==> (u:real^3->real^K) y = c)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `c:real^K` THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `transp(R:real^3^3) ** y` o check (fun th ->
      can (find_term (fun t -> t = `c:real^K`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `phi:real^3->real^K` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `smooth_map_on {z:real^3 | ~(z = vec 0)}
        (wan_rext (\y. (phi:real^3->real^K)(transp(R:real^3^3) ** y)))`
     ASSUME_TAC THENL
     [MATCH_MP_TAC CMCX_REXT_ROT_SMOOTH THEN
      ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSP];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^3->real^K`;
                   `\y. (phi:real^3->real^K)(transp(R:real^3^3) ** y)`] CMCX_VAR_SMAP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\e. cm_sen (G:real^K->real^K^K)
                      (\y. closest_point S ((u:real^3->real^K) y +
                                            e % (phi:real^3->real^K)(transp(R:real^3^3) ** y)))` THEN
    EXISTS_TAC `del:real` THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `e:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `\y. closest_point S ((u:real^3->real^K) y +
                                         e % (phi:real^3->real^K)(transp(R:real^3^3) ** y))`;
                   `R:real^3^3`] CMCX_ROT_XFER) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC]);;


(* ========================================================================= *)
(* The headline CMC_XFER_STATEMENT.                                          *)
(* ========================================================================= *)

let CMCX_XFER = prove
 (`!kk:K->bool. CMC_XFER_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CMC_XFER_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `u:real^3->real^K` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMCX_PMAP_CHART THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMCX_SEN_CHART THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                     `u:real^3->real^K`] CMCX_SAREA_CHART) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `Q:real^K->real^K^K` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                     `Q:real^K->real^K^K`; `u:real^3->real^K`] CMCX_STRACE_CHART) THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]];
    MAP_EVERY X_GEN_TAC [`u:real^3->real^K`; `R:real^3^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMCX_ROT_XFER THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real^3->real^K`; `R:real^3^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMCX_SHARM_ROT THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* SIM, planar similarities z |-> r z + c (r > 0): global weak partials, the *)
(* energy and trace integrals, and property (B).  Built on the affine        *)
(* transport lemmas CMR_AFF_* of pc_cmr_scale.                               *)
(* ========================================================================= *)

let CMCX_AFF_IMAGES = prove
 (`!r (c:real^2) E.
     ~(r = &0)
     ==> IMAGE (\x. inv r % x + --(inv r % c)) (:real^2) = (:real^2) /\
         IMAGE (\x. inv r % x + --(inv r % c)) (IMAGE (\z. r % z + c) E) = E`,
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[CMR_AFF_PREIMAGE; IN_UNIV] THEN SET_TAC[];
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_SIMP_TAC[CMR_AFF_INV; IMAGE_ID]]);;

(* The global weak partials of w(r z + c).                                  *)

let CMCX_SIM_WPD = prove
 (`!S (w:real^2->real^K) r (c:real^2) i.
     cmc_pmap S w /\ compact S /\ &0 < r /\ 1 <= i /\ i <= 2
     ==> (\z. r % wan_wd (:real^2) i w (r % z + c)) IN lspace (:real^2) (&2) /\
         wan_wpd (:real^2) i (\z. w(r % z + c)) (\z. r % wan_wd (:real^2) i w (r % z + c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `i:num`] CMC_PMAP_WD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:real`; `c:real^2`; `{}:real^2->bool`] CMCX_AFF_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `(\z. r % wan_wd (:real^2) i (w:real^2->real^K) (r % z + c)) IN lspace (:real^2) (&2)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_CMUL THEN
    MP_TAC(ISPECL [`wan_wd (:real^2) i (w:real^2->real^K)`; `(:real^2)`; `r:real`;
                   `c:real^2`] CMR_AFF_LSPACE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wan_wpd] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\z:real^2. r % z + c`; `w:real^2->real^K`; `k:real^2->bool`]
      CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      UNDISCH_TAC `cmc_pmap S (w:real^2->real^K)` THEN SIMP_TAC[cmc_pmap]];
    MATCH_MP_TAC WAN_LSPACE2_IMP_LLOC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `phi:real^2->real` THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?B. &0 < B /\ IMAGE (\z. r % z + c) k SUBSET ball(vec 0:real^2,B)`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\z:real^2. r % z + c) k` COMPACT_IMP_BOUNDED) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN
    ASM_MESON_TAC[REAL_ARITH `x <= B ==> x < B + &1`];
    ALL_TAC] THEN
  ABBREV_TAC `s = ball(vec 0:real^2,B)` THEN
  SUBGOAL_THEN `open (s:real^2->bool) /\ bounded s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[OPEN_BALL; BOUNDED_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (w:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_PMAP_W12 THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t = IMAGE (\x. inv r % x + --(inv r % c)) (s:real^2->bool)` THEN
  SUBGOAL_THEN `(k:real^2->bool) SUBSET t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN SIMP_TAC[CMR_AFF_PREIMAGE; ASSUME `~(r = &0)`] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    UNDISCH_TAC `IMAGE (\z. r % z + c) k SUBSET (s:real^2->bool)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `w:real^2->real^K`; `r:real`; `c:real^2`] CMR_AFF_W12) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[wan_wpd] THEN
  DISCH_THEN(MP_TAC o SPEC `phi:real^2->real` o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wan_test] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `(a:real^K) = a' /\ (b:real^K) = b'
                        ==> (a = --b ==> a' = --b')`) THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((x:real^2) IN k)` ASSUME_TAC THENL
     [UNDISCH_TAC `(k:real^2->bool) SUBSET t` THEN
      UNDISCH_TAC `~((x:real^2) IN t)` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[wan_dpart] THEN
    MP_TAC(ISPECL [`phi:real^2->real`; `k:real^2->bool`; `basis i:real^2`; `x:real^2`]
      WAN_TEST_DERIV_ZERO) THEN
    ASM_SIMP_TAC[DROP_VEC; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral t (\x. (phi:real^2->real) x %
                              (r % wan_wd (:real^2) i (w:real^2->real^K) (r % x + c)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN t /\
                     ~(wan_wd s i (w:real^2->real^K) (r % x + c) =
                       wan_wd (:real^2) i w (r % x + c))}` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "t" THEN
      MP_TAC(ISPECL [`\y:real^2. ~(wan_wd s i (w:real^2->real^K) y = wan_wd (:real^2) i w y)`;
                     `s:real^2->bool`; `r:real`; `c:real^2`] CMR_AFF_SET) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC CMR_AFF_NEGLIGIBLE THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `s:real^2->bool`; `i:num`]
        CMC_WD_RESTRICT) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]];
    GEN_REWRITE_TAC LAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(phi:real^2->real) x = &0` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(k:real^2->bool) SUBSET t` THEN
    UNDISCH_TAC `~((x:real^2) IN t)` THEN SET_TAC[]]);;

(* The similarity w(r z + c) is a planar map; its partials are r times the  *)
(* partials of w at r z + c almost everywhere.                             *)

let CMCX_SIM_PMAP = prove
 (`!S (w:real^2->real^K) r (c:real^2).
     cmc_pmap S w /\ compact S /\ &0 < r
     ==> cmc_pmap S (\z. w(r % z + c)) /\
         !i. 1 <= i /\ i <= 2
             ==> negligible {z | ~(wan_wd (:real^2) i (\z. w(r % z + c)) z =
                                   r % wan_wd (:real^2) i w (r % z + c))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[cmc_pmap] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`\z:real^2. r % z + c`; `w:real^2->real^K`; `(:real^2)`]
        CONTINUOUS_ON_COMPOSE) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN
        UNDISCH_TAC `cmc_pmap S (w:real^2->real^K)` THEN SIMP_TAC[cmc_pmap]];
      UNDISCH_TAC `cmc_pmap S (w:real^2->real^K)` THEN SIMP_TAC[cmc_pmap];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      EXISTS_TAC `\z. r % wan_wd (:real^2) i (w:real^2->real^K) (r % z + c)` THEN
      MATCH_MP_TAC CMCX_SIM_WPD THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `r:real`; `c:real^2`; `i:num`]
      CMCX_SIM_WPD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\z:real^2. (w:real^2->real^K)(r % z + c)`; `i:num`;
                   `\z. r % wan_wd (:real^2) i (w:real^2->real^K) (r % z + c)`]
      CMC_WD_EQ_AE) THEN
    ASM_REWRITE_TAC[]]);;

(* Gram matrices and trace densities under a scaling of the partials.     *)

let CMCX_GRAM_SCALE = prove
 (`!(G:real^K->real^K^K) (u:real^2->real^K) (w:real^2->real^K) z y r.
     u z = w y /\
     (!i. 1 <= i /\ i <= 2 ==> wan_wd (:real^2) i u z = r % wan_wd (:real^2) i w y)
     ==> cmc_gram G u z = (r pow 2) %% cmc_gram G w y`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; MATRIX_CMUL_COMPONENT; CMC_GRAM2_ENTRIES] THEN
  ASM_SIMP_TAC[ARITH; MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN REAL_ARITH_TAC);;

let CMCX_TDEN_SCALE = prove
 (`!(G:real^K->real^K^K) (Q:real^K->real^K^K) (u:real^2->real^K) (w:real^2->real^K) z y r.
     ~(r = &0) /\ u z = w y /\
     (!i. 1 <= i /\ i <= 2 ==> wan_wd (:real^2) i u z = r % wan_wd (:real^2) i w y)
     ==> cmc_tden G Q u z = r pow 2 * cmc_tden G Q w y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_tden] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^2->real^K`; `w:real^2->real^K`;
                 `z:real^2`; `y:real^2`; `r:real`] CMCX_GRAM_SCALE) THEN
  MP_TAC(ISPECL [`Q:real^K->real^K^K`; `u:real^2->real^K`; `w:real^2->real^K`;
                 `z:real^2`; `y:real^2`; `r:real`] CMCX_GRAM_SCALE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[DET_CMUL; TRACE_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; DIMINDEX_2] THEN
  ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[SQRT_MUL] THEN
  SUBGOAL_THEN `sqrt(((r:real) pow 2) pow 2) = r pow 2` SUBST1_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  ABBREV_TAC `k = (r:real) pow 2` THEN
  SUBGOAL_THEN `k * inv k = &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN EXPAND_TAC "k" THEN
    ASM_REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN CONV_TAC REAL_RING);;

(* The two scaling identities hold off one null set.                     *)

let CMCX_SIM_AE = prove
 (`!S (w:real^2->real^K) r (c:real^2).
     cmc_pmap S w /\ compact S /\ &0 < r
     ==> ?N. negligible N /\
             !z. ~(z IN N)
                 ==> (!G:real^K->real^K^K.
                        cmc_gram G (\z. w(r % z + c)) z =
                        (r pow 2) %% cmc_gram G w (r % z + c)) /\
                     (!G Q:real^K->real^K^K.
                        cmc_tden G Q (\z. w(r % z + c)) z =
                        r pow 2 * cmc_tden G Q w (r % z + c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `r:real`; `c:real^2`]
    CMCX_SIM_PMAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  EXISTS_TAC `{z | ~(wan_wd (:real^2) 1 (\z. (w:real^2->real^K)(r % z + c)) z =
                     r % wan_wd (:real^2) 1 w (r % z + c))} UNION
              {z | ~(wan_wd (:real^2) 2 (\z. (w:real^2->real^K)(r % z + c)) z =
                     r % wan_wd (:real^2) 2 w (r % z + c))}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> wan_wd (:real^2) i (\z. (w:real^2->real^K)(r % z + c)) z =
            r % wan_wd (:real^2) i w (r % z + c)`
   ASSUME_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `1 <= i /\ i <= 2 ==> i = 1 \/ i = 2`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [MATCH_MP_TAC CMCX_GRAM_SCALE; MATCH_MP_TAC CMCX_TDEN_SCALE] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The trace density only sees the symmetric part of Q.                   *)

let CMCX_DOT_TRANSP = prove
 (`!(M:real^K^K) a b. a dot (transp M ** b) = b dot (M ** a)`,
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN MATCH_ACCEPT_TAC DOT_SYM);;

let CMCX_GRAM_SYMPART = prove
 (`!(G:real^K->real^K^K) (Q:real^K->real^K^K) (w:real^2->real^K) x.
     (!z. transp(G z) = G z)
     ==> transp(cmc_gram G w x) = cmc_gram G w x /\
         cmc_gram (\z. inv(&2) %% (Q z + transp(Q z))) w x =
         inv(&2) %% (cmc_gram Q w x + transp(cmc_gram Q w x))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; TRANSP_COMPONENT; MATRIX_CMUL_COMPONENT;
           MATRIX_ADD_COMPONENT; CMC_GRAM2_ENTRIES] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB; DOT_RMUL; DOT_RADD;
              CMCX_DOT_TRANSP] THEN
  MP_TAC(ISPECL [`(G:real^K->real^K^K)((w:real^2->real^K) x)`;
                 `wan_wd (:real^2) 1 (w:real^2->real^K) x`;
                 `wan_wd (:real^2) 2 (w:real^2->real^K) x`] CMCX_DOT_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let CMCX_TDEN_SYMPART = prove
 (`!(G:real^K->real^K^K) (Q:real^K->real^K^K) (w:real^2->real^K) x.
     (!z. transp(G z) = G z)
     ==> cmc_tden G (\z. inv(&2) %% (Q z + transp(Q z))) w x = cmc_tden G Q w x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`G:real^K->real^K^K`; `Q:real^K->real^K^K`; `w:real^2->real^K`;
                `x:real^2`] CMCX_GRAM_SYMPART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[cmc_tden] THEN
  ABBREV_TAC `A = cmc_gram (G:real^K->real^K^K) (w:real^2->real^K) x` THEN
  ABBREV_TAC `B = cmc_gram (Q:real^K->real^K^K) (w:real^2->real^K) x` THEN
  REWRITE_TAC[TRACE_CMUL; TRACE_ADD; TRACE_TRANSP; MATRIX_MUL_RMUL; MATRIX_ADD_LDISTRIB] THEN
  SUBGOAL_THEN `trace((A:real^2^2) ** transp B) = trace(A ** B)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM TRACE_TRANSP] THEN
    REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN ASM_REWRITE_TAC[] THEN
    MATCH_ACCEPT_TAC TRACE_MUL_SYM;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `inv(&2) * (x + x) = x`]);;

let CMCX_SYMPART = prove
 (`!(Q:real^K->real^K^K).
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K)
     ==> ((vectorize:real^K^K->real^(K,K)finite_prod) o
          (\z. inv(&2) %% (Q z + transp(Q z)))) continuous_on (:real^K) /\
         (!z. transp(inv(&2) %% (Q z + transp(Q z))) = inv(&2) %% (Q z + transp(Q z)))`,
  GEN_TAC THEN REWRITE_TAC[o_DEF; CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[MATRIX_CMUL_COMPONENT; MATRIX_ADD_COMPONENT; TRANSP_COMPONENT;
                LIFT_CMUL; LIFT_ADD] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MATRIX_ADD; TRANSP_TRANSP] THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC MATRIX_ADD_SYM]);;

(* Change of variables for the energy and trace integrals.                *)

let CMCX_AFF_LMEAS = prove
 (`!r (c:real^2) E.
     ~(r = &0) /\ lebesgue_measurable E
     ==> lebesgue_measurable (IMAGE (\z. r % z + c) E)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\z. r % z + c) (E:real^2->bool) =
                IMAGE (\x. c + x) (IMAGE (\z. r % z) E)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_ACCEPT_TAC VECTOR_ADD_SYM;
    ALL_TAC] THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_TRANSLATION] THEN
  MP_TAC(ISPECL [`\z:real^2. r % z`; `E:real^2->bool`]
    LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LINEAR_SCALING; VECTOR_MUL_LCANCEL];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let CMCX_SIM_INTEGRAL = prove
 (`!(g:real^2->real) (f:real^2->real) r (c:real^2) E.
     &0 < r /\
     (\x. lift(f x)) integrable_on IMAGE (\z. r % z + c) E /\
     negligible {z | z IN E /\ ~(g z = r pow 2 * f(r % z + c))}
     ==> drop(integral E (\z. lift(g z))) =
         drop(integral (IMAGE (\z. r % z + c) E) (\x. lift(f x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^2. lift(f x)`; `IMAGE (\z. r % z + c) (E:real^2->bool)`;
                 `r:real`; `c:real^2`] CMR_AFF_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:real`; `c:real^2`; `E:real^2->bool`] CMCX_AFF_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `drop(integral E (\z. r pow 2 % lift((f:real^2->real)(r % z + c))))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{z | z IN E /\ ~((g:real^2->real) z = r pow 2 * f(r % z + c))}` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^2->real) x = r pow 2 * f(r % x + c)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[LIFT_CMUL]];
    ASM_SIMP_TAC[INTEGRAL_CMUL; VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_POW_EQ_0; ARITH_EQ;
                 VECTOR_MUL_LID]]);;

let CMCX_SIM_PEN = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) r (c:real^2) E.
     cm_target S G d /\ cmc_pmap S w /\ &0 < r /\ lebesgue_measurable E
     ==> cmc_pen G E (\z. w(r % z + c)) = cmc_pen G (IMAGE (\z. r % z + c) E) w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact (S:real^K->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable (IMAGE (\z. r % z + c) (E:real^2->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CMCX_AFF_LMEAS THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `r:real`; `c:real^2`] CMCX_SIM_AE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:real^2->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[cmc_pen] THEN MATCH_MP_TAC CMCX_SIM_INTEGRAL THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                   `IMAGE (\z. r % z + c) (E:real^2->bool)`] CMC_PEN_INTEGRABLE) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `N:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
    MATCH_MP_TAC(TAUT `(~q ==> p) ==> (r /\ ~p ==> q)`) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SIMP_TAC[TRACE_CMUL]]);;

let CMCX_SIM_PTR = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) r (c:real^2) Q E.
     cm_target S G d /\ cmc_pmap S w /\ &0 < r /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K) /\
     lebesgue_measurable E
     ==> cmc_ptr G Q E (\z. w(r % z + c)) = cmc_ptr G Q (IMAGE (\z. r % z + c) E) w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact (S:real^K->bool) /\ (!z. transp((G:real^K->real^K^K) z) = G z)`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable (IMAGE (\z. r % z + c) (E:real^2->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CMCX_AFF_LMEAS THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(ISPEC `Q:real^K->real^K^K` CMCX_SYMPART) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!(v:real^2->real^K) x.
      cmc_tden G Q v x =
      cmc_tden (G:real^K->real^K^K) (\z. inv(&2) %% ((Q:real^K->real^K^K) z + transp(Q z))) v x`
   ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMCX_TDEN_SYMPART THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `\z:real^K. inv(&2) %% ((Q:real^K->real^K^K) z + transp(Q z))`]
    CMC_PTR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real` (LABEL_TAC "pf")) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `r:real`; `c:real^2`] CMCX_SIM_AE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:real^2->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[cmc_ptr] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMCX_SIM_INTEGRAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    USE_THEN "pf" (MP_TAC o SPECL [`w:real^2->real^K`; `IMAGE (\z. r % z + c) (E:real^2->bool)`] o
                   CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `N:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
    MATCH_MP_TAC(TAUT `(~q ==> p) ==> (r /\ ~p ==> q)`) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SIMP_TAC[]]);;

(* Balls under the similarity, and property (B) of cmc_ah.               *)

let CMCX_AFF_BALL_IMAGES = prove
 (`!r (c:real^2) a e.
     &0 < r
     ==> IMAGE (\x. inv r % x + --(inv r % c)) (ball(r % a + c,r * e)) = ball(a,e) /\
         IMAGE (\x. inv r % x + --(inv r % c)) (ball(r % a + c,(r * e) / &8)) =
         ball(a,e / &8) /\
         IMAGE (\x. inv r % x + --(inv r % c)) (cball(r % a + c,r * e)) = cball(a,e)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMR_AFF_BALLS] THEN
  ASM_SIMP_TAC[CMR_AFF_INV; REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < r ==> (r * e) / r = e /\ ((r * e) / &8) / r = e / &8`]);;

let CMCX_AFF_BALLS_INV = prove
 (`!r (c:real^2) a e.
     &0 < r
     ==> IMAGE (\x. inv(inv r) % x + --(inv(inv r) % --(inv r % c))) (ball(a,e)) =
         ball(r % a + c,r * e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inv r`; `--(inv r % c):real^2`; `a:real^2`; `e:real`] CMR_AFF_BALLS) THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_INV_INV; VECTOR_MUL_RNEG; VECTOR_NEG_NEG; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    REWRITE_TAC[real_div; REAL_INV_INV] THEN REAL_ARITH_TAC]);;

let CMCX_SIM_AH = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) r (c:real^2) e0 eta.
     cm_target S G d /\ cmc_pmap S w /\ &0 < r /\ cmc_ah S G e0 eta w
     ==> cmc_ah S G e0 eta (\z. w(r % z + c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (S:real^K->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMCX_TARGET_GCOND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(r = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. open s /\ bounded s ==> wan_w12 s (w:real^2->real^K)` (LABEL_TAC "w12")
  THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_PMAP_W12 THEN EXISTS_TAC `S:real^K->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `cmc_ah S G e0 eta (w:real^2->real^K)` THEN REWRITE_TAC[cmc_ah] THEN
  DISCH_THEN(LABEL_TAC "ah") THEN
  MAP_EVERY X_GEN_TAC
   [`n:num`; `cc:num->real^2`; `rr:num->real`; `vv:num->real^2->real^K`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rad") (CONJUNCTS_THEN2 (LABEL_TAC "dis")
    (CONJUNCTS_THEN2 (LABEL_TAC "en") (LABEL_TAC "min")))) THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n
        ==> cm_minimizer S G (ball(r % (cc:num->real^2) k + c,(r * rr k) / &8))
              (\y. (vv:num->real^2->real^K) k (inv r % y + --(inv r % c))) /\
            wan_w120 (ball(r % cc k + c,(r * rr k) / &8))
              (\y. vv k (inv r % y + --(inv r % c)) - (w:real^2->real^K) y)`
   (LABEL_TAC "mink") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "min" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `ball(r % (cc:num->real^2) k + c,(r * rr k) / &8) =
      IMAGE (\x. inv(inv r) % x + --(inv(inv r) % --(inv r % c))) (ball(cc k,rr k / &8))`
     SUBST1_TAC THENL
     [ASM_SIMP_TAC[CMCX_AFF_BALLS_INV] THEN AP_TERM_TAC THEN
      REWRITE_TAC[PAIR_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`;
                     `ball((cc:num->real^2) k,rr k / &8)`;
                     `(vv:num->real^2->real^K) k`; `Lam:real`; `inv r`;
                     `--(inv r % c):real^2`] CMR_AFF_MINIMIZER) THEN
      ASM_REWRITE_TAC[OPEN_BALL; REAL_LT_INV_EQ];
      MP_TAC(ISPECL [`ball((cc:num->real^2) k,rr k / &8)`;
                     `\y. (vv:num->real^2->real^K) k y - (w:real^2->real^K)(r % y + c)`;
                     `inv r`; `--(inv r % c):real^2`] CMR_AFF_W120) THEN
      ASM_SIMP_TAC[OPEN_BALL; REAL_LT_INV_EQ; CMR_AFF_INV]];
    ALL_TAC] THEN
  USE_THEN "ah" (MP_TAC o SPECL
    [`n:num`; `\k. r % (cc:num->real^2) k + c`; `\k. r * (rr:num->real) k`;
     `\k y. (vv:num->real^2->real^K) k (inv r % y + --(inv r % c))`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(SET_RULE
       `!f:real^2->real^2. DISJOINT (IMAGE f s) (IMAGE f t) ==> DISJOINT s t`) THEN
      EXISTS_TAC `\x:real^2. inv r % x + --(inv r % c)` THEN
      ASM_SIMP_TAC[CMCX_AFF_BALL_IMAGES];
      USE_THEN "en" MP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> a < e0 ==> b < e0`) THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ball(r % (cc:num->real^2) k + c,r * rr k)`; `G:real^K->real^K^K`;
                     `w:real^2->real^K`; `Lam:real`; `r:real`; `c:real^2`] CMR_AFF_GDIR) THEN
      ASM_SIMP_TAC[CMCX_AFF_BALL_IMAGES; OPEN_BALL; BOUNDED_BALL];
      USE_THEN "mink" ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= eta ==> b <= eta`) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "mink" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[cm_minimizer; cm_wmap] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ball(r % (cc:num->real^2) k + c,(r * rr k) / &8)`;
                 `\y. (w:real^2->real^K) y -
                      (vv:num->real^2->real^K) k (inv r % y + --(inv r % c))`;
                 `r:real`; `c:real^2`] CMR_AFF_DIR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "w12" MATCH_MP_TAC THEN REWRITE_TAC[OPEN_BALL; BOUNDED_BALL];
    ALL_TAC] THEN
  SIMP_TAC[CMCX_AFF_BALL_IMAGES; CMR_AFF_INV; ASSUME `&0 < r`; ASSUME `~(r = &0)`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ========================================================================= *)
(* The headline CMC_SIM_STATEMENT.  The statement writes the similarity as a *)
(* + lam z; the lemmas above use r z + c.                                    *)
(* ========================================================================= *)

let CMCX_SIM = prove
 (`!kk:K->bool. CMC_SIM_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CMC_SIM_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`w:real^2->real^K`; `a:real^2`; `lam:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^2. a + lam % z = lam % z + a` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_ACCEPT_TAC VECTOR_ADD_SYM; ALL_TAC] THEN
  SUBGOAL_THEN `compact (S:real^K->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `lam:real`; `a:real^2`]
    CMCX_SIM_PMAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    EXISTS_TAC `{z | ~(wan_wd (:real^2) i (\z. (w:real^2->real^K)(lam % z + a)) z =
                       lam % wan_wd (:real^2) i w (lam % z + a))}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMCX_SIM_PEN THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMCX_SIM_PTR THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMCX_SIM_AH THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[]]);;

