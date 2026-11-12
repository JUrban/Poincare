(* ========================================================================= *)
(* Unit pc_cmp_shup (comparison-geometry layer CMP, the first of two units   *)
(* for the Gromoll-Meyer core CMP_R5_SOUL of pc_cmp_soul): the strict upper  *)
(* Hessian bound of distance functions.  sec >= 0 along a ray and sec >= k0  *)
(* on its last stretch [t1, t] give the Jacobi shape operator bound          *)
(* S(t) <= 1/t1 - k0 (t - t1) on normal vectors (Riccati and the mean value  *)
(* theorem), instead of 1/t (pc_cmp_hup).  Carried through the exp pullback  *)
(* and the Calabi barrier as in pc_cmp_hup, this gives an upper barrier D of *)
(* d(q, sigma s) with D''(t0) <= 4/L - k0 ew (1 - D'^2) when sec >= k0 on    *)
(* the ew-ball around sigma(t0) and L = d(sigma t0, q) >= 4 ew: distance     *)
(* functions from far points are strictly concave across the direction to q. *)
(* ========================================================================= *)

needs "src/pc_cmp_busemann.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The Jacobi-system form.  With R >= 0 on the normal space,                 *)
(* R >= k0 there on [t1, t] and A invertible on (0, L): for t1 <= t < L the *)
(* shape operator satisfies e.S(t)e <= (1/t1 - k0 (t - t1)) e.e on normal e, *)
(* and the Hessian form of CMPE_RAY_HESS_UP improves accordingly.            *)
(* ========================================================================= *)

let CMPSH_SHAPE_WINDOW = prove
 (`!(A:real->real^N^N) B R L k0 t1 (e:real^N) t.
        cmp_jsys A B R L /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> &0 <= v dot (R t ** v)) /\
        (!s v. t1 <= s /\ s <= t /\ v$1 = &0 ==> k0 * (v dot v) <= v dot (R s ** v)) /\
        (!t. &0 < t /\ t < L ==> invertible(A t)) /\
        &0 < t1 /\ t1 <= t /\ t < L /\ e$1 = &0
        ==> e dot ((B t ** matrix_inv(A t)) ** e) <= (inv t1 - k0 * (t - t1)) * (e dot e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(e:real^N) dot (((B:real->real^N^N) t1 ** matrix_inv((A:real->real^N^N) t1)) ** e) <=
    inv t1 * (e dot e)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `&0`; `e:real^N`] CMPJ_SHAPE_UPPER_GEN) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; CMP_SN_FLAT; CMP_CS_FLAT; REAL_MUL_LID] THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. (e:real^N) dot (((B:real->real^N^N) s ** matrix_inv((A:real->real^N^N) s)) ** e) +
         (k0 * (e dot e)) * s`;
    `\s. (--((e:real^N) dot ((R:real->real^N^N) s ** e)) -
          (((B:real->real^N^N) s ** matrix_inv((A:real->real^N^N) s)) ** e) dot
          ((B s ** matrix_inv(A s)) ** e)) + k0 * (e dot e)`;
    `t1:real`; `t:real`] REAL_MVT_VERY_SIMPLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPJ_QUAD_DERIV THEN EXISTS_TAC `L:real` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      MP_TAC(ISPECL [`\x:real. x`; `&1`; `k0 * ((e:real^N) dot e)`; `s:real`]
        HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_RID]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `k0 * ((e:real^N) dot e) <= e dot ((R:real->real^N^N) xi ** e)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `((B:real->real^N^N) xi ** matrix_inv((A:real->real^N^N) xi)) ** (e:real^N)`
    DOT_POS_LE) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= --((--((e:real^N) dot ((R:real->real^N^N) xi ** e)) -
              (((B:real->real^N^N) xi ** matrix_inv((A:real->real^N^N) xi)) ** e) dot
              ((B xi ** matrix_inv(A xi)) ** e)) + k0 * (e dot e)) * (t - t1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMPSH_RAY_HESS_UP = prove
 (`!(A:real->real^N^N) B R L k0 t1 (c:real^N) t.
        cmp_jsys A B R L /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> &0 <= v dot (R t ** v)) /\
        (!s v. t1 <= s /\ s <= t /\ v$1 = &0 ==> k0 * (v dot v) <= v dot (R s ** v)) /\
        (!t. &0 < t /\ t < L ==> invertible(A t)) /\ &0 < t1 /\ t1 <= t /\ t < L
        ==> ((B t ** c) dot (A t ** c)) / t pow 2 - c$1 pow 2 / t <=
            (inv t1 - k0 * (t - t1)) * (((A t ** c) dot (A t ** c)) / t pow 2 - c$1 pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `c:real^N` CMPP_SPLIT) THEN
  ABBREV_TAC `p:real^N = c - c$1 % basis 1` THEN
  ABBREV_TAC `a = (c:real^N)$1` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `a:real`; `p:real^N`; `t:real`] CMPP_GRAM_SPLIT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((a * t) pow 2 + ((A:real->real^N^N) t ** p) dot (A t ** (p:real^N))) / t pow 2 -
    a pow 2 = ((A t ** p) dot (A t ** p)) / t pow 2 /\
    (a pow 2 * t + ((B:real->real^N^N) t ** p) dot ((A:real->real^N^N) t ** (p:real^N))) /
    t pow 2 - a pow 2 / t = ((B t ** p) dot (A t ** p)) / t pow 2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `((B:real->real^N^N) t ** p) dot ((A:real->real^N^N) t ** (p:real^N)) =
    (A t ** p) dot ((B t ** matrix_inv(A t)) ** (A t ** p))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `matrix_inv((A:real->real^N^N) t) ** A t ** (p:real^N) = p`
    SUBST1_TAC THENL
     [REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `invertible((A:real->real^N^N) t)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
      MATCH_ACCEPT_TAC DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(((A:real->real^N^N) t ** (p:real^N))$1 = &0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `p:real^N`] CMPJ_NORMAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `e:real^N = (A:real->real^N^N) t ** p` THEN
  SUBGOAL_THEN
   `(e:real^N) dot (((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) ** e) <=
    (inv t1 - k0 * (t - t1)) * (e dot e)`
  MP_TAC THENL
   [MATCH_MP_TAC CMPSH_SHAPE_WINDOW THEN EXISTS_TAC `R:real->real^N^N` THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Y = (e:real^N) dot (((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) ** e)` THEN
  ABBREV_TAC `X = (e:real^N) dot e` THEN
  ABBREV_TAC `lmb = inv t1 - k0 * (t - t1)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `Y / t pow 2 = Y * inv(t pow 2) /\
                lmb * (X / t pow 2) = (lmb * X) * inv(t pow 2)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The ray data of the exp pullback (as CMPE_RAY_DATA_SEC0)                  *)
(* with, in addition, the curvature operator >= k0 on the normal space on   *)
(* [t1, t2] (t2 < rho) when sec >= k0 at the points of the ray at those     *)
(* times.                                                                    *)
(* ========================================================================= *)

let CMPSH_RAY_DATA = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) rho w k0 t1 t2.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 < rho /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g y u v) /\
        &0 <= t1 /\ t2 < rho /\
        (!r a c. t1 <= r /\ r <= t2 /\ ~collinear {vec 0,a,c}
                 ==> k0 <= mfd_sectional atlas g
                            (mfd_geo (top,atlas) g x (E ** (inv(norm w) % w)) r) a c) /\
        &0 < norm w
        ==> ?P A B R.
              orthogonal_matrix P /\ P ** basis 1 = inv(norm w) % w /\
              cmp_jsys A B R rho /\
              (!t v. &0 <= t /\ t < rho /\ v$1 = &0 ==> &0 <= v dot (R t ** v)) /\
              (!t v. t1 <= t /\ t <= t2 /\ v$1 = &0 ==> k0 * (v dot v) <= v dot (R t ** v)) /\
              (!s a. &0 < s /\ s < rho
                     ==> a dot (cmp_expmetric (top,atlas) g x E (s % inv(norm w) % w) ** a) =
                         ((A s ** (transp P ** a)) dot (A s ** (transp P ** a))) / s pow 2)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `u:real^N = inv(norm w) % w` THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(u:real^N) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `?P:real^N^N. orthogonal_matrix P /\ P ** basis 1 = u` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`basis 1:real^N`; `u:real^N`] ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(f:real^N->real^N)` THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ORTHOGONAL_TRANSFORMATION]) THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX];
    ALL_TAC] THEN
  EXISTS_TAC `P:real^N^N` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** u`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `P:real^N^N`; `u:real^N`]
    CMPP_FRAME_ALONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fr:num->real->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                 `Fr:num->real->real^N`] CMPP_JACOBI_ALONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:num->real->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`]
    CMPP_RADIAL) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(LABEL_TAC "rad") THEN
  EXISTS_TAC `cmp_fmat (\j. cmp_fcoord (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)
                ((Y:num->real->real^N) j))` THEN
  EXISTS_TAC `cmp_fmat (\j. cmp_fcoord (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)
                (mfd_covd atlas g (mfd_geo (top,atlas) g x (E ** u))
                   ((Y:num->real->real^N) j)))` THEN
  EXISTS_TAC `cmp_rmat atlas (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPJ_FRAME_JSYS THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`;
      `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "rad" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `v:real^N`] THEN STRIP_TAC THEN
    USE_THEN "rad" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                   `Fr:num->real->real^N`; `&0`] CMPJ_FRAME_SEC_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional" with Failure _ -> false))
          (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`t:real`; `v:real^N`]) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO]];
    MAP_EVERY X_GEN_TAC [`t:real`; `v:real^N`] THEN STRIP_TAC THEN
    USE_THEN "rad" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_CASES_TAC `v:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; DOT_RZERO; REAL_MUL_RZERO;
                      REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                   `Fr:num->real->real^N`; `v:real^N`; `t:real`] CMPJ_FRAME_SEC) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                              `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`] THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]];
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `k0:real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `a:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPP_RAY_IDENTITY THEN EXISTS_TAC `rho:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_EXP_DIFFERENTIAL_JACOBI_RAY THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
    USE_THEN "rad" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The strict upper bound of the Hessian of r = |w| at w0 in                 *)
(* the exp pullback at q: Hess_G r <= (1/t1 - k0 (|w0| - t1)) (G - dr dr)   *)
(* when sec >= 0, sec >= k0 along the ray at radii in [t1, |w0|], and       *)
(* d exp_q is injective along the segment from 0 to E w0.                   *)
(* ========================================================================= *)

let CMPSH_RAY_HESS_BOUND = prove
 (`!top atlas (g:A->real^N^N) (q:A) (E:real^N^N) t w0 k0 t1.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\
        mfd_orthonormal_frame g q E /\
        mfd_exp_dom (top,atlas) g q = (:real^N) /\
        (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g y u v) /\
        metric_field t (cmp_expmetric (top,atlas) g q E) /\ w0 IN t /\
        (!w. w IN t ==> ~(w = vec 0)) /\
        (!s h. &0 < s /\ s <= &1 /\
               mfd_differential (open_set_atlas (:real^N)) atlas
                 (mfd_exp (top,atlas) g q) (E ** (s % w0)) h = vec 0
               ==> h = vec 0) /\
        &0 < t1 /\ t1 <= norm w0 /\
        (!r a c. t1 <= r /\ r <= norm w0 /\ ~collinear {vec 0,a,c}
                 ==> k0 <= mfd_sectional atlas g
                            (mfd_geo (top,atlas) g q (E ** (inv(norm w0) % w0)) r) a c)
        ==> !a. cmp_lhess (cmp_expmetric (top,atlas) g q E) (\z. norm z) w0 a a <=
                (inv t1 - k0 * (norm w0 - t1)) *
                (a dot (cmp_expmetric (top,atlas) g q E w0 ** a) -
                 (w0 dot a) pow 2 / norm w0 pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `a:real^N` THEN
  SUBGOAL_THEN `~(w0:real^N = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w0:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `transp(E:real^N^N) ** (g:A->real^N^N) q` THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_orthonormal_frame]) THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN t ==> cmp_expmetric (top,atlas) (g:A->real^N^N) q E z ** z = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_EXPMETRIC_GAUSS THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `q:A`; `E:real^N^N`; `norm(w0:real^N) + &1`; `w0:real^N`;
                 `k0:real`; `t1:real`; `norm(w0:real^N)`]
    CMPSH_RAY_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`P:real^N^N`; `A:real->real^N^N`; `B:real->real^N^N`;
                       `R:real->real^N^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. &0 < s /\ s <= norm(w0:real^N) ==> invertible((A:real->real^N^N) s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPH_RAY_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `q:A`; `E:real^N^N`; `P:real^N^N`; `s:real`;
      `s % inv(norm(w0:real^N)) % w0`] THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN CONJ_TAC THENL
     [X_GEN_TAC `b:real^N` THEN
      UNDISCH_TAC
       `!s a. &0 < s /\ s < norm(w0:real^N) + &1
              ==> a dot (cmp_expmetric (top,atlas) (g:A->real^N^N) q E
                           (s % inv(norm w0) % w0) ** a) =
                  (((A:real->real^N^N) s ** (transp (P:real^N^N) ** a)) dot
                   (A s ** (transp P ** a))) / s pow 2` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `!s h. &0 < s /\ s <= &1 /\
            mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) (g:A->real^N^N) q) ((E:real^N^N) ** (s % w0)) h = vec 0
            ==> h = vec 0` THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `s * inv(norm(w0:real^N))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ];
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `norm(w0:real^N) + &1`; `norm(w0:real^N)`] CMPH_JSYS_INV_NEAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_REFL; REAL_ARITH `x < x + &1`]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `L' = norm(w0:real^N) + min eps (&1) / &2` THEN
  SUBGOAL_THEN `norm(w0:real^N) < L' /\ L' <= norm w0 + &1 /\ L' - norm w0 < eps`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "L'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 < s /\ s < L' ==> invertible((A:real->real^N^N) s)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s <= norm(w0:real^N)` THENL
     [ASM_SIMP_TAC[];
      UNDISCH_TAC `!s. abs(s - norm(w0:real^N)) < eps ==> invertible((A:real->real^N^N) s)` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_jsys (A:real->real^N^N) B R L'` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPH_JSYS_MONO THEN EXISTS_TAC `norm(w0:real^N) + &1` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `cmp_expmetric (top,atlas) (g:A->real^N^N) q E`;
                 `w0:real^N`; `P:real^N^N`; `A:real->real^N^N`; `B:real->real^N^N`;
                 `R:real->real^N^N`; `norm(w0:real^N) + &1`; `&1`; `a:real^N`]
    CMPE_LHESS_RAY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; REAL_ARITH `x < x + &1`] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `b:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!s a. &0 < s /\ s < norm(w0:real^N) + &1
            ==> a dot (cmp_expmetric (top,atlas) (g:A->real^N^N) q E
                         (s % inv(norm w0) % w0) ** a) =
                (((A:real->real^N^N) s ** (transp (P:real^N^N) ** a)) dot
                 (A s ** (transp P ** a))) / s pow 2` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  MATCH_MP_TAC CMPSH_RAY_HESS_UP THEN EXISTS_TAC `R:real->real^N^N` THEN
  EXISTS_TAC `L':real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `norm(w0:real^N) + &1`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_var t) = "R" with Failure _ -> false)) (concl th))) THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The generic form of CMPE_MDERIV_UP.  If Hess_G r at w is at               *)
(* most lm (G - dr dr) (in Gauss coordinates, G w w = w) then the radial     *)
(* derivative of G satisfies a.(D_w G) a <= 2 (|w| lm - 1) (|a|_G^2 -       *)
(* (w.a)^2/|w|^2), and along a geodesic of the pullback the second          *)
(* derivative of |beta|^2 / 2 is at most |V|_G^2 + (|w| lm - 1) (|V|_G^2 -   *)
(* (w.V)^2/|w|^2).  With lm = 1/|w| these are the bounds of pc_cmp_hup.     *)
(* ========================================================================= *)

let CMPSH_MDERIV_UP = prove
 (`!U (G:real^N->real^N^N) w a lm.
        metric_field U G /\ w IN U /\ (!z. z IN U ==> G z ** z = z) /\ ~(w = vec 0) /\
        cmp_lhess G (\z. norm z) w a a <=
        lm * (a dot (G w ** a) - (w dot a) pow 2 / norm w pow 2)
        ==> a dot (mderiv G w w ** a) <=
            &2 * (norm w * lm - &1) * (a dot (G w ** a) - (w dot a) pow 2 / norm w pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `cmp_lhess (G:real^N->real^N^N) (\z. norm z) w a a <=
               lm * (a dot (G w ** a) - (w dot a) pow 2 / norm w pow 2)` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`; `a:real^N`]
    CMPP_LHESS_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `n = norm(w:real^N)` THEN
  ABBREV_TAC `A = (a:real^N) dot ((G:real^N->real^N^N) w ** a)` THEN
  ABBREV_TAC `B = ((w:real^N) dot a) pow 2` THEN
  ABBREV_TAC `M = (a:real^N) dot (mderiv (G:real^N->real^N^N) w w ** a)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(&2 * n) * (A / n - B / n pow 3 + M / (&2 * n)) <=
                (&2 * n) * (lm * (A - B / n pow 2))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * n) * (A / n - B / n pow 3 + M / (&2 * n)) =
                &2 * A - &2 * (B / n pow 2) + M /\
                (&2 * n) * (lm * (A - B / n pow 2)) = &2 * (n * lm) * (A - B / n pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let CMPSH_PSI_BOUND = prove
 (`!U (G:real^N->real^N^N) y v lm.
        metric_field U G /\ y IN U /\ (!z. z IN U ==> G z ** z = z) /\ ~(y = vec 0) /\
        cmp_lhess G (\z. norm z) y v v <=
        lm * (v dot (G y ** v) - (y dot v) pow 2 / norm y pow 2)
        ==> v dot v - y dot christoffel G y v v <=
            v dot (G y ** v) +
            (norm y * lm - &1) * (v dot (G y ** v) - (y dot v) pow 2 / norm y pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`]
    CMPP_CHRISTOFFEL_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`;
                 `lm:real`] CMPSH_MDERIV_UP) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Calabi barrier in the exp pullback at b (generic form                 *)
(* of CMPE_BARRIER_PB).  If Hess_G r <= lm (G - dr dr) at w0 then the      *)
(* barrier bf of d(q, sigma s)^2 - s^2 (q at distance delta from b) has      *)
(* bf'' <= 2 ((delta/|w0|) C + ((|w0| + delta) lm - 1) (1 - C)) at t0,       *)
(* where C = (w0.V0)^2 / |w0|^2 is the squared cosine of the angle between  *)
(* sigma'(t0) and the radial direction.                                     *)
(* ========================================================================= *)

let CMPSH_BARRIER_PB = prove
 (`!top atlas (g:A->real^N^N) (b:A) (E:real^N^N) t w0 (sigma:real->A) t0 V0 (q:A) delta lm.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ b IN topspace top /\ mfd_orthonormal_frame g b E /\
        mfd_exp_dom (top,atlas) g b = (:real^N) /\ open t /\
        metric_field t (cmp_expmetric (top,atlas) g b E) /\ w0 IN t /\
        (!w. w IN t ==> ~(w = vec 0)) /\
        (!a. cmp_lhess (cmp_expmetric (top,atlas) g b E) (\z. norm z) w0 a a <=
             lm *
             (a dot (cmp_expmetric (top,atlas) g b E w0 ** a) -
              (w0 dot a) pow 2 / norm w0 pow 2)) /\
        (!s. mfd_geo (top,atlas) g (cmp_psi (top,atlas) g b E w0)
                     (cmp_dexp (top,atlas) g b E w0 ** V0) s = sigma(t0 + s)) /\
        V0 dot (cmp_expmetric (top,atlas) g b E w0 ** V0) = &1 /\
        mfd_joinable (top,atlas) q b /\ mfd_dist (top,atlas) g q b = delta /\ &0 < delta
        ==> ?e bf bf' bf2.
              &0 < e /\
              (!s. abs(s - t0) < e ==> (bf has_real_derivative bf'(s)) (atreal s)) /\
              (bf' has_real_derivative bf2) (atreal t0) /\
              bf2 <= &2 * ((delta / norm w0) * ((w0 dot V0) pow 2 / norm w0 pow 2) +
                           ((norm w0 + delta) * lm - &1) *
                           (&1 - (w0 dot V0) pow 2 / norm w0 pow 2)) /\
              bf t0 = (delta + norm w0) pow 2 - t0 pow 2 /\
              bf' t0 = &2 * (&1 + delta / norm w0) * (w0 dot V0) - &2 * t0 /\
              (!s. abs(s - t0) < e
                   ==> mfd_joinable (top,atlas) q (sigma s) /\
                       mfd_dist (top,atlas) g q (sigma s) pow 2 - s pow 2 <= bf s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `G = cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N)` THEN
  MP_TAC(ISPEC `t:real^N->bool` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas t) (G:real^N->real^N^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (t:real^N->bool)`; `open_set_atlas (t:real^N->bool)`;
                 `G:real^N->real^N^N`; `w0:real^N`; `V0:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (subtopology euclidean t,open_set_atlas t)
                    (G:real^N->real^N^N) w0 V0` THEN
  ABBREV_TAC `beta = mfd_geo (subtopology euclidean t,open_set_atlas t)
                       (G:real^N->real^N^N) w0 V0` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?e. &0 < e /\ !r. abs r < e ==> r IN M` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_open (M:real->bool)` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `&0`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO];
    ALL_TAC] THEN
  EXISTS_TAC `e:real` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`; `t:real^N->bool`; `w0:real^N`;
                 `V0:real^N`] CMPE_LIFT_GEO) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(LABEL_TAC "lift") THEN
  ABBREV_TAC `c = norm(w0:real^N)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[NORM_POS_LT] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `V = mfd_vel (open_set_atlas t) (beta:real->real^N)` THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `G:real^N->real^N^N`; `beta:real->real^N`;
                 `M:real->bool`] CMPE_GEO_DOT_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "dd") THEN
  SUBGOAL_THEN `!z. z IN t ==> (G:real^N->real^N^N) z ** z = z` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_EXPMETRIC_GAUSS THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `psi2 = (V0:real^N) dot V0 -
                     (w0:real^N) dot christoffel (G:real^N->real^N^N) w0 V0 V0` THEN
  SUBGOAL_THEN `psi2 <= &1 + (c * lm - &1) * (&1 - ((w0:real^N) dot V0) pow 2 / c pow 2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `cmp_lhess (G:real^N->real^N^N) (\z. norm z) w0 V0 V0 <=
                  lm * (&1 - ((w0:real^N) dot V0) pow 2 / c pow 2)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `V0:real^N` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "cmp_lhess"
                                 with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "psi2" THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `G:real^N->real^N^N`; `w0:real^N`; `V0:real^N`;
                   `lm:real`] CMPSH_PSI_BOUND) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\s. (delta pow 2 + delta * c) +
                  (&1 + delta / c) * ((beta:real->real^N)(s - t0) dot beta(s - t0)) -
                  s pow 2` THEN
  EXISTS_TAC `\s. (&1 + delta / c) *
                  (&2 * ((beta:real->real^N)(s - t0) dot (V:real->real^N)(s - t0))) -
                  &2 * s` THEN
  EXISTS_TAC `(&1 + delta / c) * (&2 * psi2) - &2` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC CMPE_BF_DERIV THEN
    MP_TAC(ISPECL [`\r. (beta:real->real^N) r dot beta r`;
                   `&2 * ((beta:real->real^N)(s - t0) dot (V:real->real^N)(s - t0))`;
                   `t0:real`; `s:real`] CMPE_SHIFT_DERIV) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "dd" (MP_TAC o SPEC `s - t0`) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[];
    MATCH_MP_TAC CMPE_BF1_DERIV THEN
    MP_TAC(ISPECL [`\r. (beta:real->real^N) r dot (V:real->real^N) r`; `psi2:real`;
                   `t0:real`; `t0:real`] CMPE_SHIFT_DERIV) THEN
    REWRITE_TAC[REAL_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "dd" (fun th -> MP_TAC(MATCH_MP (SPEC `&0` th) (ASSUME `&0 IN M`))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    SUBGOAL_THEN `&0 <= delta / c` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `psi2 <= &1 + (c * lm - &1) * (&1 - ((w0:real^N) dot V0) pow 2 / c pow 2)` THEN
    ABBREV_TAC `C = ((w0:real^N) dot V0) pow 2 / c pow 2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 * ((delta / c) * C + ((c + delta) * lm - &1) * (&1 - C)) =
                  (&1 + delta / c) * (&2 * (&1 + (c * lm - &1) * (&1 - C))) - &2`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - &2 <= y - &2`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_SUB_REFL] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(w0:real^N) dot w0 = c pow 2` SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_SUB_REFL] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(s - t0) IN M` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(sigma:real->A) s =
                mfd_exp (top,atlas) (g:A->real^N^N) b ((E:real^N^N) ** beta(s - t0))`
  ASSUME_TAC THENL
   [USE_THEN "lift" (fun th -> MP_TAC(MATCH_MP (SPEC `s - t0` th)
      (ASSUME `(s - t0) IN M`))) THEN
    REWRITE_TAC[cmp_psi] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `(E:real^N^N) ** (beta:real->real^N)(s - t0)`]
    CMPH_EXP_DIST_LE) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  ASM_SIMP_TAC[CMPP_TNORM_FRAME] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhand(concl th) = `(sigma:real->A) s`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (q:A) ((sigma:real->A) s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `b:A`; `(sigma:real->A) s`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `(sigma:real->A) s`] MFD_DIST_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= a + b ==> x - z <= a + b - z`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(delta + norm((beta:real->real^N)(s - t0))) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN MATCH_MP_TAC CMPE_AMGM THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The pullback data at the base point (as CMPE_PB_SETUP) with               *)
(* the strict Hessian bound, when sec >= k0 along geo(b,ub) on [t1, L'].    *)
(* ========================================================================= *)

let CMPSH_PB_SETUP = prove
 (`!top atlas (g:A->real^N^N) (b:A) ub L' (z:A) X k0 t1.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        b IN topspace top /\ mfd_tnorm g b ub = &1 /\ &0 < L' /\
        (!s h. &0 < s /\ s <= L' /\
               mfd_differential (open_set_atlas (:real^N)) atlas
                 (mfd_exp (top,atlas) g b) (s % ub) h = vec 0
               ==> h = vec 0) /\
        mfd_geo (top,atlas) g b ub L' = z /\
        &0 < t1 /\ t1 <= L' /\
        (!r a c. t1 <= r /\ r <= L' /\ ~collinear {vec 0,a,c}
                 ==> k0 <= mfd_sectional atlas g (mfd_geo (top,atlas) g b ub r) a c)
        ==> ?E t w0 V0.
              mfd_orthonormal_frame g b E /\ mfd_exp_dom (top,atlas) g b = (:real^N) /\
              open t /\ metric_field t (cmp_expmetric (top,atlas) g b E) /\ w0 IN t /\
              (!w. w IN t ==> ~(w = vec 0)) /\
              (!a. cmp_lhess (cmp_expmetric (top,atlas) g b E) (\z. norm z) w0 a a <=
                   (inv t1 - k0 * (norm w0 - t1)) *
                   (a dot (cmp_expmetric (top,atlas) g b E w0 ** a) -
                    (w0 dot a) pow 2 / norm w0 pow 2)) /\
              norm w0 = L' /\ cmp_psi (top,atlas) g b E w0 = z /\
              cmp_dexp (top,atlas) g b E w0 ** V0 = X /\
              V0 dot (cmp_expmetric (top,atlas) g b E w0 ** V0) = X dot (g z ** X) /\
              w0 dot V0 =
              L' * (mfd_vel atlas (mfd_geo (top,atlas) g b ub) L' dot (g z ** X))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `!v. mfd_geo_maxint (top,atlas) (g:A->real^N^N) b v = (:real)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) b = (:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_exp_dom; IN_UNIV; EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN EXISTS_TAC `E:real^N^N` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMPQ_FRAME_INVERTIBLE) THEN
  ABBREV_TAC `w0 = L' % (matrix_inv(E:real^N^N) ** (ub:real^N))` THEN
  SUBGOAL_THEN `(E:real^N^N) ** w0 = L' % ub` ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(w0:real^N) = L'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`] CMPP_TNORM_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) b ((E:real^N^N) ** w0) = z`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `ub:real^N`; `L':real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h. mfd_differential (open_set_atlas (:real^N)) atlas
                      (mfd_exp (top,atlas) (g:A->real^N^N) b) ((E:real^N^N) ** w0) h = vec 0
                    ==> h = vec 0`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `L':real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_differential"
                               with Failure _ -> false)) (concl th))) THEN
    EXISTS_TAC `L':real` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`;
                 `(:real^N) DELETE vec 0`; `z:A`] CMPH_EXP_CHART_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV] THEN SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
    REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `t:real^N->bool` THEN EXISTS_TAC `w0:real^N` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`;
                 `t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`; `&0`;
                 `w0:real^N`] CMPH_CHART_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV] THEN
    UNDISCH_TAC `t SUBSET (:real^N) DELETE vec 0` THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN SIMP_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `!w. w IN t ==> ~(w:real^N = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `t SUBSET (:real^N) DELETE vec 0` THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^N^N) ** (inv(norm(w0:real^N)) % w0) = ub` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. cmp_lhess (cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N)) (\z. norm z)
          w0 a a <=
        (inv t1 - k0 * (norm w0 - t1)) *
        (a dot (cmp_expmetric (top,atlas) g b E w0 ** a) - (w0 dot a) pow 2 / norm w0 pow 2)`
  (ASSUME_TAC o REWRITE_RULE[ASSUME `norm(w0:real^N) = L'`]) THENL
   [MATCH_MP_TAC CMPSH_RAY_HESS_BOUND THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `h:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `L':real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_differential"
                               with Failure _ -> false)) (concl th))) THEN
    EXISTS_TAC `s * L'` THEN
    UNDISCH_TAC `mfd_differential (open_set_atlas (:real^N)) atlas
                   (mfd_exp (top,atlas) (g:A->real^N^N) b) ((E:real^N^N) ** (s % w0)) h =
                 vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `s * L <= &1 * L ==> s * L <= L`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cmp_psi] THEN
  SUBGOAL_THEN `invertible(cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE_KER] THEN
    X_GEN_TAC `h:real^N` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`; `h:real^N`]
      CMPP_DEXP_APPLY) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(E:real^N^N) ** h = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        not(can (find_term ((=) `L':real`)) (concl th)) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_differential"
                                 with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. matrix_inv(E:real^N^N) ** v`) THEN
      SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; ASSUME `invertible(E:real^N^N)`;
               MATRIX_VECTOR_MUL_LID; MATRIX_VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  EXISTS_TAC `matrix_inv(cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0) ** X` THEN
  ABBREV_TAC `V0 = matrix_inv(cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0) ** X` THEN
  SUBGOAL_THEN `cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0 ** V0 = X`
  ASSUME_TAC THENL
   [EXPAND_TAC "V0" THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
             ASSUME `invertible(cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^N)) atlas
      (mfd_exp (top,atlas) (g:A->real^N^N) b) ((E:real^N^N) ** w0) (E ** V0) = X`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`; `V0:real^N`]
      CMPP_DEXP_APPLY) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`; `V0:real^N`;
                   `V0:real^N`] CMPP_EXPMETRIC_DOT) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w0:real^N) dot V0 =
    w0 dot (cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0 ** V0)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`] CMPP_EXPMETRIC_SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`] CMPP_EXPMETRIC_GAUSS) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN REPEAT DISCH_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM(ASSUME
      `transp(cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0) =
       cmp_expmetric (top,atlas) g b E w0`)] THEN
    REWRITE_TAC[CMPP_DOT_TRANSP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`; `w0:real^N`;
                 `V0:real^N`] CMPP_EXPMETRIC_DOT) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^N)) atlas
      (mfd_exp (top,atlas) (g:A->real^N^N) b) (L' % ub) (L' % ub) =
    L' % mfd_vel atlas (mfd_geo (top,atlas) g b ub) L'`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `\r:real. r % (L' % (ub:real^N))`;
                   `L' % (ub:real^N)`; `&1`] GEOG_DEXP_CURVE) THEN
    ASM_REWRITE_TAC[IN_UNIV; VECTOR_MUL_LID] THEN ANTS_TAC THENL
     [REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN
     `(\r. mfd_exp (top,atlas) (g:A->real^N^N) b (r % L' % ub)) =
      (\r. mfd_geo (top,atlas) g b ub (L' * r + &0))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; REAL_ADD_RID] THEN X_GEN_TAC `r:real` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `b:A`; `ub:real^N`; `r * L'`] MFD_EXP_RADIAL) THEN
      ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_MUL_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) b ub`; `(:real)`;
                   `L':real`; `&0`] MFD_GEODESIC_AFFINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `b:A`; `ub:real^N`] MFD_GEO_MAXIMAL) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `&1` o CONJUNCT2) THEN
    REWRITE_TAC[IN_UNIV; REAL_MUL_RID; REAL_ADD_RID] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LMUL]);;

(* ========================================================================= *)
(* The strict Calabi barrier on M (as CMPE_BARRIER).  If also                *)
(* sec >= k0 on the ball of radius ew around z = sigma(t0) and delta + ew < *)
(* L = d(z,q) = |w|, the barrier bf of d(q, sigma s)^2 - s^2 has             *)
(* bf''(t0) <= 2 ((delta/(L - delta)) C + (L (1/(L - delta - ew) - k0 ew)    *)
(* - 1) (1 - C)), C = <w, sigma'(t0)>^2 / L^2.  The base point b is at       *)
(* distance delta from q on the segment, and the window [L - delta - ew,    *)
(* L - delta] of geo(b, ub) lies in that ball.                               *)
(* ========================================================================= *)

let CMPSH_GEO_NEAR = prove
 (`!top atlas (g:A->real^N^N) (b:A) ub s r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        b IN topspace top /\ mfd_tnorm g b ub = &1
        ==> mfd_geo (top,atlas) g b ub r IN topspace top /\
            mfd_joinable (top,atlas) (mfd_geo (top,atlas) g b ub s)
                                     (mfd_geo (top,atlas) g b ub r) /\
            mfd_dist (top,atlas) g (mfd_geo (top,atlas) g b ub s)
                     (mfd_geo (top,atlas) g b ub r) <= abs(r - s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `ub:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let CMPSH_BARRIER = prove
 (`!top atlas (g:A->real^N^N) (p:A) u t0 (z:A) w (q:A) delta k0 ew.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p u = &1 /\
        mfd_geo (top,atlas) g p u t0 = z /\ mfd_exp (top,atlas) g z w = q /\
        mfd_dist (top,atlas) g z q = mfd_tnorm g z w /\
        &0 < delta /\ &0 < ew /\ delta + ew < mfd_tnorm g z w /\
        (!y a c. y IN topspace top /\ mfd_joinable (top,atlas) z y /\
                 mfd_dist (top,atlas) g z y <= ew /\ ~collinear {vec 0,a,c}
                 ==> k0 <= mfd_sectional atlas g y a c)
        ==> ?e bf bf' bf2.
              &0 < e /\
              (!s. abs(s - t0) < e ==> (bf has_real_derivative bf'(s)) (atreal s)) /\
              (bf' has_real_derivative bf2) (atreal t0) /\
              bf2 <= &2 * ((delta / (mfd_tnorm g z w - delta)) *
                           ((w dot (g z ** mfd_vel atlas (mfd_geo (top,atlas) g p u) t0)) pow 2 /
                            mfd_tnorm g z w pow 2) +
                           (mfd_tnorm g z w * (inv(mfd_tnorm g z w - delta - ew) - k0 * ew) - &1) *
                           (&1 - (w dot (g z ** mfd_vel atlas (mfd_geo (top,atlas) g p u) t0)) pow 2 /
                                 mfd_tnorm g z w pow 2)) /\
              bf t0 = mfd_tnorm g z w pow 2 - t0 pow 2 /\
              bf' t0 = --(&2 * (w dot (g z ** mfd_vel atlas (mfd_geo (top,atlas) g p u) t0))) -
                       &2 * t0 /\
              (!s. abs(s - t0) < e
                   ==> mfd_joinable (top,atlas) q (mfd_geo (top,atlas) g p u s) /\
                       mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u s) pow 2 - s pow 2
                       <= bf s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u = (:real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) p u` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `z:A`)) THEN
    MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `(:real)`] THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `L = mfd_tnorm (g:A->real^N^N) z w` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `w:real^N`] CMPE_REVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `zeta = mfd_geo (top,atlas) (g:A->real^N^N) z (inv L % w)` THEN
  ABBREV_TAC `uq = --(mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (zeta:real->A) L)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(zeta:real->A) (&0) = z` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`; `inv L % (w:real^N)`] MFD_GEO_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) q uq L = z` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) q (mfd_geo (top,atlas) g q uq L) = L`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `z:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `uq:real^N`; `L:real`; `delta:real`] CMPE_BASE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `b = mfd_geo (top,atlas) (g:A->real^N^N) q uq delta` THEN
  ABBREV_TAC `ub = mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                     (mfd_geo (top,atlas) (g:A->real^N^N) q uq) delta` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) b ub (L - delta) = z` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_ADD; REAL_SUB_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r a c. (L - delta) - ew <= r /\ r <= L - delta /\ ~collinear {vec 0,a,c}
            ==> k0 <= mfd_sectional atlas (g:A->real^N^N) (mfd_geo (top,atlas) g b ub r) a c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `ub:real^N`; `L - delta`; `r:real`]
      CMPSH_GEO_NEAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ew:real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `ub:real^N`; `L - delta`; `z:A`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (sigma:real->A) t0`;
                 `k0:real`; `(L - delta) - ew`]
    CMPSH_PB_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`E:real^N^N`; `t:real^N->bool`; `w0:real^N`; `V0:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (sigma:real->A) t0 dot
    ((g:A->real^N^N) z ** mfd_vel atlas sigma t0) = &1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC
      `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (sigma:real->A) t0` o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `t0:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`; `t:real^N->bool`; `w0:real^N`;
                 `sigma:real->A`; `t0:real`; `V0:real^N`; `q:A`; `delta:real`;
                 `inv((L - delta) - ew) - k0 * (norm(w0:real^N) - ((L - delta) - ew))`]
    CMPSH_BARRIER_PB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `u:real^N`; `t0:real`] MFD_GEO_SHIFT) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
      (mfd_geo (top,atlas) (g:A->real^N^N) b ub) (L - delta) = --(inv L % w)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) b ub =
                  (\s. mfd_geo (top,atlas) g q uq (&1 * s + delta))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_LID] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) q uq`; `(:real)`;
                   `&1`; `delta:real`] MFD_GEODESIC_AFFINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `q:A`; `uq:real^N`] MFD_GEO_MAXIMAL) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `L - delta` o CONJUNCT2) THEN
    REWRITE_TAC[IN_UNIV; REAL_MUL_LID; REAL_SUB_ADD; VECTOR_MUL_LID] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC
     `bf2 <= &2 * ((delta / norm(w0:real^N)) * ((w0 dot V0) pow 2 / norm w0 pow 2) +
                   ((norm w0 + delta) *
                    (inv((L - delta) - ew) - k0 * (norm w0 - ((L - delta) - ew))) - &1) *
                   (&1 - (w0 dot V0) pow 2 / norm w0 pow 2))` THEN
    ASM_REWRITE_TAC[DOT_LNEG; DOT_LMUL] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> b <= x ==> b <= y`) THEN
    SUBGOAL_THEN `~(L - delta = &0) /\ ~(L = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `L - delta - ew = (L - delta) - ew /\
                  (L - delta) - ((L - delta) - ew) = ew /\ (L - delta) + delta = L`
    (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    UNDISCH_TAC `(bf:real->real) t0 = (delta + norm(w0:real^N)) pow 2 - t0 pow 2` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ARITH `delta + (L - delta) = L`];
    UNDISCH_TAC `(bf':real->real) t0 =
                 &2 * (&1 + delta / norm(w0:real^N)) * (w0 dot V0) - &2 * t0` THEN
    ASM_REWRITE_TAC[DOT_LNEG; DOT_LMUL] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(L - delta = &0) /\ ~(L = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The strict barrier of the distance (as CMPB_DIST_BARRIER,                 *)
(* delta = L/2).  If sec >= k0 on the ew-ball around z = sigma(t0) and      *)
(* L = d(z,q) >= 4 ew, then d(q, sigma s) has a smooth upper barrier D near *)
(* t0, equal at t0, with |D'(t0)| <= 1 (D'(t0) is minus the cosine of the   *)
(* angle between sigma'(t0) and a minimizing direction to q) and            *)
(* D''(t0) <= 4/L - k0 ew (1 - D'(t0)^2).                                  *)
(* ========================================================================= *)

let CMPSH_DIST_BARRIER = prove
 (`!top atlas (g:A->real^N^N) (p:A) u t0 (q:A) k0 ew.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p u = &1 /\
        mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u t0) q /\
        &0 < ew /\ &4 * ew <= mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) q /\
        (!y a c. y IN topspace top /\
                 mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u t0) y /\
                 mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) y <= ew /\
                 ~collinear {vec 0,a,c}
                 ==> k0 <= mfd_sectional atlas g y a c)
        ==> ?d D D' D2.
              &0 < d /\
              (!s. abs(s - t0) < d ==> (D has_real_derivative D' s) (atreal s)) /\
              (D' has_real_derivative D2) (atreal t0) /\
              D2 <= &4 / mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) q -
                    k0 * ew * (&1 - D' t0 pow 2) /\
              abs(D' t0) <= &1 /\
              D t0 = mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) q /\
              (!s. abs(s - t0) < d
                   ==> mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u s) <= D s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u = (:real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_tnorm (g:A->real^N^N) (mfd_geo (top,atlas) g p u t0)
      (mfd_vel atlas (mfd_geo (top,atlas) g p u) t0) = &1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) p u`; `(:real)`;
                   `t0:real`; `&0`] MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p u t0 IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `(:real)`] THEN
    ASM_MESON_TAC[IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `z = mfd_geo (top,atlas) (g:A->real^N^N) p u t0` THEN
  ABBREV_TAC `vel = mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                      (mfd_geo (top,atlas) (g:A->real^N^N) p u) t0` THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^N^N) z q` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `q:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `abs((w:real^N) dot ((g:A->real^N^N) z ** vel)) <= L` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(g:A->real^N^N) z`; `w:real^N`; `vel:real^N`] GEOD_METRIC_CS) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC GEOG_G_SYM_POS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM mfd_tnorm] THEN ASM_REWRITE_TAC[REAL_MUL_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`; `t0:real`; `z:A`; `w:real^N`; `q:A`;
                 `L / &2`; `k0:real`; `ew:real`] CMPSH_BARRIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `bf:real->real`
    (X_CHOOSE_THEN `bf':real->real` (X_CHOOSE_THEN `bf2:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`bf:real->real`; `bf':real->real`; `bf2:real`; `t0:real`; `e:real`]
    CMPB_SQRT_BARRIER) THEN
  ASM_REWRITE_TAC[REAL_SUB_ADD] THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `D':real->real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `sqrt(L pow 2) = L` ASSUME_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `W = (w:real^N) dot ((g:A->real^N^N) z ** vel)` THEN
  SUBGOAL_THEN `(D':real->real) t0 = --(W / L)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(D':real->real) t0 pow 2 = W pow 2 / L pow 2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `abs((D':real->real) t0) <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `(D':real->real) t0 = --(W / L)`; REAL_ABS_NEG; REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < L ==> &0 < abs L`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= W pow 2 / L pow 2 /\ W pow 2 / L pow 2 <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_MUL_LID] THEN
      REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `C = W pow 2 / L pow 2` THEN
  SUBGOAL_THEN `inv(L - L / &2 - ew) <= &4 / L` ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 / L = inv(L / &4)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `I0 = inv(L - L / &2 - ew)` THEN
  SUBGOAL_THEN `D2 <= &2 * C / L + (I0 - k0 * ew) * (&1 - C)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(bf2 + &2) / (&2 * L)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `D2 <= (bf2 + &2) / (&2 * sqrt(L pow 2))` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * (&1 * C + (L * (I0 - k0 * ew) - &1) * (&1 - C)) + &2) / (&2 * L)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < L ==> &0 < &2 * L`] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= x ==> b + &2 <= x + &2`) THEN
      UNDISCH_TAC
       `bf2 <= &2 * ((L / &2 / (L - L / &2)) * C + (L * (I0 - k0 * ew) - &1) * (&1 - C))` THEN
      SUBGOAL_THEN `L / &2 / (L - L / &2) = &1` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; SIMP_TAC[]];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(I0 - k0 * ew) * (&1 - C) <= (&4 / L - k0 * ew) * (&1 - C)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C / L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`min d e`; `\s. sqrt((bf:real->real) s + s pow 2)`;
                        `D':real->real`; `D2:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN];
    X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ASSUME `(D':real->real) t0 pow 2 = C`] THEN
    SUBGOAL_THEN `&2 * C / L = &2 * (C / L) /\ &4 / L - k0 * ew * (&1 - C) =
                  &4 / L - (k0 * ew) * (&1 - C)` (fun th -> REWRITE_TAC[th] THEN
      UNDISCH_TAC `D2 <= &2 * C / L + (I0 - k0 * ew) * (&1 - C)` THEN REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&4 / L = &4 * inv L /\ C / L = C * inv L` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_div]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_SUB_ADD];
    X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th) &&
      can (find_term ((=) `bf:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `mfd_geo (top,atlas) (g:A->real^N^N) p u s`]
      MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC]);;

