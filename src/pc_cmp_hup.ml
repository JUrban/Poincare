(* ========================================================================= *)
(* Unit pc_cmp_hup (comparison-geometry layer CMP, the first of three units  *)
(* for MT Lemma 11.13, with pc_cmp_topo and pc_cmp_a7): the upper Hessian    *)
(* bound of distance functions under sec >= 0.  Along a ray of exp_b o E     *)
(* without conjugate points the Jacobi shape operator is at most 1/t         *)
(* (CMPJ_SHAPE_UPPER_GEN at k = 0), so in the exp pullback G the Hessian of  *)
(* r = |w| is at most (G - dr dr)/r, i.e. Hess_G(|w|^2/2) <= G; along a      *)
(* geodesic beta of the pullback, (beta.beta)'' <= 2 |beta'|_G^2.  These are *)
(* the inputs of the Calabi barriers for Toponogov's hinge comparison        *)
(* (pc_cmp_topo).                                                            *)
(* ========================================================================= *)

needs "src/pc_cmp_pmfd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The Jacobi-system form of the bound.  With R >= 0 on the                  *)
(* normal space and A invertible on (0,L): for 0 < t < L,                   *)
(* (B c.A c)/t^2 - c_1^2/t <= (1/t)(|A c|^2/t^2 - c_1^2).                    *)
(* ========================================================================= *)

let CMPE_RAY_HESS_UP = prove
 (`!(A:real->real^N^N) B R L (c:real^N) t.
        cmp_jsys A B R L /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> &0 <= v dot (R t ** v)) /\
        (!t. &0 < t /\ t < L ==> invertible(A t)) /\ &0 < t /\ t < L
        ==> ((B t ** c) dot (A t ** c)) / t pow 2 - c$1 pow 2 / t <=
            inv t * (((A t ** c) dot (A t ** c)) / t pow 2 - c$1 pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
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
  ABBREV_TAC `Y = (e:real^N) dot (((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) ** e)` THEN
  ABBREV_TAC `X = (e:real^N) dot e` THEN
  SUBGOAL_THEN `Y * t <= X` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `&0`; `e:real^N`] CMPJ_SHAPE_UPPER_GEN) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; CMP_SN_FLAT; CMP_CS_FLAT; REAL_MUL_LID] THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Y / t pow 2 = (Y * t) * inv(t pow 3) /\
                inv t * (X / t pow 2) = X * inv(t pow 3)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The ray data of the exp pullback (as CMPH_RAY_DATA_RIC) with              *)
(* the curvature operator nonnegative on the normal space when sec >= 0.    *)
(* ========================================================================= *)

let CMPE_RAY_DATA_SEC0 = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) rho w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 < rho /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g y u v) /\
        &0 < norm w
        ==> ?P A B R.
              orthogonal_matrix P /\ P ** basis 1 = inv(norm w) % w /\
              cmp_jsys A B R rho /\
              (!t v. &0 <= t /\ t < rho /\ v$1 = &0 ==> &0 <= v dot (R t ** v)) /\
              (!s a. &0 < s /\ s < rho
                     ==> a dot (cmp_expmetric (top,atlas) g x E (s % inv(norm w) % w) ** a) =
                         ((A s ** (transp P ** a)) dot (A s ** (transp P ** a))) / s pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u:real^N = inv(norm w) % w` THEN
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
    MAP_EVERY X_GEN_TAC [`s:real`; `a:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPP_RAY_IDENTITY THEN EXISTS_TAC `rho:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_EXP_DIFFERENTIAL_JACOBI_RAY THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
    USE_THEN "rad" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The Hessian of r = |w| along the ray through w in the                     *)
(* Jacobi data (CMPP_LHESS_NORM with CMPH_RAY_MDERIV), and the upper bound   *)
(* Hess_G r <= (G - dr dr)/r at w0 in the exp pullback at q when sec >= 0    *)
(* and d exp_q is injective along the segment from 0 to E w0.                *)
(* ========================================================================= *)

let CMPE_LHESS_RAY = prove
 (`!U (G:real^N->real^N^N) w (P:real^N^N) (A:real->real^N^N) B R L eta a.
        metric_field U G /\ w IN U /\ (!z. z IN U ==> G z ** z = z) /\
        &0 < norm w /\ norm w < L /\ &0 < eta /\
        orthogonal_matrix P /\ P ** basis 1 = inv(norm w) % w /\ cmp_jsys A B R L /\
        (!s a. abs(s - norm w) < eta /\ &0 < s
               ==> a dot (G(s % inv(norm w) % w) ** a) =
                   ((A s ** (transp P ** a)) dot (A s ** (transp P ** a))) / s pow 2)
        ==> cmp_lhess G (\z. norm z) w a a =
            ((B(norm w) ** (transp P ** a)) dot (A(norm w) ** (transp P ** a))) /
            norm w pow 2 - (transp P ** a)$1 pow 2 / norm w /\
            a dot (G w ** a) =
            ((A(norm w) ** (transp P ** a)) dot (A(norm w) ** (transp P ** a))) /
            norm w pow 2 /\
            (w dot a) pow 2 / norm w pow 2 = (transp P ** a)$1 pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(w:real^N = vec 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^N) % inv(norm w) % w = w` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(a:real^N) dot ((G:real^N->real^N^N) w ** a) =
    (((A:real->real^N^N)(norm w) ** (transp (P:real^N^N) ** a)) dot
     (A(norm w) ** (transp P ** a))) / norm w pow 2`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`norm(w:real^N)`; `a:real^N`]) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(transp (P:real^N^N) ** (a:real^N))$1 = (w dot a) / norm(w:real^N)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(transp (P:real^N^N) ** (a:real^N))$1 = basis 1 dot (transp P ** a)`
    SUBST1_TAC THENL [SIMP_TAC[DOT_BASIS; DIMINDEX_GE_1; LE_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[CMPP_DOT_TRANSP; DOT_LMUL] THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`; `P:real^N^N`;
                 `A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`; `L:real`;
                 `eta:real`; `a:real^N`] CMPH_RAY_MDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`; `a:real^N`]
    CMPP_LHESS_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `r = norm(w:real^N)` THEN
  ABBREV_TAC `X = ((A:real->real^N^N) r ** (transp (P:real^N^N) ** (a:real^N))) dot
                  (A r ** (transp P ** a))` THEN
  ABBREV_TAC `Y = ((B:real->real^N^N) r ** (transp (P:real^N^N) ** (a:real^N))) dot
                  ((A:real->real^N^N) r ** (transp P ** a))` THEN
  ABBREV_TAC `d = (w:real^N) dot a` THEN
  CONV_TAC REAL_FIELD);;

let CMPE_RAY_HESS_BOUND = prove
 (`!top atlas (g:A->real^N^N) (q:A) (E:real^N^N) t w0.
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
               ==> h = vec 0)
        ==> !a. cmp_lhess (cmp_expmetric (top,atlas) g q E) (\z. norm z) w0 a a <=
                inv(norm w0) *
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
                 `q:A`; `E:real^N^N`; `norm(w0:real^N) + &1`; `w0:real^N`]
    CMPE_RAY_DATA_SEC0) THEN
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
  MATCH_MP_TAC CMPE_RAY_HESS_UP THEN EXISTS_TAC `R:real->real^N^N` THEN
  EXISTS_TAC `L':real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `norm(w0:real^N) + &1`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_var t) = "R" with Failure _ -> false)) (concl th))) THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Along a geodesic beta of the pullback U, at a time where                  *)
(* the Hessian upper bound holds at beta(t), (beta.beta)' = 2 beta.V and     *)
(* (beta.V)' = V.V - beta.Gamma(V,V) <= |V|_G^2, i.e. (beta.beta)'' <=      *)
(* 2 |beta'|_G^2 (the radial derivative of G is nonpositive).                *)
(* ========================================================================= *)

let CMPE_MDERIV_UP = prove
 (`!U (G:real^N->real^N^N) w a.
        metric_field U G /\ w IN U /\ (!z. z IN U ==> G z ** z = z) /\
        (~(w = vec 0)
         ==> cmp_lhess G (\z. norm z) w a a <=
             inv(norm w) * (a dot (G w ** a) - (w dot a) pow 2 / norm w pow 2))
        ==> a dot (mderiv G w w ** a) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN
     `linear (\v. lift((a:real^N) dot (mderiv (G:real^N->real^N^N) (vec 0) v ** a)))`
    MP_TAC THENL
     [MATCH_MP_TAC LRG_MDERIV_DOT_LINEAR THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `vec 0:real^N`]
        LRG_METRIC_FIELD_DIFF) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN
      REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`; `a:real^N`]
    CMPP_LHESS_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN
  ABBREV_TAC `n = norm(w:real^N)` THEN
  ABBREV_TAC `A = (a:real^N) dot ((G:real^N->real^N^N) w ** a)` THEN
  ABBREV_TAC `B = ((w:real^N) dot a) pow 2` THEN
  ABBREV_TAC `M = (a:real^N) dot (mderiv (G:real^N->real^N^N) w w ** a)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(&2 * n) * (A / n - B / n pow 3 + M / (&2 * n)) <=
                (&2 * n) * (inv n * (A - B / n pow 2))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * n) * (A / n - B / n pow 3 + M / (&2 * n)) =
                &2 * A - &2 * B / n pow 2 + M /\
                (&2 * n) * (inv n * (A - B / n pow 2)) = &2 * A - &2 * B / n pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let CMPE_GEO_DOT_DERIV = prove
 (`!U (G:real^N->real^N^N) (beta:real->real^N) J t.
        open U /\ metric_field U G /\
        mfd_geodesic (subtopology euclidean U,open_set_atlas U) G beta J /\ t IN J
        ==> ((\s. beta s dot beta s) has_real_derivative
             (&2 * (beta t dot mfd_vel (open_set_atlas U) beta t))) (atreal t) /\
            ((\s. beta s dot mfd_vel (open_set_atlas U) beta s) has_real_derivative
             (mfd_vel (open_set_atlas U) beta t dot mfd_vel (open_set_atlas U) beta t -
              beta t dot christoffel G (beta t) (mfd_vel (open_set_atlas U) beta t)
                                                (mfd_vel (open_set_atlas U) beta t)))
            (atreal t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `beta:real->real^N`; `J:real->bool`]
    CMPW_GEO_ODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V = mfd_vel (open_set_atlas U) (beta:real->real^N)` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`beta:real->real^N`; `beta:real->real^N`; `(V:real->real^N) t`;
                   `(V:real->real^N) t`; `t:real`] CMPW_DOT_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`beta:real->real^N`; `V:real->real^N`; `(V:real->real^N) t`;
                   `--(christoffel (G:real^N->real^N^N) ((beta:real->real^N) t)
                                   ((V:real->real^N) t) (V t))`; `t:real`]
      CMPW_DOT_DERIV) THEN
    ASM_REWRITE_TAC[DOT_RNEG] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

let CMPE_CONCAVE_DERIV = prove
 (`!U (G:real^N->real^N^N) (beta:real->real^N) J t.
        open U /\ metric_field U G /\ (!z. z IN U ==> G z ** z = z) /\
        mfd_geodesic (subtopology euclidean U,open_set_atlas U) G beta J /\ t IN J /\
        (!a. ~(beta t = vec 0)
             ==> cmp_lhess G (\z. norm z) (beta t) a a <=
                 inv(norm(beta t)) *
                 (a dot (G(beta t) ** a) - (beta t dot a) pow 2 / norm(beta t) pow 2))
        ==> ((\s. beta s dot beta s) has_real_derivative
             (&2 * (beta t dot mfd_vel (open_set_atlas U) beta t))) (atreal t) /\
            ((\s. beta s dot mfd_vel (open_set_atlas U) beta s) has_real_derivative
             (mfd_vel (open_set_atlas U) beta t dot mfd_vel (open_set_atlas U) beta t -
              beta t dot christoffel G (beta t) (mfd_vel (open_set_atlas U) beta t)
                                                (mfd_vel (open_set_atlas U) beta t)))
            (atreal t) /\
            mfd_vel (open_set_atlas U) beta t dot mfd_vel (open_set_atlas U) beta t -
            beta t dot christoffel G (beta t) (mfd_vel (open_set_atlas U) beta t)
                                              (mfd_vel (open_set_atlas U) beta t) <=
            mfd_vel (open_set_atlas U) beta t dot
            (G(beta t) ** mfd_vel (open_set_atlas U) beta t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `beta:real->real^N`; `J:real->bool`]
    CMPW_GEO_ODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V = mfd_vel (open_set_atlas U) (beta:real->real^N)` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`beta:real->real^N`; `beta:real->real^N`; `(V:real->real^N) t`;
                   `(V:real->real^N) t`; `t:real`] CMPW_DOT_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`beta:real->real^N`; `V:real->real^N`; `(V:real->real^N) t`;
                   `--(christoffel (G:real^N->real^N^N) ((beta:real->real^N) t)
                                   ((V:real->real^N) t) (V t))`; `t:real`]
      CMPW_DOT_DERIV) THEN
    ASM_REWRITE_TAC[DOT_RNEG] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(beta:real->real^N) t`;
                 `(V:real->real^N) t`] CMPP_CHRISTOFFEL_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(beta:real->real^N) t`;
                 `(V:real->real^N) t`] CMPE_MDERIV_UP) THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Lifting geodesics.  On an open t where the exp pullback G at              *)
(* b is a metric field, the geodesic of (t,G) from w0 with velocity V0 is    *)
(* mapped by Psi = exp_b o E onto the geodesic of M from Psi(w0) with        *)
(* velocity dPsi(V0) (local isometry and uniqueness of geodesics).           *)
(* ========================================================================= *)

let CMPE_LIFT_GEO = prove
 (`!top atlas (g:A->real^N^N) (b:A) (E:real^N^N) t w0 V0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ b IN topspace top /\ open t /\
        (!w. w IN t ==> E ** w IN mfd_exp_dom (top,atlas) g b) /\
        metric_field t (cmp_expmetric (top,atlas) g b E) /\ w0 IN t
        ==> !s. s IN mfd_geo_maxint (subtopology euclidean t,open_set_atlas t)
                       (cmp_expmetric (top,atlas) g b E) w0 V0
                ==> cmp_psi (top,atlas) g b E
                      (mfd_geo (subtopology euclidean t,open_set_atlas t)
                               (cmp_expmetric (top,atlas) g b E) w0 V0 s) =
                    mfd_geo (top,atlas) g (cmp_psi (top,atlas) g b E w0)
                            (cmp_dexp (top,atlas) g b E w0 ** V0) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^N->bool` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas t)
                  (cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (t:real^N->bool)`; `open_set_atlas (t:real^N->bool)`;
                 `cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N)`;
                 `w0:real^N`; `V0:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (subtopology euclidean t,open_set_atlas t)
                    (cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N)) w0 V0` THEN
  ABBREV_TAC `beta = mfd_geo (subtopology euclidean t,open_set_atlas t)
                    (cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N)) w0 V0` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`; `t:real^N->bool`] CMPW_PSI_LISOM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (t:real^N->bool)`; `open_set_atlas (t:real^N->bool)`;
                 `cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `t:real^N->bool`; `cmp_psi (top,atlas) (g:A->real^N^N) b (E:real^N^N)`;
                 `beta:real->real^N`; `M:real->bool`] MFD_LOCAL_ISOMETRY_GEODESIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (t:real^N->bool)`;
                   `open_set_atlas (t:real^N->bool)`;
                   `cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N)`;
                   `beta:real->real^N`; `M:real->bool`; `s:real`]
      GEOL_GEODESIC_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `cmp_psi (top,atlas) (g:A->real^N^N) b (E:real^N^N) o (beta:real->real^N)`;
                 `M:real->bool`; `cmp_psi (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0`;
                 `cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0 ** V0`]
    MFD_GEO_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_differential"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `t:real^N->bool`; `w0:real^N`]
      CMPW_PSI_DIFF) THEN
    ASM_SIMP_TAC[];
    SIMP_TAC[o_THM]]);;

(* ========================================================================= *)
(* Reversing a geodesic segment.  For w <> 0 at z (M complete)               *)
(* and zeta the unit-speed geodesic from z in the direction of w, with      *)
(* L = |w|_g and q = exp_z(w) = zeta(L): the geodesic from q with velocity  *)
(* uq = -zeta'(L) is s |-> zeta(L - s); it has unit speed, reaches z at     *)
(* time L with velocity -w/L.                                                *)
(* ========================================================================= *)

let CMPE_REVERSE = prove
 (`!top atlas (g:A->real^N^N) (z:A) w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ z IN topspace top /\
        &0 < mfd_tnorm g z w
        ==> mfd_exp (top,atlas) g z w =
            mfd_geo (top,atlas) g z (inv(mfd_tnorm g z w) % w) (mfd_tnorm g z w) /\
            mfd_exp (top,atlas) g z w IN topspace top /\
            mfd_tnorm g (mfd_exp (top,atlas) g z w)
              (--(mfd_vel atlas (mfd_geo (top,atlas) g z (inv(mfd_tnorm g z w) % w))
                              (mfd_tnorm g z w))) = &1 /\
            (!s. mfd_geo (top,atlas) g (mfd_exp (top,atlas) g z w)
                   (--(mfd_vel atlas (mfd_geo (top,atlas) g z (inv(mfd_tnorm g z w) % w))
                                   (mfd_tnorm g z w))) s =
                 mfd_geo (top,atlas) g z (inv(mfd_tnorm g z w) % w) (mfd_tnorm g z w - s)) /\
            mfd_vel atlas
              (mfd_geo (top,atlas) g (mfd_exp (top,atlas) g z w)
                 (--(mfd_vel atlas (mfd_geo (top,atlas) g z (inv(mfd_tnorm g z w) % w))
                                 (mfd_tnorm g z w))))
              (mfd_tnorm g z w) =
            --(inv(mfd_tnorm g z w) % w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  ABBREV_TAC `L = mfd_tnorm (g:A->real^N^N) z w` THEN
  ABBREV_TAC `w' = inv L % (w:real^N)` THEN
  SUBGOAL_THEN `L % (w':real^N) = w` ASSUME_TAC THENL
   [EXPAND_TAC "w'" THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) z w' = &1` ASSUME_TAC THENL
   [EXPAND_TAC "w'" THEN ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < L ==> abs L = L`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ABBREV_TAC `zeta = mfd_geo (top,atlas) (g:A->real^N^N) z w'` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `w':real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) z w = (zeta:real->A) L` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`; `w':real^N`; `L:real`] MFD_EXP_RADIAL) THEN
    ASM_SIMP_TAC[IN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s. (zeta:real->A) s IN topspace top` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `(:real)`] THEN
    ASM_MESON_TAC[IN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `v = mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (zeta:real->A) L` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `w':real^N`; `L:real`] MFD_GEO_SHIFT) THEN
  ASM_SIMP_TAC[IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(zeta:real->A) L`; `v:real^N`; `--(&1)`]
    MFD_GEO_RESCALE) THEN
  ASM_SIMP_TAC[IN_UNIV] THEN
  REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID; REAL_MUL_LNEG; REAL_MUL_LID] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!s. mfd_geo (top,atlas) (g:A->real^N^N) ((zeta:real->A) L) (--v) s =
                    zeta(L - s)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `--(v:real^N)`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(zeta:real->A) L`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `--(v:real^N) = --(&1) % v`] THEN
    ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_1; REAL_MUL_LID] THEN
    EXPAND_TAC "v" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `zeta:real->A`; `(:real)`; `L:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_SIMP_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) ((zeta:real->A) L) (--v) =
                (\s. zeta(--(&1) * s + L))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `zeta:real->A`; `(:real)`; `--(&1)`; `L:real`]
    MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(MP_TAC o SPEC `L:real` o CONJUNCT2) THEN
  REWRITE_TAC[REAL_ARITH `--(&1) * L + L = &0`] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* The shifted base point of the Calabi barrier.  On a unit-                 *)
(* speed geodesic from q minimizing up to time L (M complete), the point    *)
(* b = geo(delta), 0 < delta < L, is at distance delta from q, the geodesic  *)
(* from b with the shifted velocity is the shifted geodesic, and d exp_b is  *)
(* injective along it up to time L - delta (CMPN_NO_CONJ).                   *)
(* ========================================================================= *)

let CMPE_BASE = prove
 (`!top atlas (g:A->real^N^N) (q:A) uq L delta.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        q IN topspace top /\ mfd_tnorm g q uq = &1 /\
        mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g q uq L) = L /\
        &0 < delta /\ delta < L
        ==> mfd_geo (top,atlas) g q uq delta IN topspace top /\
            mfd_joinable (top,atlas) q (mfd_geo (top,atlas) g q uq delta) /\
            mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g q uq delta) = delta /\
            mfd_tnorm g (mfd_geo (top,atlas) g q uq delta)
              (mfd_vel atlas (mfd_geo (top,atlas) g q uq) delta) = &1 /\
            (!t. mfd_geo (top,atlas) g (mfd_geo (top,atlas) g q uq delta)
                   (mfd_vel atlas (mfd_geo (top,atlas) g q uq) delta) t =
                 mfd_geo (top,atlas) g q uq (t + delta)) /\
            (!s h. &0 < s /\ s <= L - delta /\
                   mfd_differential (open_set_atlas (:real^N)) atlas
                     (mfd_exp (top,atlas) g (mfd_geo (top,atlas) g q uq delta))
                     (s % mfd_vel atlas (mfd_geo (top,atlas) g q uq) delta) h = vec 0
                   ==> h = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) q uq = (:real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `uq:real^N`; `delta:real`] CMPN_SHIFT_SETUP) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `uq:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) q uq` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `(:real)`; `&0`; `delta:real`]
    GEOH_GEO_SEG_DIST) THEN
  ASM_REWRITE_TAC[IN_UNIV; REAL_SUB_RZERO; REAL_MUL_RID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `(:real)`; `delta:real`; `L:real`]
    GEOH_GEO_SEG_DIST) THEN
  ASM_REWRITE_TAC[IN_UNIV; REAL_MUL_RID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `(gam:real->A) delta`; `(gam:real->A) L`]
    MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (q:A) ((gam:real->A) delta)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPN_NO_CONJ THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `q:A`; `uq:real^N`; `L:real`; `delta:real`; `s:real`] THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Calabi barrier in the pullback.  Let G be the exp                     *)
(* pullback at b on an open t (a metric field, 0 not in t), w0 in t with     *)
(* the Hessian upper bound, beta the pullback geodesic from w0 with          *)
(* |V0|_G = 1 whose image under Psi is sigma(t0 + .), and d(q,b) = delta.    *)
(* With c = |w0|: d(q,sigma(s)) <= delta + |beta(s - t0)| and AM-GM give the *)
(* smooth upper barrier                                                      *)
(*   bf(s) = delta^2 + delta c + (1 + delta/c) |beta(s - t0)|^2 - s^2       *)
(* of d(q,sigma(s))^2 - s^2 near t0, equal at t0, with                      *)
(* bf''(t0) <= 2 delta / c and bf'(t0) = 2 (1 + delta/c) (w0.V0) - 2 t0.     *)
(* ========================================================================= *)

let CMPE_AMGM = prove
 (`!d c x. &0 <= d /\ &0 < c /\ &0 <= x
           ==> (d + x) pow 2 <= (d pow 2 + d * c) + (&1 + d / c) * x pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(d pow 2 + d * c) + (&1 + d / c) * x pow 2 =
                (d + x) pow 2 + d / c * (x - c) pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;

let CMPE_SHIFT_DERIV = prove
 (`!f f' t0 x. (f has_real_derivative f') (atreal (x - t0))
               ==> ((\s. f(s - t0)) has_real_derivative f') (atreal x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s:real. s - t0`; `f:real->real`; `&1`; `f':real`; `x:real`]
    REAL_DIFF_CHAIN_ATREAL) THEN
  REWRITE_TAC[o_DEF; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV) [GSYM REAL_SUB_RZERO] THEN
  REAL_DIFF_TAC THEN REAL_ARITH_TAC);;

let CMPE_BF_DERIV = prove
 (`!(Fn:real->real) Fd a k x. (Fn has_real_derivative Fd) (atreal x)
       ==> ((\s. a + k * Fn s - s pow 2) has_real_derivative (k * Fd - &2 * x)) (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\s. s pow 2) has_real_derivative (&2 * x)) (atreal x)` ASSUME_TAC THENL
   [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((\s. k * Fn s) has_real_derivative (k * Fd)) (atreal x)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real. a:real`; `&0`; `\s:real. k * Fn s`; `k * Fd`; `atreal x`]
    HAS_REAL_DERIVATIVE_ADD) THEN
  ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_ADD_LID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\s:real. a + k * Fn s`; `k * Fd`; `\s:real. s pow 2`; `&2 * x`; `atreal x`]
    HAS_REAL_DERIVATIVE_SUB) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ARITH `a + b - c = (a + b) - c`]);;

let CMPE_BF1_DERIV = prove
 (`!P P' k x. (P has_real_derivative P') (atreal x)
       ==> ((\s. k * (&2 * P s) - &2 * s) has_real_derivative (k * (&2 * P') - &2)) (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\s. &2 * s) has_real_derivative &2) (atreal x)` ASSUME_TAC THENL
   [REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((\s. k * (&2 * P s)) has_real_derivative (k * (&2 * P'))) (atreal x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real. k * (&2 * P s)`; `k * (&2 * P')`; `\s:real. &2 * s`; `&2`;
                 `atreal x`] HAS_REAL_DERIVATIVE_SUB) THEN
  ASM_REWRITE_TAC[]);;

let CMPE_BARRIER_PB = prove
 (`!top atlas (g:A->real^N^N) (b:A) (E:real^N^N) t w0 (sigma:real->A) t0 V0 (q:A) delta.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ b IN topspace top /\ mfd_orthonormal_frame g b E /\
        mfd_exp_dom (top,atlas) g b = (:real^N) /\ open t /\
        metric_field t (cmp_expmetric (top,atlas) g b E) /\ w0 IN t /\
        (!w. w IN t ==> ~(w = vec 0)) /\
        (!a. cmp_lhess (cmp_expmetric (top,atlas) g b E) (\z. norm z) w0 a a <=
             inv(norm w0) *
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
              bf2 <= &2 * delta / norm w0 /\
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
  SUBGOAL_THEN `psi2 <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^N->bool`; `G:real^N->real^N^N`; `beta:real->real^N`;
                   `M:real->bool`; `&0`] CMPE_CONCAVE_DERIV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
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
    SUBGOAL_THEN `&0 <= delta / c` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * delta / c = (&1 + delta / c) * (&2 * &1) - &2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - &2 <= y - &2`) THEN
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
(* The pullback data at the base point.  For a unit vector ub                *)
(* at b with d exp_b injective at s ub, 0 < s <= L', and z = geo(b,ub)(L'): *)
(* an orthonormal frame E at b, an open t around w0 = L' E^-1 ub where the   *)
(* pullback G is a metric field (0 not in t), the Hessian upper bound at w0  *)
(* (sec >= 0), Psi(w0) = z, and for X at z the vector V0 = dPsi^-1 X with    *)
(* |V0|_G = |X|_g and w0.V0 = L' <geo'(L'), X>_g.                           *)
(* ========================================================================= *)

let CMPE_PB_SETUP = prove
 (`!top atlas (g:A->real^N^N) (b:A) ub L' (z:A) X.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        b IN topspace top /\ mfd_tnorm g b ub = &1 /\ &0 < L' /\
        (!s h. &0 < s /\ s <= L' /\
               mfd_differential (open_set_atlas (:real^N)) atlas
                 (mfd_exp (top,atlas) g b) (s % ub) h = vec 0
               ==> h = vec 0) /\
        mfd_geo (top,atlas) g b ub L' = z
        ==> ?E t w0 V0.
              mfd_orthonormal_frame g b E /\ mfd_exp_dom (top,atlas) g b = (:real^N) /\
              open t /\ metric_field t (cmp_expmetric (top,atlas) g b E) /\ w0 IN t /\
              (!w. w IN t ==> ~(w = vec 0)) /\
              (!a. cmp_lhess (cmp_expmetric (top,atlas) g b E) (\z. norm z) w0 a a <=
                   inv(norm w0) *
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
  SUBGOAL_THEN
   `!a. cmp_lhess (cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N)) (\z. norm z)
          w0 a a <=
        inv(norm w0) *
        (a dot (cmp_expmetric (top,atlas) g b E w0 ** a) - (w0 dot a) pow 2 / norm w0 pow 2)`
  (ASSUME_TAC o REWRITE_RULE[ASSUME `norm(w0:real^N) = L'`]) THENL
   [MATCH_MP_TAC CMPE_RAY_HESS_BOUND THEN EXISTS_TAC `t:real^N->bool` THEN
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
(* The Calabi barrier on M (sec >= 0, M complete).  For a                    *)
(* unit-speed geodesic sigma = geo(p,u), a point z = sigma(t0) and w at z    *)
(* with q = exp_z(w), d(z,q) = |w|_g = L, and 0 < delta < L: a smooth upper  *)
(* barrier bf of d(q,sigma s)^2 - s^2 near t0, equal at t0, with             *)
(* bf''(t0) <= 2 delta / (L - delta) and bf'(t0) = -2 <w, sigma'(t0)> - 2 t0.*)
(* The base point is b = geo(q,uq)(delta) on the reversed segment from q to  *)
(* z (CMPE_REVERSE, CMPE_BASE), the pullback at b (CMPE_PB_SETUP), and      *)
(* CMPE_BARRIER_PB.                                                          *)
(* ========================================================================= *)

let CMPE_BARRIER = prove
 (`!top atlas (g:A->real^N^N) (p:A) u t0 (z:A) w (q:A) delta.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p u = &1 /\
        mfd_geo (top,atlas) g p u t0 = z /\ mfd_exp (top,atlas) g z w = q /\
        mfd_dist (top,atlas) g z q = mfd_tnorm g z w /\
        &0 < delta /\ delta < mfd_tnorm g z w
        ==> ?e bf bf' bf2.
              &0 < e /\
              (!s. abs(s - t0) < e ==> (bf has_real_derivative bf'(s)) (atreal s)) /\
              (bf' has_real_derivative bf2) (atreal t0) /\
              bf2 <= &2 * delta / (mfd_tnorm g z w - delta) /\
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
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `b = mfd_geo (top,atlas) (g:A->real^N^N) q uq delta` THEN
  ABBREV_TAC `ub = mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                     (mfd_geo (top,atlas) (g:A->real^N^N) q uq) delta` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) b ub (L - delta) = z` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_ADD; REAL_SUB_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `ub:real^N`; `L - delta`; `z:A`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (sigma:real->A) t0`]
    CMPE_PB_SETUP) THEN
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
                 `sigma:real->A`; `t0:real`; `V0:real^N`; `q:A`; `delta:real`]
    CMPE_BARRIER_PB) THEN
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
    UNDISCH_TAC `bf2 <= &2 * delta / norm(w0:real^N)` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(bf:real->real) t0 = (delta + norm(w0:real^N)) pow 2 - t0 pow 2` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ARITH `delta + (L - delta) = L`];
    UNDISCH_TAC `(bf':real->real) t0 =
                 &2 * (&1 + delta / norm(w0:real^N)) * (w0 dot V0) - &2 * t0` THEN
    ASM_REWRITE_TAC[DOT_LNEG; DOT_LMUL] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(L - delta = &0) /\ ~(L = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ASM_REWRITE_TAC[]]);;

