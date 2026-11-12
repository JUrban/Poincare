(* ========================================================================= *)
(* Unit pc_cmp_tpg (comparison-geometry layer CMP): CMP_R1_TOPONOGOV, the    *)
(* angle form of Toponogov's comparison under sec >= 0 on a complete         *)
(* manifold.  For two minimizing unit-speed geodesics from p, the cosine of  *)
(* the comparison angle (s1^2 + s2^2 - d^2)/(2 s1 s2) is non-decreasing in   *)
(* each length, by the concavity of t |-> d(q, sigma t)^2 - t^2 (Calabi      *)
(* barriers, pc_cmp_hup, pc_cmp_topo) applied in each variable.  The         *)
(* statement has no connectedness hypothesis: all points involved are        *)
(* joinable to p.                                                            *)
(* ========================================================================= *)

needs "src/pc_cmp_a7.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The barriers of CMPA_HBARRIER with joinability of q to the                *)
(* geodesic instead of connectedness of M.                                   *)
(* ========================================================================= *)

let CMPAN_HBARRIER_J = prove
 (`!top atlas (g:A->real^N^N) (p:A) u (q:A) t0 e.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p u = &1 /\ q IN topspace top /\ &0 < e /\
        (!t. mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u t) q)
        ==> ?d bf bf' bf2.
              &0 < d /\
              (!s. abs(s - t0) < d ==> (bf has_real_derivative bf'(s)) (atreal s)) /\
              (bf' has_real_derivative bf2) (atreal t0) /\ bf2 <= e /\
              bf t0 = mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u t0) pow 2 -
                      t0 pow 2 /\
              (!s. abs(s - t0) < d
                   ==> mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u s) pow 2 -
                       s pow 2 <= bf s)`,
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
  SUBGOAL_THEN `!s. (sigma:real->A) s IN topspace top` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `(:real)`] THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. mfd_tnorm (g:A->real^N^N) ((sigma:real->A) s) (mfd_vel atlas sigma s) = &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `s:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  ASM_CASES_TAC `(sigma:real->A) t0 = q` THENL
   [EXISTS_TAC `&1` THEN
    EXISTS_TAC `\s. t0 pow 2 - &2 * s * t0` THEN
    EXISTS_TAC `\s:real. --(&2 * t0)` THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[REAL_LT_01] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `q:A`] MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `t0:real`; `s:real`]
        GEOH_GEO_SEG_DIST) THEN
      ASM_REWRITE_TAC[IN_UNIV; REAL_MUL_RID] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `q:A`; `(sigma:real->A) s`] MFD_DIST_POS_LE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) q ((sigma:real->A) s) pow 2 <=
                    (s - t0) pow 2` MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `z = (sigma:real->A) t0` THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) z q` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `q:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^N^N) z q` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`; `q:A`] MFD_DIST_EQ_0) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`; `q:A`] MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `delta = min (L / &2) (e * L / &4)` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= L / &2 /\ delta <= e * L / &4` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < e * L / &4` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "delta" THEN REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`; `t0:real`; `z:A`; `w:real^N`; `q:A`;
                 `delta:real`] CMPE_BARRIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `bf2 <= &2 * delta / (mfd_tnorm (g:A->real^N^N) z w - delta)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * delta / (L - delta)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < L - delta` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `!x y. &2 * x / y = (&2 * x) / y`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `e * L / &2 <= e * (L - delta)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `z:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th) &&
      can (find_term ((=) `bf:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* Monotonicity in one variable.  For q joinable to p with                   *)
(* d(p,q) = s1 > 0 and a unit-speed geodesic sigma from p, the comparison   *)
(* cosine (s1^2 + s^2 - d(q,sigma s)^2)/(2 s1 s) is non-decreasing in s > 0  *)
(* (concavity of d(q,sigma s)^2 - s^2, whose value at 0 is s1^2).            *)
(* ========================================================================= *)

let CMPAN_ALG = prove
 (`!X Y a c s1. &0 < a /\ &0 < c /\ &0 < s1 /\ X <= a / c * Y
                ==> X / (&2 * s1 * a) <= Y / (&2 * s1 * c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(a / c * Y) / (&2 * s1 * a)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * s1 * a` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `~(a = &0) /\ ~(c = &0) /\ ~(s1 = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]);;

let CMPAN_MONO1 = prove
 (`!top atlas (g:A->real^N^N) (p:A) v (q:A) s1 s2 s2'.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p v = &1 /\ q IN topspace top /\
        mfd_joinable (top,atlas) p q /\
        mfd_dist (top,atlas) g p q = s1 /\ &0 < s1 /\ &0 < s2 /\ s2 <= s2'
        ==> (s1 pow 2 + s2 pow 2 -
             mfd_dist (top,atlas) g q (mfd_exp (top,atlas) g p (s2 % v)) pow 2) /
            (&2 * s1 * s2) <=
            (s1 pow 2 + s2' pow 2 -
             mfd_dist (top,atlas) g q (mfd_exp (top,atlas) g p (s2' % v)) pow 2) /
            (&2 * s1 * s2')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s2:real = s2'` THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `s2 < s2'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p v = (:real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) p = (:real^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[mfd_exp_dom; EXTENSION; IN_UNIV; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. mfd_exp (top,atlas) (g:A->real^N^N) p (t % v) =
                    mfd_geo (top,atlas) g p v t`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `v:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                      (mfd_geo (top,atlas) (g:A->real^N^N) p v t) q`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `p:A` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p v t`; `p:A`] MFD_JOINABLE_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `t % (v:real^N)`] CMPH_EXP_DIST_LE) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `v:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. mfd_dist (top,atlas) (g:A->real^N^N) q
                        (mfd_geo (top,atlas) g p v t) pow 2 - t pow 2`;
                 `&0`; `s2':real`] CMPA_CALABI) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CMPA_HCONT THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t0:real`; `e:real`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`; `v:real^N`; `q:A`; `t0:real`; `e:real`]
        CMPAN_HBARRIER_J) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s2:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `p:A`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_POW_ZERO; ARITH_EQ] THEN DISCH_TAC THEN
  MATCH_MP_TAC CMPAN_ALG THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN ABBREV_TAC `Da = mfd_dist (top,atlas) (g:A->real^N^N) q
                                          (mfd_geo (top,atlas) g p v s2) pow 2` THEN
  ABBREV_TAC `Dc = mfd_dist (top,atlas) (g:A->real^N^N) q
                     (mfd_geo (top,atlas) g p v s2') pow 2` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The angle comparison CMP_R1_TOPONOGOV.  The two-variable monotonicity     *)
(* from CMPAN_MONO1 applied in each variable (initial segments of the sides  *)
(* are minimizing, CMPL_SEG_MIN); the statement constant has the body of the *)
(* statement P2B_REQ_CMP_TOPONOGOV_STATEMENT of pc_p2b_defs verbatim.        *)
(* ========================================================================= *)

let CMPAN_TOPONOGOV_GEN = prove
 (`!top atlas (g:A->real^N^N) p v1 v2 L1 L2.
       hausdorff_space top /\ smooth_manifold_atlas top atlas /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       p IN topspace top /\ mfd_tnorm g p v1 = &1 /\ mfd_tnorm g p v2 = &1 /\
       &0 < L1 /\ &0 < L2 /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L1 % v1)) = L1 /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L2 % v2)) = L2
       ==> !s1 s1' s2 s2'. &0 < s1 /\ s1 <= s1' /\ s1' <= L1 /\
                           &0 < s2 /\ s2 <= s2' /\ s2' <= L2
           ==> (s1 pow 2 + s2 pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1 % v1))
                                       (mfd_exp (top,atlas) g p (s2 % v2)) pow 2) /
               (&2 * s1 * s2) <=
               (s1' pow 2 + s2' pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1' % v1))
                                       (mfd_exp (top,atlas) g p (s2' % v2)) pow 2) /
               (&2 * s1' * s2')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) p = (:real^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[mfd_exp_dom; EXTENSION; IN_UNIV; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v L s. mfd_tnorm (g:A->real^N^N) p v = &1 /\ &0 < L /\
            mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L % v)) = L /\
            &0 <= s /\ s <= L
            ==> mfd_exp (top,atlas) g p (s % v) IN topspace top /\
                mfd_joinable (top,atlas) p (mfd_exp (top,atlas) g p (s % v)) /\
                mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (s % v)) = s`
  (LABEL_TAC "seg") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[IN_UNIV];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`; `s % (v:real^N)`] CMPH_EXP_DIST_LE) THEN
      ASM_REWRITE_TAC[IN_UNIV] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`; `L % (v:real^N)`; `s:real`] CMPL_SEG_MIN) THEN
      ASM_REWRITE_TAC[REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < L ==> abs L = L`] THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `(s * inv L) * L = s` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; SIMP_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(s1 pow 2 + s2' pow 2 -
     mfd_dist (top,atlas) (g:A->real^N^N) (mfd_exp (top,atlas) g p (s1 % v1))
                            (mfd_exp (top,atlas) g p (s2' % v2)) pow 2) /
    (&2 * s1 * s2')` THEN
  CONJ_TAC THENL
   [USE_THEN "seg" (MP_TAC o SPECL [`v1:real^N`; `L1:real`; `s1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC CMPAN_MONO1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "seg" (MP_TAC o SPECL [`v2:real^N`; `L2:real`; `s2':real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `v1:real^N`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) p (s2' % v2)`;
                 `s2':real`; `s1:real`; `s1':real`] CMPAN_MONO1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= L1
        ==> mfd_dist (top,atlas) (g:A->real^N^N) (mfd_exp (top,atlas) g p (s2' % v2))
              (mfd_exp (top,atlas) g p (s % v1)) =
            mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s % v1))
              (mfd_exp (top,atlas) g p (s2' % v2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s1 /\ s1 <= L1 /\ &0 <= s1' /\ s1' <= L1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a = c /\ b = d ==> a <= b ==> c <= d`) THEN
  CONJ_TAC THEN BINOP_TAC THEN REAL_ARITH_TAC);;

let CMP_R1_TOPONOGOV_STATEMENT = new_definition
 `CMP_R1_TOPONOGOV_STATEMENT (w:B->bool) <=>
    !top atlas g p v1 v2 L1 L2.
       hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       p IN topspace top /\ mfd_tnorm g p v1 = &1 /\ mfd_tnorm g p v2 = &1 /\
       &0 < L1 /\ &0 < L2 /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L1 % v1)) = L1 /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L2 % v2)) = L2
       ==> !s1 s1' s2 s2'. &0 < s1 /\ s1 <= s1' /\ s1' <= L1 /\
                           &0 < s2 /\ s2 <= s2' /\ s2' <= L2
           ==> (s1 pow 2 + s2 pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1 % v1))
                                       (mfd_exp (top,atlas) g p (s2 % v2)) pow 2) /
               (&2 * s1 * s2) <=
               (s1' pow 2 + s2' pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1' % v1))
                                       (mfd_exp (top,atlas) g p (s2' % v2)) pow 2) /
               (&2 * s1' * s2')`;;

let CMP_R1_TOPONOGOV = prove
 (`!w:B->bool. CMP_R1_TOPONOGOV_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[CMP_R1_TOPONOGOV_STATEMENT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMPAN_TOPONOGOV_GEN THEN
  ASM_REWRITE_TAC[]);;

