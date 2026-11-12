(* ========================================================================= *)
(* Unit pc_cmp_a7 (comparison-geometry layer CMP): MT Lemma 11.13            *)
(* (CMP_A7_LEMMA_11_13).  On a complete connected manifold with sec >= 0 and *)
(* x0 in M there is D > 0 such that every y with d(x0,y) = d >= D has a      *)
(* point x with d(y,x) = d and d(x0,x) > 3d/2.  MT's proof with the ray      *)
(* replaced by a second minimizing geodesic: if the lemma fails, the initial *)
(* directions u_n of minimizing geodesics to bad points y_n (d_n >= n + 1)   *)
(* have, by compactness of the unit sphere, two members u_n, u_m with |u_n - *)
(* u_m|_g < 1/2 and d_m >= 2 d_n; the hinge comparison (CMPA_HINGE) puts y_n *)
(* within d_n/2 of exp(d_n u_m), and the intermediate value theorem on s |-> *)
(* d(y_n, exp(s u_m)), s in [d_n, d_m], gives a point at distance d_n from   *)
(* y_n and at distance > 3 d_n / 2 from x0.                                  *)
(* ========================================================================= *)

needs "src/pc_cmp_topo.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Initial segments of a minimizing geodesic are minimizing (S5), and the    *)
(* hinge comparison in the form d(exp(s u1),exp(s u2)) <= s |u1 - u2|_g.     *)
(* ========================================================================= *)

let CMPL_SEG_MIN = prove
 (`!top atlas (g:A->real^N^N) (x:A) v s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ x IN topspace top /\
        &0 < mfd_tnorm g x v /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v /\
        &0 <= s /\ s <= mfd_tnorm g x v
        ==> mfd_dist (top,atlas) g x
              (mfd_exp (top,atlas) g x (s % (inv(mfd_tnorm g x v) % v))) = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = mfd_tnorm (g:A->real^N^N) x v` THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_CASES_TAC `s:real = L` THENL
   [ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `(v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[mfd_exp_dom; IN_ELIM_THM; IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:A)`; `(:N)`] CMP_MINIMIZING_GEODESIC) THEN
  REWRITE_TAC[CMP_MINIMIZING_GEODESIC_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                             `g:A->real^N^N`; `x:A`; `v:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s * inv L`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID]);;

let CMPL_HINGE_EQ = prove
 (`!top atlas (g:A->real^N^N) (p:A) u1 u2 s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ connected_space top /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p u1 = &1 /\ mfd_tnorm g p u2 = &1 /\ &0 < s /\
        mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (s % u1)) = s
        ==> mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s % u1))
                                   (mfd_exp (top,atlas) g p (s % u2))
            <= s * mfd_tnorm g p (u1 - u2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u1:real^N`; `u2:real^N`; `s:real`; `s:real`]
    CMPA_HINGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOG_G_SYM_POS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(u1:real^N) dot ((g:A->real^N^N) p ** u1) = &1 /\ u2 dot (g p ** u2) = &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `(v:real^N) dot ((g:A->real^N^N) p ** v)`)) (concl th)
      then REWRITE_TAC[GSYM th] else failwith "") THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p (u1 - u2) pow 2 =
                &2 - &2 * (u1 dot (g p ** u2))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_LSUB; DOT_RSUB; MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u2:real^N`; `u1:real^N`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> try fst(dest_const t) = "dot" with Failure _ -> false))
        (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_MUL] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The main step.  If y = exp(d u1) with d(x0,y) = d, s |-> exp(s u2) is     *)
(* minimizing on [0,dm] with dm >= 2 d, and |u1 - u2|_g < 1/2, then some x   *)
(* has d(y,x) = d and d(x0,x) > 3d/2.                                        *)
(* ========================================================================= *)

let CMPL_DCONT = prove
 (`!top atlas (g:A->real^N^N) (p:A) u (q:A) a c.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top
        ==> (\t. mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u t))
            real_continuous_on real_interval[a,c]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u = (:real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) p u`; `(:real)`] GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM GRGD_CONTINUOUS_MAP_REAL] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN EXISTS_TAC `(:real)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN
  SUBGOAL_THEN `(\t. mfd_dist (top,atlas) (g:A->real^N^N) q (mfd_geo (top,atlas) g p u t)) =
                (\y. mfd_dist (top,atlas) g q y) o mfd_geo (top,atlas) g p u`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[]);;

let CMPL_STEP = prove
 (`!top atlas (g:A->real^N^N) (x0:A) u1 u2 d dm.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ connected_space top /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        x0 IN topspace top /\ mfd_tnorm g x0 u1 = &1 /\ mfd_tnorm g x0 u2 = &1 /\
        &0 < d /\
        mfd_dist (top,atlas) g x0 (mfd_exp (top,atlas) g x0 (d % u1)) = d /\
        mfd_dist (top,atlas) g x0 (mfd_exp (top,atlas) g x0 (dm % u2)) = dm /\
        &2 * d <= dm /\ mfd_tnorm g x0 (u1 - u2) < inv(&2)
        ==> ?x. x IN topspace top /\
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g x0 (d % u1)) x = d /\
                &3 / &2 * d < mfd_dist (top,atlas) g x0 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x0 u2 = (:real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) x0 = (:real^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[mfd_exp_dom; EXTENSION; IN_UNIV; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. mfd_exp (top,atlas) (g:A->real^N^N) x0 (t % u2) =
                    mfd_geo (top,atlas) g x0 u2 t`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x0:A`; `u2:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x0:A`; `u2:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) x0 u2` THEN STRIP_TAC THEN
  ABBREV_TAC `y = mfd_exp (top,atlas) (g:A->real^N^N) x0 (d % u1)` THEN
  SUBGOAL_THEN `(y:A) IN topspace top /\ !t. (sigma:real->A) t IN topspace top`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "y" THEN MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[IN_UNIV];
      GEN_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `(:real)`] THEN
      ASM_REWRITE_TAC[IN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:A. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) a b`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) y ((sigma:real->A) d) < d / &2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x0:A`; `u1:real^N`; `u2:real^N`; `d:real`]
      CMPL_HINGE_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `d * mfd_tnorm (g:A->real^N^N) x0 (u1 - u2)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `d * mfd_tnorm (g:A->real^N^N) x0 (u1 - u2) < d * inv(&2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= dm
                    ==> mfd_dist (top,atlas) (g:A->real^N^N) x0 ((sigma:real->A) s) = s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x0:A`; `dm % (u2:real^N)`; `s:real`] CMPL_SEG_MIN) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x0:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN
    SUBGOAL_THEN `abs dm = dm /\ &0 < dm` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(s * inv dm) * dm = s` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < dm` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. mfd_dist (top,atlas) (g:A->real^N^N) y ((sigma:real->A) s)`;
                 `d:real`; `dm:real`; `d:real`] REAL_IVT_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      EXPAND_TAC "sigma" THEN MATCH_MP_TAC CMPL_DCONT THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x0:A`; `y:A`; `(sigma:real->A) dm`]
        MFD_DIST_TRIANGLE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x0 ((sigma:real->A) dm) = dm`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `dm:real`)) (concl th) &&
          can (find_term ((=) `x0:A`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `ss:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(sigma:real->A) ss` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x0 ((sigma:real->A) ss) = ss`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `dm:real`)) (concl th) &&
      can (find_term ((=) `x0:A`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `sigma:real->A`; `(:real)`; `d:real`; `ss:real`] GEOH_GEO_SEG_DIST) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `sigma:real->A`; `(:real)`; `d:real`; `&0`] MFD_GEODESIC_SPEED) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_MUL_RID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `(sigma:real->A) d`; `(sigma:real->A) ss`]
    MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* MT Lemma 11.13 in dimension n.  If it fails there are bad points Y n with *)
(* d(x0, Y n) >= n + 1; their unit initial directions (in an orthonormal     *)
(* frame at x0) lie on the compact unit sphere, so two of them, n0 < m0      *)
(* along a convergent subsequence, are within 1/2 with d(x0, Y m0) >= 2      *)
(* d(x0, Y n0), and CMPL_STEP contradicts the badness of Y n0.               *)
(* ========================================================================= *)

let CMPL_A7_GEN = prove
 (`!top atlas (g:A->real^N^N) (x0:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ connected_space top /\ mfd_complete (top,atlas) g /\
        x0 IN topspace top /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g x u v)
        ==> ?D. &0 < D /\
                !y. y IN topspace top /\ D <= mfd_dist (top,atlas) g x0 y
                    ==> ?x. x IN topspace top /\
                            mfd_dist (top,atlas) g y x = mfd_dist (top,atlas) g x0 y /\
                            &3 / &2 * mfd_dist (top,atlas) g x0 y <
                            mfd_dist (top,atlas) g x0 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. ?y. y IN topspace top /\ &n + &1 <= mfd_dist (top,atlas) (g:A->real^N^N) x0 y /\
            ~(?x. x IN topspace top /\
                  mfd_dist (top,atlas) g y x = mfd_dist (top,atlas) g x0 y /\
                  &3 / &2 * mfd_dist (top,atlas) g x0 y < mfd_dist (top,atlas) g x0 x)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&n + &1` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; DE_MORGAN_THM] THEN
    SUBGOAL_THEN `&0 < &n + &1` (fun th -> REWRITE_TAC[th]) THENL
     [REAL_ARITH_TAC; MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `Y:num->A` (LABEL_TAC "Y")) THEN
  SUBGOAL_THEN
   `!n. ?v. mfd_exp (top,atlas) (g:A->real^N^N) x0 v = (Y:num->A) n /\
            mfd_tnorm g x0 v = mfd_dist (top,atlas) g x0 (Y n)`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x0:A`; `(Y:num->A) n`]
      MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "Y" (fun th -> REWRITE_TAC[th]);
      MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:num->real^N` (LABEL_TAC "V")) THEN
  ABBREV_TAC `dd = \n. mfd_dist (top,atlas) (g:A->real^N^N) x0 ((Y:num->A) n)` THEN
  SUBGOAL_THEN `!n. &n + &1 <= (dd:num->real) n /\ &0 < dd n` (LABEL_TAC "dd") THENL
   [GEN_TAC THEN EXPAND_TAC "dd" THEN REWRITE_TAC[] THEN
    USE_THEN "Y" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = \n. inv((dd:num->real) n) % (V:num->real^N) n` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x0:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. mfd_tnorm (g:A->real^N^N) x0 ((u:num->real^N) n) = &1 /\
        mfd_exp (top,atlas) g x0 ((dd:num->real) n % u n) = (Y:num->A) n /\
        mfd_dist (top,atlas) g x0 (mfd_exp (top,atlas) g x0 (dd n % u n)) = dd n`
  (LABEL_TAC "u") THENL
   [GEN_TAC THEN EXPAND_TAC "u" THEN REWRITE_TAC[] THEN
    USE_THEN "dd" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    USE_THEN "V" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; REAL_ABS_INV] THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x0 ((Y:num->A) n) = dd n`
    SUBST1_TAC THENL [EXPAND_TAC "dd" THEN REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x0:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMPQ_FRAME_INVERTIBLE) THEN
  ABBREV_TAC `a = \n. matrix_inv(E:real^N^N) ** (u:num->real^N) n` THEN
  SUBGOAL_THEN `!n. (E:real^N^N) ** (a:num->real^N) n = (u:num->real^N) n` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "a" THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (a:num->real^N) n IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0] THEN
    MP_TAC(ISPECL [`g:A->real^N^N`; `x0:A`; `E:real^N^N`; `(a:num->real^N) n`]
      CMPP_TNORM_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "u" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `&1`] COMPACT_SPHERE) THEN REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `a:num->real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N` (X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(((a:num->real^N) o (r:num->num)) --> l) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&4)`) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `K:num`) THEN
  ABBREV_TAC `n0 = (r:num->num) K` THEN
  MP_TAC(SPEC `&2 * (dd:num->real) n0` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  ABBREV_TAC `m0 = (r:num->num) (MAX K N1)` THEN
  SUBGOAL_THEN `(N1:num) <= m0` ASSUME_TAC THENL
   [EXPAND_TAC "m0" THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `MAX K N1` THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `r:num->num` MONOTONE_BIGGER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `MAX K N1`)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (dd:num->real) n0 <= dd m0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N1` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "dd" (MP_TAC o SPEC `m0:num`) THEN
    UNDISCH_TAC `(N1:num) <= m0` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x0 ((u:num->real^N) n0 - u m0) < inv(&2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(u:num->real^N) n0 - u m0 = (E:real^N^N) ** ((a:num->real^N) n0 - a m0)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB]; ALL_TAC] THEN
    ASM_SIMP_TAC[CMPP_TNORM_FRAME] THEN
    FIRST_ASSUM(MP_TAC o SPEC `K:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `l:real^N`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SPEC `MAX K N1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `l:real^N`)) (concl th))) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `K <= MAX K N1`] THEN
    REWRITE_TAC[ASSUME `(r:num->num) K = n0`; ASSUME `(r:num->num) (MAX K N1) = m0`] THEN
    REWRITE_TAC[dist] THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x0:A`; `(u:num->real^N) n0`; `(u:num->real^N) m0`;
                 `(dd:num->real) n0`; `(dd:num->real) m0`] CMPL_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "u" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "dd" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "u" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "Y" (MP_TAC o SPEC `n0:num`) THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x0 ((Y:num->A) n0) = dd n0`
  SUBST1_TAC THENL [EXPAND_TAC "dd" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MESON_TAC[]);;

(* The headline (MT Lemma 11.13): the statement constant                     *)
(* CMP_A7_LEMMA_11_13_STATEMENT, with the body of the statement              *)
(* P2C_REQ_LEMMA_11_13_STATEMENT of pc_p2c_iface, and its proof from         *)
(* CMPL_A7_GEN at dimension 3 (non-compactness is not used).                 *)
(* CMPL_A7_GEN at dimension 3 (non-compactness is not used).                 *)
(* ========================================================================= *)

let CMP_A7_LEMMA_11_13_STATEMENT = new_definition
 `CMP_A7_LEMMA_11_13_STATEMENT (u:A->bool) <=>
    !top atlas g x0.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       riemannian_metric atlas g /\ connected_space top /\ ~compact_space top /\
       mfd_complete (top,atlas) g /\ x0 IN topspace top /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v)
       ==> ?D. &0 < D /\
               !y. y IN topspace top /\ D <= mfd_dist (top,atlas) g x0 y
                   ==> ?x. x IN topspace top /\
                           mfd_dist (top,atlas) g y x = mfd_dist (top,atlas) g x0 y /\
                           &3 / &2 * mfd_dist (top,atlas) g x0 y < mfd_dist (top,atlas) g x0 x`;;

let CMP_A7_LEMMA_11_13 = prove
 (`!u:A->bool. CMP_A7_LEMMA_11_13_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[CMP_A7_LEMMA_11_13_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CMPL_A7_GEN THEN ASM_REWRITE_TAC[]);;

