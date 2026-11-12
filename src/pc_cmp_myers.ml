(* ========================================================================= *)
(* Unit pc_cmp_myers (comparison-geometry layer CMP): Myers-type diameter  *)
(* bounds on a complete manifold, along a minimizing geodesic of length    *)
(* d >= 2 r0 (MFD_COMPLETE_MINIMIZING_GEODESIC, pc_geo_hr):                 *)
(* - CMP_MYERS_DIAMETER (k g <= Ric <= (n-1) K g, k > 0): the Ricci integral*)
(*   is at least k d^2 and at most d 2 (n-1) (2/3 K r0 + 1/r0)              *)
(*   (CMP_RICCI_INTEGRAL, MT Claim 3.24), so                                *)
(*   d <= max (2 r0) (2 (n-1) (2/3 K r0 + 1/r0) / k);                       *)
(* - CMP_MYERS_DIAMETER_RIC (only k g <= Ric, k > 0): the tent inequality   *)
(*   CMPI_TENT_RICCI gives k (d - 2 r0) <= 2 (n-1) / r0, so                 *)
(*   d <= 2 r0 + 2 (n-1) / (k r0).                                          *)
(* Used for the diameter of round components (pc_p2c_blowup, Claim 11.6).    *)
(* ========================================================================= *)

needs "src/pc_cmp_index.ml";;
needs "src/pc_geo_hr.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The Ricci lower bound along the minimizing geodesic and the               *)
(* diameter bound.                                                            *)
(* ========================================================================= *)

(* Along t |-> exp_x(t v), t in [0,1], the velocity has g-norm |v|, so a     *)
(* lower bound k g <= Ric gives Ric(gamma',gamma') >= k |v|^2.               *)

let CMPMY_RICCI_LOWER_ALONG = prove
 (`!top atlas (g:A->real^N^N) k x v t.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ v IN mfd_exp_dom (top,atlas) g x /\ &0 < mfd_tnorm g x v /\
     (!z w. z IN topspace top ==> k * (w dot (g z ** w)) <= mfd_ricci atlas g z w w) /\
     &0 <= t /\ t <= &1
     ==> k * mfd_tnorm g x v pow 2 <=
         mfd_ricci atlas g (mfd_geo (top,atlas) g x v t)
           (mfd_vel atlas (mfd_geo (top,atlas) g x v) t)
           (mfd_vel atlas (mfd_geo (top,atlas) g x v) t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "lo") STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `v:real^N`] CMPI_UNIT_GEO) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d = mfd_tnorm (g:A->real^N^N) x v` THEN
  ABBREV_TAC `u:real^N = inv d % v` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "unit")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rel")))))))) THEN
  SUBGOAL_THEN `t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `real_interval[&0,&1]`)) (concl th))) THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "rel" (MP_TAC o C MP (ASSUME `t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`) o
                  SPEC `t:real`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  ABBREV_TAC `w = mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^N^N) x u) (d * t)` THEN
  ABBREV_TAC `p = mfd_geo (top,atlas) (g:A->real^N^N) x u (d * t)` THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) dot ((g:A->real^N^N) p ** w) = &1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w"; "p"] THEN USE_THEN "unit" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "lo" (MP_TAC o C MP (ASSUME `(p:A) IN topspace top`) o
                 SPECL [`p:A`; `d % w:real^N`]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_RID]);;

(* The diameter bound. *)

let CMP_MYERS_DIAMETER = prove
 (`!top atlas (g:A->real^N^N) k K r0 x y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ &0 < k /\ &0 < r0 /\
     (!z w. z IN topspace top ==> k * (w dot (g z ** w)) <= mfd_ricci atlas g z w w) /\
     (!z w. z IN topspace top
            ==> mfd_ricci atlas g z w w <= &(dimindex(:N) - 1) * K * (w dot (g z ** w))) /\
     mfd_joinable (top,atlas) x y
     ==> mfd_dist (top,atlas) g x y <=
         max (&2 * r0) (&2 * &(dimindex(:N) - 1) * (&2 / &3 * K * r0 + inv r0) / k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "lo") (CONJUNCTS_THEN2 (LABEL_TAC "hi")
     ASSUME_TAC)))))))) THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) (g:A->real^N^N) x y` THEN
  ASM_CASES_TAC `d < &2 * r0` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * r0 <= d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `y:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
                &0 < mfd_tnorm (g:A->real^N^N) x v`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[CMP_RICCI_INTEGRAL_STATEMENT]
           (ISPECL [`(:A)`; `(:N)`] CMP_RICCI_INTEGRAL)) THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                             `g:A->real^N^N`; `x:A`; `v:real^N`; `K:real`; `r0:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`z:A`; `w:real^N`] THEN
    REWRITE_TAC[IN_UNION; mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "hi" MATCH_MP_TAC THEN ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `k * d pow 2 <=
    real_integral (real_interval[&0,&1])
      (\t. mfd_ricci atlas (g:A->real^N^N) (mfd_geo (top,atlas) g x v t)
             (mfd_vel atlas (mfd_geo (top,atlas) g x v) t)
             (mfd_vel atlas (mfd_geo (top,atlas) g x v) t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[&0,&1]) (\t:real. k * d pow 2)` THEN
    CONJ_TAC THENL
     [SIMP_TAC[REAL_INTEGRAL_CONST; REAL_POS] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      BETA_TAC THEN
      SUBGOAL_THEN `d = mfd_tnorm (g:A->real^N^N) x v` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CMPMY_RICCI_LOWER_ALONG THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `k * d pow 2 <= d * (&2 * &(dimindex(:N) - 1) * (&2 / &3 * K * r0 + inv r0))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[&0,&1])
      (\t. mfd_ricci atlas (g:A->real^N^N) (mfd_geo (top,atlas) g x v t)
             (mfd_vel atlas (mfd_geo (top,atlas) g x v) t)
             (mfd_vel atlas (mfd_geo (top,atlas) g x v) t))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `inv r0`)) (concl th) &&
      can (find_term (fun u -> try fst(dest_const u) = "real_integral" with _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `y <= b ==> y <= max a b`) THEN
  SUBGOAL_THEN `&2 * &(dimindex(:N) - 1) * (&2 / &3 * K * r0 + inv r0) / k =
                (&2 * &(dimindex(:N) - 1) * (&2 / &3 * K * r0 + inv r0)) / k`
  SUBST1_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The diameter bound from a lower Ricci bound only.  The tent               *)
(* inequality CMPI_TENT_RICCI along a unit-speed minimizing geodesic of      *)
(* length d >= 2 r0 bounds the middle integral, which is at least            *)
(* k (d - 2 r0); the end integrals are nonnegative.  Hence                   *)
(*   d <= 2 r0 + 2 (n-1) / (k r0).                                           *)
(* ========================================================================= *)

let CMPMY_TENT_LOWER = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J d (Fr:num->real->real^N) r0 k.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_geodesic (top,atlas) g gamma J /\
        (!t. t IN J
             ==> mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t) = &1) /\
        real_interval[&0,d] SUBSET J /\
        mfd_dist (top,atlas) g (gamma(&0)) (gamma d) = d /\
        cmp_pframe atlas g gamma J Fr /\
        (!t. t IN J ==> Fr 1 t = mfd_vel atlas gamma t) /\
        &0 < r0 /\ &2 * r0 <= d /\ &0 <= k /\
        (!t. t IN J
             ==> k <= mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t)
                        (mfd_vel atlas gamma t))
        ==> k * (d - &2 * r0) <= &2 * &(dimindex(:N) - 1) / r0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `d:real`;
                 `Fr:num->real->real^N`; `r0:real`] CMPI_TENT_RICCI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `R1 = \t. mfd_ricci atlas (g:A->real^N^N) ((gamma:real->A) t)
                         (mfd_vel atlas gamma t) (mfd_vel atlas gamma t)` THEN
  SUBGOAL_THEN `!t. mfd_ricci atlas (g:A->real^N^N) ((gamma:real->A) t)
                      (mfd_vel atlas gamma t) (mfd_vel atlas gamma t) = (R1:real->real) t`
  (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "R1" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(R1:real->real) real_continuous_on J` ASSUME_TAC THENL
   [EXPAND_TAC "R1" THEN MATCH_MP_TAC CMPI_RICCI_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `Fr:num->real->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN J ==> k <= (R1:real->real) t` (LABEL_TAC "lo") THENL
   [EXPAND_TAC "R1" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!p q. &0 <= p /\ p <= q /\ q <= d ==> real_interval[p,q] SUBSET J`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `real_interval[&0,d]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q a b. &0 <= p /\ p <= q /\ q <= d
              ==> (\t. (a + b * t) pow 2 * (R1:real->real) t) real_integrable_on
                  real_interval[p,q] /\
                  &0 <= real_integral (real_interval[p,q]) (\t. (a + b * t) pow 2 * R1 t)`
  (LABEL_TAC "int") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(R1:real->real) real_continuous_on real_interval[p,q]` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `J:real->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\t. a + b * t) real_continuous_on real_interval[p,q]` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\t. (a + b * t) pow 2 * (R1:real->real) t) real_integrable_on
                  real_interval[p,q]` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "lo" MATCH_MP_TAC THEN
    USE_THEN "sub" (MP_TAC o SPECL [`p:real`; `q:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `k * (d - &2 * r0) <=
    real_integral (real_interval[r0,d - r0]) (\t. (&1 + &0 * t) pow 2 * (R1:real->real) t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[r0,d - r0]) (\t:real. k)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH `&2 * r0 <= d ==> r0 <= d - r0`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [USE_THEN "int" (MP_TAC o SPECL [`r0:real`; `d - r0`; `&1`; `&0`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_POW_ONE; REAL_MUL_LID] THEN
    USE_THEN "lo" MATCH_MP_TAC THEN
    USE_THEN "sub" (MP_TAC o SPECL [`r0:real`; `d - r0`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= real_integral (real_interval[&0,r0])
            (\t. (&0 + inv r0 * t) pow 2 * (R1:real->real) t) /\
    &0 <= real_integral (real_interval[d - r0,d])
            (\t. (d / r0 + --inv r0 * t) pow 2 * (R1:real->real) t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "int" (MP_TAC o SPECL [`&0`; `r0:real`; `&0`; `inv r0`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "int" (MP_TAC o SPECL [`d - r0`; `d:real`; `d / r0`; `--inv r0`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMP_MYERS_DIAMETER_RIC = prove
 (`!top atlas (g:A->real^N^N) k r0 x y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ &0 < k /\ &0 < r0 /\
     (!z w. z IN topspace top ==> k * (w dot (g z ** w)) <= mfd_ricci atlas g z w w) /\
     mfd_joinable (top,atlas) x y
     ==> mfd_dist (top,atlas) g x y <= &2 * r0 + &2 * &(dimindex(:N) - 1) / (k * r0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "lo") ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `&0 <= &2 * &(dimindex(:N) - 1) / (k * r0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) (g:A->real^N^N) x y` THEN
  ASM_CASES_TAC `d < &2 * r0` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * r0 <= d /\ &0 < d` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `y:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
                &0 < mfd_tnorm (g:A->real^N^N) x v`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `v:real^N`] CMPI_UNIT_GEO) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `u:real^N = inv d % v` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x u = &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM(ASSUME `inv d % (v:real^N) = u`)] THEN
    ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] CMPI_FRAME_UNIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fr:num->real->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) x u`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u`; `d:real`;
                 `Fr:num->real->real^N`; `r0:real`; `k:real`] CMPMY_TENT_LOWER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [GSYM(MATCH_MP (check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `&1`)) (concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "mfd_vel" with _ -> false))
             (concl th)) th) (ASSUME `t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u`))]) THEN
    USE_THEN "lo" MATCH_MP_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `d - &2 * r0 <= inv k * (&2 * &(dimindex(:N) - 1) / r0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv k * (k * (d - &2 * r0))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID;
                   REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv k * (&2 * &(dimindex(:N) - 1) / r0) =
                &2 * &(dimindex(:N) - 1) / (k * r0)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

