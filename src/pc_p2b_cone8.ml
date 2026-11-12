(* ========================================================================= *)
(* Unit pc_p2b_cone8: step (D) of the blow-up of MT Sec 10.6.  From the      *)
(* end-cone data of a bad tube (P2BK_END_CONE_STATEMENT: dE 1-Lipschitz, ray *)
(* points, the comparison angles at E satisfy the triangle inequality up to  *)
(* delta near E) and a local limit at points x k with dE(x k) -> 0, rescaled *)
(* by Q k with sqrt(Q k) dE(x k) in [m0,M0] (the form delivered by           *)
(* P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT at time 0), the rescaled distance   *)
(* functions sqrt(Q k) dE o phi k converge (Arzela-Ascoli) to a function rho *)
(* on a ball of real^3 that satisfies the hypotheses of                      *)
(* P2BK_CONE_REGULAR_STATEMENT for the limit metric (P2BK_LIMIT_CONE).       *)
(* ========================================================================= *)

needs "src/pc_p2b_cone7.ml";;
needs "src/pc_p2b_conestmts.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Comparison angles: scale invariance, the range of the cosine argument on  *)
(* admissible triangles, and sequential continuity on admissible triangles   *)
(* (acs is continuous on [-1,1] only).                                       *)
(* ========================================================================= *)

let P2BK_CANG_SCALE = prove
 (`!lam a b d. &0 < lam
               ==> p2bk_cang (lam * a) (lam * b) (lam * d) = p2bk_cang a b d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bk_cang] THEN AP_TERM_TAC THEN
  ASM_CASES_TAC `a = &0 \/ b = &0` THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_INV_0];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `~(a = &0)` THEN UNDISCH_TAC `~(b = &0)` THEN
  CONV_TAC REAL_FIELD);;

let P2BK_CANG_ARG_BOUND = prove
 (`!A C D. &0 < A /\ &0 < C /\ abs(A - C) <= D /\ D <= A + C
           ==> abs((A pow 2 + C pow 2 - D pow 2) / (&2 * A * C)) <= &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * A * C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_LDIV_EQ;
               REAL_MUL_LID] THEN
  SUBGOAL_THEN `(A - C) pow 2 <= D pow 2 /\ D pow 2 <= (A + C) pow 2` MP_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
      UNDISCH_TAC `abs(A - C) <= D` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs(A - C) <= D` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Limits through a function continuous within a set the arguments enter. *)

let P2BK_REALLIM_CONT_WITHIN = prove
 (`!f (net:A net) g l s.
     f real_continuous (atreal l within s) /\ (g ---> l) net /\
     eventually (\x. g x IN s) net
     ==> ((\x. f(g x)) ---> f l) net`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; tendsto_real; EVENTUALLY_WITHINREAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fc") (CONJUNCTS_THEN2 (LABEL_TAC "gl")
    (LABEL_TAC "gs"))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "fc" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "gl" (MP_TAC o SPEC `d:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC EVENTUALLY_MONO THEN
  EXISTS_TAC `\x:A. abs((g:A->real) x - l) < d /\ g x IN s` THEN
  ASM_REWRITE_TAC[EVENTUALLY_AND] THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_CASES_TAC `(g:A->real) x = l` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((g:A->real) x = l)` THEN REAL_ARITH_TAC);;

let P2BK_CANG_LIMIT = prove
 (`!A C D (An:num->real) Cn Dn.
     &0 < A /\ &0 < C /\ abs(A - C) <= D /\ D <= A + C /\
     (?N. !n. N <= n ==> &0 < An n /\ &0 < Cn n /\ abs(An n - Cn n) <= Dn n /\
                         Dn n <= An n + Cn n) /\
     (An ---> A) sequentially /\ (Cn ---> C) sequentially /\ (Dn ---> D) sequentially
     ==> ((\n. p2bk_cang (An n) (Cn n) (Dn n)) ---> p2bk_cang A C D) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bk_cang] THEN
  MATCH_MP_TAC P2BK_REALLIM_CONT_WITHIN THEN
  EXISTS_TAC `{u:real | abs u <= &1}` THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `{u:real | abs u <= &1}` REAL_CONTINUOUS_ON_ACS) THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC P2BK_CANG_ARG_BOUND THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REALLIM_POW THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THEN MATCH_MP_TAC REALLIM_POW THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ENTIRE] THEN UNDISCH_TAC `&0 < A` THEN UNDISCH_TAC `&0 < C` THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; IN_ELIM_THM] THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2BK_CANG_ARG_BOUND THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* The data of the limit cone (p2bk_lcdata: end-cone data of a manifold,     *)
(* points x k with dE(x k) -> 0, scales Q k with sqrt(Q k) dE(x k) in        *)
(* [m0,M0], and a local limit at time 0 of the rescaled metrics Q k g in     *)
(* charts phi k), and the distance comparison for it (P2BK_LCDATA_DIST).     *)
(* ========================================================================= *)

let p2bk_lcdata = new_definition
 `p2bk_lcdata (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
              (dE:B->real) (s1:real) (x:num->B) (Q:num->real) (m0:real) (M0:real)
              (phi:num->real^3->B) (G0:real^3->real^3^3) (r0:real) (rb:real) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
    (!y. y IN topspace top ==> &0 < dE y) /\
    (!y z. y IN topspace top /\ z IN topspace top
           ==> mfd_joinable (top,atlas) y z /\
               abs(dE y - dE z) <= mfd_dist (top,atlas) g y z) /\
    &0 < s1 /\
    (!y t. y IN topspace top /\ dE y <= s1 /\ &0 < t /\ t <= dE y / &2
           ==> ?z. z IN topspace top /\ mfd_dist (top,atlas) g y z = t /\ dE z = dE y - t) /\
    (!delta. &0 < delta
       ==> ?s0. &0 < s0 /\
             !a b c. a IN topspace top /\ b IN topspace top /\ c IN topspace top /\
                     dE a <= s0 /\ dE b <= s0 /\ dE c <= s0 /\
                     dE a <= &2 * dE b /\ dE b <= &2 * dE a /\
                     dE b <= &2 * dE c /\ dE c <= &2 * dE b
                     ==> p2bk_cang (dE a) (dE c) (mfd_dist (top,atlas) g a c) <=
                         p2bk_cang (dE a) (dE b) (mfd_dist (top,atlas) g a b) +
                         p2bk_cang (dE b) (dE c) (mfd_dist (top,atlas) g b c) + delta) /\
    &0 < m0 /\ m0 <= M0 /\
    (!k. &0 < Q k /\ x k IN topspace top /\
         m0 <= sqrt(Q k) * dE(x k) /\ sqrt(Q k) * dE(x k) <= M0) /\
    (!e. &0 < e ==> ?k0. !k. k0 <= k ==> dE(x k) < e) /\
    &0 < rb /\ rb < r0 /\ metric_field (ball(vec 0,r0)) G0 /\
    (!k. mfd_param top atlas (ball(vec 0,r0)) (phi k) /\ phi k (vec 0) = x k) /\
    (!eta. &0 < eta
           ==> ?k0. !k w. k0 <= k /\ w IN cball(vec 0,rb)
                          ==> lck_dist2 0 G0 (rfs_pullback atlas (phi k) (\y. Q k %% g y)) w
                              < eta)`;;

(* The charts map into the manifold. *)

let P2BK_LCDATA_IN = prove
 (`!top atlas (g:B->real^3^3) dE s1 x Q m0 M0 phi G0 r0 rb k w.
     p2bk_lcdata (top,atlas) g dE s1 x Q m0 M0 phi G0 r0 rb /\ w IN ball(vec 0,r0)
     ==> phi k w IN topspace top`,
  REWRITE_TAC[p2bk_lcdata] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "mfd_param" with Failure _ -> false))
        (concl th))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MFD_PARAM_MAPS o CONJUNCT1) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  UNDISCH_TAC `(w:real^3) IN ball(vec 0,r0)` THEN SET_TAC[]);;

let P2BK_LCDATA_DIST = prove
 (`!top atlas (g:B->real^3^3) dE s1 x Q m0 M0 phi G0 r0 rb.
     p2bk_lcdata (top,atlas) g dE s1 x Q m0 M0 phi G0 r0 rb
     ==> ?r rk rho0.
           &0 < r /\ &0 < rk /\ &0 < rho0 /\ ball(vec 0:real^3,r) SUBSET cball(vec 0,rk) /\ rk < rb /\
           !e. &0 < e /\ e <= &1 / &2
               ==> ?k0. !k w w'.
                      k0 <= k /\ w IN ball(vec 0,r) /\ w' IN ball(vec 0,r)
                      ==> mfd_joinable (subtopology euclidean (ball(vec 0,rb)),
                                        open_set_atlas (ball(vec 0,rb))) w w' /\
                          abs(sqrt(Q k) * mfd_dist (top,atlas) g (phi k w) (phi k w') -
                              mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                        open_set_atlas (ball(vec 0,rb))) G0 w w')
                          <= e * mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                           open_set_atlas (ball(vec 0,rb))) G0 w w' /\
                          (!q. q IN topspace top /\
                               sqrt(Q k) * mfd_dist (top,atlas) g (phi k w) q < rho0
                               ==> ?y. y IN cball(vec 0,rk) /\ q = phi k y /\
                                       mfd_joinable (subtopology euclidean (ball(vec 0,rb)),
                                                     open_set_atlas (ball(vec 0,rb))) w y /\
                                       mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                                 open_set_atlas (ball(vec 0,rb))) G0 w y
                                       <= (&1 + e) *
                                          (sqrt(Q k) * mfd_dist (top,atlas) g (phi k w) q))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_lcdata]) THEN
  MP_TAC(ISPECL [`\k:num. (top:B topology)`; `\k:num. (atlas:((B->bool)#(B->real^3))->bool)`;
                 `\k:num y:B. (Q:num->real) k %% (g:B->real^3^3) y`; `phi:num->real^3->B`;
                 `G0:real^3->real^3^3`; `r0:real`; `rb:real`] P2BK_LOCAL_LIMIT_DIST) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `rk:real` (X_CHOOSE_THEN `rho0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lim"))))))))) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `rk:real`; `rho0:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "lim" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN EXISTS_TAC `k0:num` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `w:real^3`; `w':real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v. v IN ball(vec 0:real^3,r) ==> (phi:num->real^3->B) k v IN topspace top`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BK_LCDATA_IN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                          `dE:B->real`; `s1:real`; `x:num->B`; `Q:num->real`; `m0:real`;
                          `M0:real`; `G0:real^3->real^3^3`; `r0:real`; `rb:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET cball(vec 0,rk)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
    UNDISCH_TAC `(v:real^3) IN ball(vec 0,r)` THEN REWRITE_TAC[IN_BALL_0] THEN
    UNDISCH_TAC `rk < rb` THEN UNDISCH_TAC `rb < r0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "k0" (MP_TAC o SPECL [`k:num`; `w:real^3`; `w':real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (Q:num->real) k` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y z:B. y IN topspace top /\ z IN topspace top
                        ==> mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) y z`
    (LABEL_TAC "jn") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(phi:num->real^3->B) k w IN topspace top /\ phi k w' IN topspace top`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. q IN topspace top
        ==> mfd_dist (top,atlas) (\y. (Q:num->real) k %% (g:B->real^3^3) y)
                     ((phi:num->real^3->B) k w) q =
            sqrt(Q k) * mfd_dist (top,atlas) g (phi k w) q`
    (LABEL_TAC "sc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_DIST_SCALE THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "jn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "pre")))) THEN
  USE_THEN "sc" (fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `(phi:num->real^3->B) k w' IN topspace top`)]) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `q:B` THEN STRIP_TAC THEN
  USE_THEN "pre" (MP_TAC o SPEC `q:B`) THEN
  USE_THEN "sc" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(q:B) IN topspace top`)]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "jn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Arzela-Ascoli.  On cball(vec 0,r/2) the rescaled functions sqrt(Q k) dE o *)
(* phi k are uniformly Lipschitz (the comparison with e = 1/2 and            *)
(* P2BK_OSA_DIST_EUCLID) and bounded at vec 0 (by M0), so a subsequence sig  *)
(* converges uniformly to some rho (P2BK_LCDATA_LIMIT); the comparison of    *)
(* distances holds along sig with errors tending to 0.                       *)
(* ========================================================================= *)

let p2bk_lclim = new_definition
 `p2bk_lclim (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
             (dE:B->real) (Q:num->real) (phi:num->real^3->B) (G0:real^3->real^3^3) (rb:real)
             (r:real) (rk:real) (rho0:real) (C:real) (sig:num->num) (rho:real^3->real) <=>
           &0 < r /\ &0 < rk /\ &0 < rho0 /\ &0 < C /\
           ball(vec 0:real^3,r) SUBSET cball(vec 0,rk) /\ rk < rb /\
           (!m n. m < n ==> sig m < sig n) /\
           (!p q. p IN cball(vec 0,r / &2) /\ q IN cball(vec 0,r / &2)
                  ==> mfd_joinable (subtopology euclidean (ball(vec 0,rb)),
                                    open_set_atlas (ball(vec 0,rb))) p q /\
                      mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                open_set_atlas (ball(vec 0,rb))) G0 p q <= C * dist(p,q)) /\
           (!e. &0 < e /\ e <= &1 / &2
                ==> ?N. !n w w'.
                       N <= n /\ w IN ball(vec 0,r) /\ w' IN ball(vec 0,r)
                       ==> mfd_joinable (subtopology euclidean (ball(vec 0,rb)),
                                         open_set_atlas (ball(vec 0,rb))) w w' /\
                           abs(sqrt(Q(sig n)) *
                               mfd_dist (top,atlas) g (phi (sig n) w) (phi (sig n) w') -
                               mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                         open_set_atlas (ball(vec 0,rb))) G0 w w')
                           <= e * mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                            open_set_atlas (ball(vec 0,rb))) G0 w w' /\
                           (!q. q IN topspace top /\
                                sqrt(Q(sig n)) * mfd_dist (top,atlas) g (phi (sig n) w) q < rho0
                                ==> ?y. y IN cball(vec 0,rk) /\ q = phi (sig n) y /\
                                        mfd_joinable (subtopology euclidean (ball(vec 0,rb)),
                                                      open_set_atlas (ball(vec 0,rb))) w y /\
                                        mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                                  open_set_atlas (ball(vec 0,rb))) G0 w y
                                        <= (&1 + e) *
                                           (sqrt(Q(sig n)) *
                                            mfd_dist (top,atlas) g (phi (sig n) w) q))) /\
           (!e. &0 < e
                ==> ?N. !n w. N <= n /\ w IN cball(vec 0,r / &2)
                              ==> abs(sqrt(Q(sig n)) * dE(phi (sig n) w) - rho w) < e)`;;

let P2BK_LCDATA_LIMIT = prove
 (`!top atlas (g:B->real^3^3) dE s1 x Q m0 M0 phi G0 r0 rb.
     p2bk_lcdata (top,atlas) g dE s1 x Q m0 M0 phi G0 r0 rb
     ==> ?r rk rho0 C (sig:num->num) (rho:real^3->real).
           p2bk_lclim (top,atlas) g dE Q phi G0 rb r rk rho0 C sig rho`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BK_LCDATA_DIST) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `rk:real` (X_CHOOSE_THEN `rho0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lim"))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_lcdata]) THEN
  SUBGOAL_THEN `metric_field (ball(vec 0:real^3,rb)) (G0:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r0)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^3,r / &2) SUBSET ball(vec 0,r)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^3,rk) SUBSET ball(vec 0,rb)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN UNDISCH_TAC `rk < rb` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^3,rb)`; `G0:real^3->real^3^3`; `cball(vec 0:real^3,r / &2)`]
    P2BK_OSA_DIST_EUCLID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; COMPACT_CBALL; CONVEX_CBALL] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eu")))] THEN
  USE_THEN "lim" (MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "k1")) THEN
  MP_TAC(ISPECL
   [`\n:num w:real^3. lift(sqrt((Q:num->real)(k1 + n)) * (dE:B->real)((phi:num->real^3->B) (k1 + n) w))`;
    `cball(vec 0:real^3,r / &2)`; `cball(vec 0:real^1,M0)`; `&3 / &2 * C`]
    ARZELA_ASCOLI_LIPSCHITZ) THEN
  REWRITE_TAC[COMPACT_CBALL; BOUNDED_CBALL] THEN BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`n:num`; `w:real^3`] THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
      EXISTS_TAC `lift(sqrt((Q:num->real)(k1 + n)) * (dE:B->real)((x:num->B) (k1 + n)))` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `vec 0:real^3` THEN ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN
        UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
        REWRITE_TAC[IN_CBALL_0; NORM_LIFT] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k1 + n:num` o check (fun th ->
          can (find_term (fun t -> try fst(dest_var t) = "m0" with Failure _ -> false))
              (concl th) && is_forall(concl th))) THEN
        STRIP_TAC THEN UNDISCH_TAC `&0 < m0` THEN
        UNDISCH_TAC `m0 <= sqrt((Q:num->real)(k1 + n)) * (dE:B->real)((x:num->B) (k1 + n))` THEN
        UNDISCH_TAC `sqrt((Q:num->real)(k1 + n)) * (dE:B->real)((x:num->B) (k1 + n)) <= M0` THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `p:real^3`; `q:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; GSYM REAL_SUB_LDISTRIB] THEN
    SUBGOAL_THEN `(p:real^3) IN ball(vec 0,r) /\ (q:real^3) IN ball(vec 0,r)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "k1" (MP_TAC o SPECL [`k1 + n:num`; `p:real^3`; `q:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
    USE_THEN "eu" (MP_TAC o SPECL [`p:real^3`; `q:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(phi:num->real^3->B) (k1 + n) p IN topspace top /\
                  (phi:num->real^3->B) (k1 + n) q IN topspace top` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC P2BK_LCDATA_IN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                            `dE:B->real`; `s1:real`; `x:num->B`; `Q:num->real`; `m0:real`;
                            `M0:real`; `G0:real^3->real^3^3`; `r0:real`; `rb:real`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET cball(vec 0,rk)` THEN
      UNDISCH_TAC `cball(vec 0:real^3,rk) SUBSET ball(vec 0,rb)` THEN
      UNDISCH_TAC `rb < r0` THEN
      UNDISCH_TAC `(p:real^3) IN ball(vec 0,r)` THEN UNDISCH_TAC `(q:real^3) IN ball(vec 0,r)` THEN
      REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN MESON_TAC[REAL_LT_TRANS];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(phi:num->real^3->B) (k1 + n) p`;
                                  `(phi:num->real^3->B) (k1 + n) q`] o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable" with Failure _ -> false))
          (concl th) && is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_var t) = "dE" with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < sqrt((Q:num->real)(k1 + n))` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt((Q:num->real)(k1 + n)) *
                mfd_dist (top,atlas) (g:B->real^3^3) ((phi:num->real^3->B) (k1 + n) p)
                  (phi (k1 + n) q)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                      open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) p q`
      ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN
      ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_BALL; RFB_OPEN_SET_RIEMANNIAN];
      ALL_TAC] THEN
    SUBGOAL_THEN `&3 / &2 * mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                                      open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) p q
                  <= &3 / &2 * (C * dist(p,q))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[dist] THEN
    UNDISCH_TAC
     `abs(sqrt((Q:num->real)(k1 + n)) *
          mfd_dist (top,atlas) (g:B->real^3^3) ((phi:num->real^3->B) (k1 + n) p) (phi (k1 + n) q) -
          mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                    open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) p q)
      <= &1 / &2 * mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                             open_set_atlas (ball(vec 0,rb))) G0 p q` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^3->real^1` (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `s:num->num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `rk:real`; `rho0:real`; `C:real`; `\n:num. (k1:num) + (s:num->num) n`;
                        `\w:real^3. drop((G:real^3->real^1) w)`] THEN
  REWRITE_TAC[p2bk_lclim] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[LT_ADD_LCANCEL] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    USE_THEN "lim" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN EXISTS_TAC `k0:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `w:real^3`; `w':real^3`] THEN STRIP_TAC THEN
    USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN UNDISCH_TAC `k0:num <= n` THEN ARITH_TAC;
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `w:real^3`] THEN STRIP_TAC THEN
    USE_THEN "N" (MP_TAC o SPECL [`n:num`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GE]; ALL_TAC] THEN
    REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP]]);;

(* ========================================================================= *)
(* Abstract limit facts for the rescaled functions Fs n -> rho (uniformly on *)
(* K): rho is 1-Lipschitz for any limit distance dS that the Fs n satisfy up *)
(* to the factor 1 + e (P2BK_RHO_LIP), and pointwise lower bounds pass to    *)
(* the limit (P2BK_RHO_LBOUND).                                              *)
(* ========================================================================= *)

let P2BK_LE_EPS2 = prove
 (`!a b. &0 <= b /\ (!e. &0 < e /\ e <= &1 / &2 ==> a <= (&1 + e) * b + &2 * e)
         ==> a <= b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (a - b) / (b + &3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN UNDISCH_TAC `b < a` THEN UNDISCH_TAC `&0 <= b` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e = min (&1 / &2) ((a - b) / (b + &3))` THEN
  SUBGOAL_THEN `&0 < e /\ e <= &1 / &2 /\ e <= (a - b) / (b + &3)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN UNDISCH_TAC `&0 < (a - b) / (b + &3)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `e * (b + &2) <= (a - b) / (b + &3) * (b + &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= b` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a - b) / (b + &3) * (b + &2) = (a - b) - (a - b) / (b + &3)` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(b + &3 = &0)` MP_TAC THENL
     [UNDISCH_TAC `&0 <= b` THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  UNDISCH_TAC `a <= (&1 + e) * b + &2 * e` THEN
  UNDISCH_TAC `e * (b + &2) <= (a - b) / (b + &3) * (b + &2)` THEN
  UNDISCH_TAC `(a - b) / (b + &3) * (b + &2) = (a - b) - (a - b) / (b + &3)` THEN
  UNDISCH_TAC `&0 < (a - b) / (b + &3)` THEN REAL_ARITH_TAC);;

let P2BK_RHO_LIP = prove
 (`!(Fs:num->real^3->real) rho (dS:real^3->real^3->real) K.
     (!e. &0 < e ==> ?N. !n w. N <= n /\ w IN K ==> abs(Fs n w - rho w) < e) /\
     (!e. &0 < e /\ e <= &1 / &2
          ==> ?N. !n w w'. N <= n /\ w IN K /\ w' IN K
                           ==> abs(Fs n w - Fs n w') <= (&1 + e) * dS w w') /\
     (!w w'. w IN K /\ w' IN K ==> &0 <= dS w w')
     ==> !w w'. w IN K /\ w' IN K ==> abs(rho w - rho w') <= dS w w'`,
  REPEAT GEN_TAC THEN INTRO_TAC "unif lip pos" THEN
  MAP_EVERY X_GEN_TAC [`w:real^3`; `w':real^3`] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BK_LE_EPS2 THEN CONJ_TAC THENL
   [USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  USE_THEN "unif" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  USE_THEN "lip" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  SUBGOAL_THEN
   `abs((Fs:num->real^3->real) (N1 + N2:num) w - rho w) < e /\
    abs((Fs:num->real^3->real) (N1 + N2:num) w' - rho w') < e /\
    abs(Fs (N1 + N2:num) w - Fs (N1 + N2) w') <= (&1 + e) * (dS:real^3->real^3->real) w w'`
    MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "N1" MATCH_MP_TAC; USE_THEN "N1" MATCH_MP_TAC; USE_THEN "N2" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REAL_ARITH_TAC]);;

let P2BK_RHO_LBOUND = prove
 (`!(Fs:num->real^3->real) rho v m.
     (!n. m <= Fs n v) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(Fs n v - rho v) < e)
     ==> m <= rho v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m - rho(v:real^3)`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `rho(v:real^3) < m` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Abstract limit of ray points.  If y n in a compact set B satisfy Fs n (y  *)
(* n) = Fs n w - t and dS w (y n) -> t, then a limit point z of the y n is a *)
(* ray point of the limit function rho: dS w z = t and rho z = rho w - t     *)
(* (P2BK_RAY_LIMIT).                                                         *)
(* ========================================================================= *)

let P2BK_REAL_EQ_EPS = prove
 (`!x. (!e. &0 < e ==> abs x < e) ==> x = &0`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `~(&0 < abs x) ==> x = &0`) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `abs x`) THEN ASM_REWRITE_TAC[REAL_LT_REFL]);;

let P2BK_RAY_LIMIT = prove
 (`!(Fs:num->real^3->real) rho (dS:real^3->real^3->real) K B C w t (y:num->real^3) N0.
     compact B /\ B SUBSET K /\ w IN K /\ &0 <= C /\
     (!e. &0 < e ==> ?N. !n v. N <= n /\ v IN K ==> abs(Fs n v - rho v) < e) /\
     (!p q. p IN K /\ q IN K ==> abs(rho p - rho q) <= dS p q) /\
     (!p q. p IN K /\ q IN K ==> dS p q <= C * dist(p,q)) /\
     (!p q r. p IN K /\ q IN K /\ r IN K ==> dS p r <= dS p q + dS q r) /\
     (!p q. p IN K /\ q IN K ==> dS p q = dS q p) /\
     (!n. N0 <= n ==> y n IN B /\ Fs n (y n) = Fs n w - t) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(dS w (y n) - t) <= e)
     ==> ?z. z IN B /\ dS w z = t /\ rho z = rho w - t`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "cB BK wK C0 unif rlip deu tri sym yB conv" THEN
  UNDISCH_TAC `compact(B:real^3->bool)` THEN REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `\n:num. (y:num->real^3) (N0 + n)`) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    USE_THEN "yB" (MP_TAC o SPEC `N0 + n:num`) THEN REWRITE_TAC[LE_ADD] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (X_CHOOSE_THEN `tau:num->num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:real^3) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. (y:num->real^3) (N0 + (tau:num->num) n) IN K /\
                    (Fs:num->real^3->real) (N0 + tau n) (y (N0 + tau n)) =
                    Fs (N0 + tau n) w - t`
    (LABEL_TAC "yK") THENL
   [GEN_TAC THEN USE_THEN "yB" (MP_TAC o SPEC `N0 + tau(n:num):num`) THEN
    REWRITE_TAC[LE_ADD] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `tau:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!e. &0 < e ==> ?J. !j. J <= j ==> (dS:real^3->real^3->real) ((y:num->real^3) ((N0:num) + (tau:num->num) j)) z < e`
    (LABEL_TAC "yz") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(((\n:num. (y:num->real^3) (N0 + n)) o tau) --> z) sequentially` THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e / (C + &1)`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= C` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `J:num` (LABEL_TAC "J")) THEN EXISTS_TAC `J:num` THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "J" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; BETA_TAC THEN DISCH_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `C * dist((y:num->real^3) (N0 + (tau:num->num) j),z)` THEN CONJ_TAC THENL
     [USE_THEN "deu" MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(C + &1) * dist((y:num->real^3) (N0 + (tau:num->num) j),z)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DIST_POS_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < C + &1` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 <= C` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `dist((y:num->real^3) (N0 + (tau:num->num) j),z) < e / (C + &1)` THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < C + &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!J N. N <= (N0:num) + (tau:num->num)(J + N)` (LABEL_TAC "big") THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `J + N:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_var t) = "tau" with Failure _ -> false)) (concl th) &&
      not(can (find_term (fun t -> try fst(dest_var t) = "y" with Failure _ -> false)) (concl th)))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN MATCH_MP_TAC P2BK_REAL_EQ_EPS THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "yz" (MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `J:num` (LABEL_TAC "J")) THEN
    USE_THEN "conv" (MP_TAC o SPEC `e / &4`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
    ABBREV_TAC `m = (N0:num) + (tau:num->num)(J + N)` THEN
    SUBGOAL_THEN `(y:num->real^3) m IN K /\ (Fs:num->real^3->real) m (y m) = Fs m w - t /\
                  (dS:real^3->real^3->real) (y m) z < e / &2 /\
                  abs(dS w (y m) - t) <= e / &4`
      STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REPEAT CONJ_TAC THENL
       [USE_THEN "yK" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `J + N:num` th)]);
        USE_THEN "yK" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `J + N:num` th)]);
        USE_THEN "J" MATCH_MP_TAC THEN ARITH_TAC;
        USE_THEN "N" MATCH_MP_TAC THEN USE_THEN "big" (fun th -> REWRITE_TAC[th])];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(dS:real^3->real^3->real) w z <= dS w (y m) + dS ((y:num->real^3) m) z /\
      dS w (y m) <= dS w z + dS z (y m) /\
      dS z (y m) = dS (y m) z`
      STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "tri" MATCH_MP_TAC; USE_THEN "tri" MATCH_MP_TAC; USE_THEN "sym" MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(dS:real^3->real^3->real) ((y:num->real^3) m) z < e / &2` THEN
    UNDISCH_TAC `abs((dS:real^3->real^3->real) w ((y:num->real^3) m) - t) <= e / &4` THEN
    UNDISCH_TAC `(dS:real^3->real^3->real) w z <= dS w ((y:num->real^3) m) + dS (y m) z` THEN
    UNDISCH_TAC `(dS:real^3->real^3->real) w ((y:num->real^3) m) <= dS w z + dS z (y m)` THEN
    UNDISCH_TAC `(dS:real^3->real^3->real) z ((y:num->real^3) m) = dS (y m) z` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN MATCH_MP_TAC P2BK_REAL_EQ_EPS THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "yz" (MP_TAC o SPEC `e / &4`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num` (LABEL_TAC "J")) THEN
  USE_THEN "unif" (MP_TAC o SPEC `e / &4`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  ABBREV_TAC `m = (N0:num) + (tau:num->num)(J + N)` THEN
  SUBGOAL_THEN `(y:num->real^3) m IN K /\ (Fs:num->real^3->real) m (y m) = Fs m w - t /\
                (dS:real^3->real^3->real) (y m) z < e / &4 /\
                abs(Fs m (y m) - rho (y m)) < e / &4 /\ abs(Fs m w - rho w) < e / &4`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `N <= m:num` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN USE_THEN "big" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    SUBGOAL_THEN `(y:num->real^3) m IN K /\ (Fs:num->real^3->real) m (y m) = Fs m w - t`
      STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN USE_THEN "yK" (fun th -> REWRITE_TAC[SPEC `J + N:num` th]); ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      EXPAND_TAC "m" THEN USE_THEN "J" MATCH_MP_TAC THEN ARITH_TAC;
      USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((rho:real^3->real) z - rho ((y:num->real^3) m)) <= (dS:real^3->real^3->real) z (y m) /\
    dS z (y m) = dS (y m) z`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [USE_THEN "rlip" MATCH_MP_TAC; USE_THEN "sym" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(Fs:num->real^3->real) m ((y:num->real^3) m) = Fs m w - t` THEN
  UNDISCH_TAC `abs((rho:real^3->real) z - rho ((y:num->real^3) m)) <=
               (dS:real^3->real^3->real) z (y m)` THEN
  UNDISCH_TAC `(dS:real^3->real^3->real) z ((y:num->real^3) m) = dS (y m) z` THEN
  UNDISCH_TAC `(dS:real^3->real^3->real) ((y:num->real^3) m) z < e / &4` THEN
  UNDISCH_TAC `abs((Fs:num->real^3->real) m w - rho w) < e / &4` THEN
  UNDISCH_TAC `abs((Fs:num->real^3->real) m ((y:num->real^3) m) - rho (y m)) < e / &4` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Abstract limit of the angle inequality.  If the comparison angles of      *)
(* admissible triangles with sides Fs n and D n satisfy the triangle         *)
(* inequality up to delta and the sides converge to those of an admissible   *)
(* limit triangle, the limit angles satisfy it up to delta                   *)
(* (P2BK_ANGLE_LIMIT).                                                       *)
(* ========================================================================= *)

let P2BK_ANGLE_LIMIT = prove
 (`!(Fs:num->real^3->real) rho (D:num->real^3->real^3->real) (dS:real^3->real^3->real)
    w y z delta.
     &0 < rho w /\ &0 < rho y /\ &0 < rho z /\
     abs(rho w - rho z) <= dS w z /\ dS w z <= rho w + rho z /\
     abs(rho w - rho y) <= dS w y /\ dS w y <= rho w + rho y /\
     abs(rho y - rho z) <= dS y z /\ dS y z <= rho y + rho z /\
     ((\n. Fs n w) ---> rho w) sequentially /\ ((\n. Fs n y) ---> rho y) sequentially /\
     ((\n. Fs n z) ---> rho z) sequentially /\
     ((\n. D n w z) ---> dS w z) sequentially /\ ((\n. D n w y) ---> dS w y) sequentially /\
     ((\n. D n y z) ---> dS y z) sequentially /\
     (?N. !n. N <= n
              ==> &0 < Fs n w /\ &0 < Fs n y /\ &0 < Fs n z /\
                  abs(Fs n w - Fs n z) <= D n w z /\ D n w z <= Fs n w + Fs n z /\
                  abs(Fs n w - Fs n y) <= D n w y /\ D n w y <= Fs n w + Fs n y /\
                  abs(Fs n y - Fs n z) <= D n y z /\ D n y z <= Fs n y + Fs n z /\
                  p2bk_cang (Fs n w) (Fs n z) (D n w z) <=
                  p2bk_cang (Fs n w) (Fs n y) (D n w y) +
                  p2bk_cang (Fs n y) (Fs n z) (D n y z) + delta)
     ==> p2bk_cang (rho w) (rho z) (dS w z) <=
         p2bk_cang (rho w) (rho y) (dS w y) + p2bk_cang (rho y) (rho z) (dS y z) + delta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  EXISTS_TAC `\n. p2bk_cang ((Fs:num->real^3->real) n w) (Fs n z)
                            ((D:num->real^3->real^3->real) n w z)` THEN
  EXISTS_TAC `\n. p2bk_cang ((Fs:num->real^3->real) n w) (Fs n y)
                            ((D:num->real^3->real^3->real) n w y) +
                  p2bk_cang (Fs n y) (Fs n z) (D n y z) + delta` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`(rho:real^3->real) w`; `(rho:real^3->real) z`; `(dS:real^3->real^3->real) w z`;
                   `\n. (Fs:num->real^3->real) n w`; `\n. (Fs:num->real^3->real) n z`;
                   `\n. (D:num->real^3->real^3->real) n w z`] P2BK_CANG_LIMIT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(rho:real^3->real) w`; `(rho:real^3->real) y`; `(dS:real^3->real^3->real) w y`;
                     `\n. (Fs:num->real^3->real) n w`; `\n. (Fs:num->real^3->real) n y`;
                     `\n. (D:num->real^3->real^3->real) n w y`] P2BK_CANG_LIMIT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
      MP_TAC(ISPECL [`(rho:real^3->real) y`; `(rho:real^3->real) z`; `(dS:real^3->real^3->real) y z`;
                     `\n. (Fs:num->real^3->real) n y`; `\n. (Fs:num->real^3->real) n z`;
                     `\n. (D:num->real^3->real^3->real) n y z`] P2BK_CANG_LIMIT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[]];
    EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* The limit function rho.  On cball(vec 0,r/2) the limit distance dS of the *)
(* open-set manifold ball(vec 0,rb) is nonnegative, symmetric and satisfies  *)
(* the triangle inequality, rho is 1-Lipschitz for it, and rho(vec 0) >= m0  *)
(* (P2BK_LCLIM_BASIC).                                                       *)
(* ========================================================================= *)

let P2BK_LCLIM_BASIC = prove
 (`!top atlas (g:B->real^3^3) dE s1 x Q m0 M0 phi G0 r0 rb r rk rho0 C sig rho.
     p2bk_lcdata (top,atlas) g dE s1 x Q m0 M0 phi G0 r0 rb /\
     p2bk_lclim (top,atlas) g dE Q phi G0 rb r rk rho0 C sig rho
     ==> (!p q. p IN cball(vec 0,r / &2) /\ q IN cball(vec 0,r / &2)
                ==> &0 <= mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                    open_set_atlas (ball(vec 0,rb))) G0 p q /\
                    mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                              open_set_atlas (ball(vec 0,rb))) G0 p q =
                    mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                              open_set_atlas (ball(vec 0,rb))) G0 q p) /\
         (!p q u. p IN cball(vec 0,r / &2) /\ q IN cball(vec 0,r / &2) /\
                  u IN cball(vec 0,r / &2)
                  ==> mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                open_set_atlas (ball(vec 0,rb))) G0 p u <=
                      mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                open_set_atlas (ball(vec 0,rb))) G0 p q +
                      mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                open_set_atlas (ball(vec 0,rb))) G0 q u) /\
         (!p q. p IN cball(vec 0,r / &2) /\ q IN cball(vec 0,r / &2)
                ==> abs(rho p - rho q) <=
                    mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                              open_set_atlas (ball(vec 0,rb))) G0 p q) /\
         m0 <= rho(vec 0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[p2bk_lclim] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "eu")
    (CONJUNCTS_THEN2 (LABEL_TAC "cmp") (LABEL_TAC "unif")))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_lcdata]) THEN
  SUBGOAL_THEN `metric_field (ball(vec 0:real^3,rb)) (G0:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r0)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology euclidean (ball(vec 0:real^3,rb)))
                          (open_set_atlas (ball(vec 0,rb))) /\
    riemannian_metric (open_set_atlas (ball(vec 0:real^3,rb))) (G0:real^3->real^3^3)`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_BALL; RFB_OPEN_SET_RIEMANNIAN]; ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^3,r / &2) SUBSET ball(vec 0,r) /\
                ball(vec 0:real^3,r) SUBSET ball(vec 0,r0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN
    UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET cball(vec 0,rk)` THEN
    UNDISCH_TAC `rk < rb` THEN UNDISCH_TAC `rb < r0` THEN
    REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. p IN cball(vec 0:real^3,r / &2) /\ q IN cball(vec 0,r / &2)
          ==> &0 <= mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                              open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) p q /\
              mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                        open_set_atlas (ball(vec 0,rb))) G0 p q =
              mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                        open_set_atlas (ball(vec 0,rb))) G0 q p`
    (LABEL_TAC "ds") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "eu" (fun th -> ASM_MESON_TAC[th]);
      MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "eu" (fun th -> ASM_MESON_TAC[th]);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\n w. sqrt((Q:num->real)((sig:num->num) n)) * (dE:B->real)((phi:num->real^3->B) ((sig:num->num) n) w)`;
      `rho:real^3->real`;
      `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),open_set_atlas (ball(vec 0,rb)))
                (G0:real^3->real^3^3)`;
      `cball(vec 0:real^3,r / &2)`] P2BK_RHO_LIP) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [USE_THEN "unif" ACCEPT_TAC;
      X_GEN_TAC `e:real` THEN STRIP_TAC THEN
      USE_THEN "cmp" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `p:real^3`; `q:real^3`] THEN STRIP_TAC THEN
      USE_THEN "N" (MP_TAC o SPECL [`n:num`; `p:real^3`; `q:real^3`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
      SUBGOAL_THEN `(phi:num->real^3->B) ((sig:num->num) n) p IN topspace top /\
                    (phi:num->real^3->B) ((sig:num->num) n) q IN topspace top` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC P2BK_LCDATA_IN THEN
        MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                              `dE:B->real`; `s1:real`; `x:num->B`; `Q:num->real`; `m0:real`;
                              `M0:real`; `G0:real^3->real^3^3`; `r0:real`; `rb:real`] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `abs((dE:B->real)((phi:num->real^3->B) ((sig:num->num) n) p) - dE(phi ((sig:num->num) n) q)) <=
        mfd_dist (top,atlas) (g:B->real^3^3) (phi ((sig:num->num) n) p) (phi ((sig:num->num) n) q)`
        ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`(phi:num->real^3->B) ((sig:num->num) n) p`;
                                     `(phi:num->real^3->B) ((sig:num->num) n) q`] o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable" with Failure _ -> false))
              (concl th) &&
          can (find_term (fun t -> try fst(dest_var t) = "dE" with Failure _ -> false)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < sqrt((Q:num->real)((sig:num->num) n))` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt((Q:num->real)((sig:num->num) n)) *
                  mfd_dist (top,atlas) (g:B->real^3^3) ((phi:num->real^3->B) ((sig:num->num) n) p)
                    (phi ((sig:num->num) n) q)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      UNDISCH_TAC
       `abs(sqrt((Q:num->real)((sig:num->num) n)) *
            mfd_dist (top,atlas) (g:B->real^3^3) ((phi:num->real^3->B) ((sig:num->num) n) p)
              (phi ((sig:num->num) n) q) -
            mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                      open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) p q)
        <= e * mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                         open_set_atlas (ball(vec 0,rb))) G0 p q` THEN
      REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "ds" (fun th -> ASM_SIMP_TAC[th])];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n w. sqrt((Q:num->real)((sig:num->num) n)) * (dE:B->real)((phi:num->real^3->B) ((sig:num->num) n) w)`;
    `rho:real^3->real`; `vec 0:real^3`; `m0:real`] P2BK_RHO_LBOUND) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "unif" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN USE_THEN "N" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC]);;

(* Ray points of rho near vec 0: limits of the preimages of the ray points  *)
(* of the end-cone data (P2BK_RAY_LIMIT).                                   *)

let P2BK_LCLIM_RAY = prove
 (`!top atlas (g:B->real^3^3) dE s1 x Q m0 M0 phi G0 r0 rb r rk rho0 C sig rho w.
     p2bk_lcdata (top,atlas) g dE s1 x Q m0 M0 phi G0 r0 rb /\
     p2bk_lclim (top,atlas) g dE Q phi G0 rb r rk rho0 C sig rho /\
     w IN ball(vec 0,min (r / &4) (m0 / (&8 * C)))
     ==> ?r'. &0 < r' /\
              !t. &0 < t /\ t < r'
                  ==> ?y. y IN ball(vec 0,min (r / &4) (m0 / (&8 * C))) /\
                          mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                    open_set_atlas (ball(vec 0,rb))) G0 w y = t /\
                          rho y = rho w - t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `dE:B->real`; `s1:real`; `x:num->B`; `Q:num->real`; `m0:real`; `M0:real`;
                 `phi:num->real^3->B`; `G0:real^3->real^3^3`; `r0:real`; `rb:real`; `r:real`;
                 `rk:real`; `rho0:real`; `C:real`; `sig:num->num`; `rho:real^3->real`]
    P2BK_LCLIM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ds") (CONJUNCTS_THEN2 (LABEL_TAC "tri")
    (CONJUNCTS_THEN2 (LABEL_TAC "rlip") ASSUME_TAC))) THEN
  UNDISCH_TAC `p2bk_lclim (top,atlas) (g:B->real^3^3) dE Q phi G0 rb r rk rho0 C sig rho` THEN
  REWRITE_TAC[p2bk_lclim] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sigm") (CONJUNCTS_THEN2 (LABEL_TAC "eu")
    (CONJUNCTS_THEN2 (LABEL_TAC "cmp") (LABEL_TAC "unif")))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_lcdata]) THEN
  SUBGOAL_THEN `metric_field (ball(vec 0:real^3,rb)) (G0:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r0)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `rf = min (r / &4) (m0 / (&8 * C))` THEN
  SUBGOAL_THEN `&0 < rf /\ rf <= r / &4 /\ C * rf <= m0 / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rf" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * m0 / (&8 * C)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,rf) SUBSET cball(vec 0,r / &2) /\
                cball(vec 0:real^3,r / &2) SUBSET ball(vec 0,r) /\
                ball(vec 0:real^3,r) SUBSET ball(vec 0,r0) /\
                cball(vec 0:real^3,r / &2) SUBSET ball(vec 0,rb)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET cball(vec 0,rk)` THEN
    REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN
    UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `rf <= r / &4` THEN UNDISCH_TAC `rk < rb` THEN
    UNDISCH_TAC `rb < r0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN cball(vec 0,r / &2)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &8 * m0 <= (rho:real^3->real) w` ASSUME_TAC THENL
   [USE_THEN "rlip" (MP_TAC o SPECL [`vec 0:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "eu" (MP_TAC o SPECL [`vec 0:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `C * dist(vec 0:real^3,w) <= m0 / &8` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * rf` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^3) IN ball(vec 0,rf)` THEN
      REWRITE_TAC[IN_BALL_0; DIST_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `m0 <= (rho:real^3->real)(vec 0)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,rb))`;
                 `open_set_atlas (ball(vec 0:real^3,rb))`; `G0:real^3->real^3^3`;
                 `ball(vec 0:real^3,rb)`; `\z:real^3. z`; `w:real^3`]
    MFD_DIST_LOCAL_EUCLIDEAN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN; OPEN_SET_ATLAS;
                 OPEN_BALL; RFB_OPEN_SET_RIEMANNIAN; RFB_OPEN_SET_ATLAS_CASES] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_ID] THEN
  DISCH_THEN(X_CHOOSE_THEN `rw:real` (X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `c2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "in") (LABEL_TAC "out"))))))))) THEN
  ABBREV_TAC `del = rf - norm(w:real^3)` THEN
  SUBGOAL_THEN `&0 < del` ASSUME_TAC THENL
   [EXPAND_TAC "del" THEN UNDISCH_TAC `(w:real^3) IN ball(vec 0,rf)` THEN
    REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(w:real^3,&3 / &4 * del) SUBSET ball(vec 0,rf)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_BALLS; DIST_0] THEN DISJ1_TAC THEN
    UNDISCH_TAC `rf - norm(w:real^3) = del` THEN UNDISCH_TAC `&0 < del` THEN
    REWRITE_TAC[DIST_SYM; DIST_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (min (rho0 / &2) (m0 / &8)) (c1 * min rw del / &2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < rho0` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < m0` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < rw` THEN UNDISCH_TAC `&0 < del` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?N0 (y:num->real^3). !n. N0 <= n
        ==> y n IN cball(w,&3 / &4 * del) /\
            sqrt((Q:num->real)((sig:num->num) n)) *
            (dE:B->real)((phi:num->real^3->B) (sig n) (y n)) =
            sqrt(Q(sig n)) * dE(phi (sig n) w) - t /\
            sqrt(Q(sig n)) *
            mfd_dist (top,atlas) (g:B->real^3^3) (phi (sig n) w) (phi (sig n) (y n)) = t`
    (X_CHOOSE_THEN `N0:num` (X_CHOOSE_THEN `y:num->real^3` (LABEL_TAC "yn"))) THENL
   [USE_THEN "unif" (MP_TAC o SPEC `m0 / &8`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `&0 < m0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Nu:num` (LABEL_TAC "Nu")) THEN
    USE_THEN "cmp" (MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `Nc:num` (LABEL_TAC "Nc")) THEN
    SUBGOAL_THEN `&0 < (rho:real^3->real) w + m0` ASSUME_TAC THENL
     [UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) w` THEN UNDISCH_TAC `&0 < m0` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(s1 * m0) / ((rho:real^3->real) w + m0)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_var t) = "x" with Failure _ -> false)) (concl th) &&
      not(can (find_term (fun t -> try fst(dest_var t) = "M0" with Failure _ -> false)) (concl th)) &&
      not(can (find_term (fun t -> try fst(dest_var t) = "phi" with Failure _ -> false)) (concl th)))) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `kx:num` (LABEL_TAC "kx")) THEN
    EXISTS_TAC `Nu + Nc + kx:num` THEN
    REWRITE_TAC[GSYM SKOLEM_THM] THEN REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `Nu <= n /\ Nc <= n /\ kx <= (sig:num->num) n` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `sig:num->num` MONOTONE_BIGGER) THEN
      USE_THEN "sigm" (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN UNDISCH_TAC `Nu + Nc + kx <= n:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `p = (phi:num->real^3->B) ((sig:num->num) n) w` THEN
    ABBREV_TAC `sq = sqrt((Q:num->real)((sig:num->num) n))` THEN
    SUBGOAL_THEN `&0 < sq` ASSUME_TAC THENL
     [EXPAND_TAC "sq" THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(p:B) IN topspace top` ASSUME_TAC THENL
     [EXPAND_TAC "p" THEN MATCH_MP_TAC P2BK_LCDATA_IN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                            `dE:B->real`; `s1:real`; `x:num->B`; `Q:num->real`; `m0:real`;
                            `M0:real`; `G0:real^3->real^3^3`; `r0:real`; `rb:real`] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(sq * (dE:B->real) p - (rho:real^3->real) w) < m0 / &8` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["sq"; "p"] THEN USE_THEN "Nu" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `m0 <= sq * (dE:B->real)((x:num->B) ((sig:num->num) n)) /\
                  dE(x(sig n)) < (s1 * m0) / ((rho:real^3->real) w + m0)`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "sq" THEN ASM_MESON_TAC[];
        USE_THEN "kx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(rho:real^3->real) w + m0 < sq * s1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `m0:real` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `m0 * ((rho:real^3->real) w + m0) <=
        (sq * (dE:B->real)((x:num->B) ((sig:num->num) n))) * (rho w + m0)`
        ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      SUBGOAL_THEN
       `sq * ((dE:B->real)((x:num->B) ((sig:num->num) n)) * ((rho:real^3->real) w + m0)) <
        sq * (s1 * m0)`
        ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(dE:B->real)((x:num->B) ((sig:num->num) n)) <
                     (s1 * m0) / ((rho:real^3->real) w + m0)` THEN
        SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < (rho:real^3->real) w + m0`];
        ALL_TAC] THEN
      UNDISCH_TAC
       `m0 * ((rho:real^3->real) w + m0) <=
        (sq * (dE:B->real)((x:num->B) ((sig:num->num) n))) * (rho w + m0)` THEN
      UNDISCH_TAC
       `sq * ((dE:B->real)((x:num->B) ((sig:num->num) n)) * ((rho:real^3->real) w + m0)) <
        sq * (s1 * m0)` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(dE:B->real) p <= s1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `sq:real` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs(sq * (dE:B->real) p - (rho:real^3->real) w) < m0 / &8` THEN
      UNDISCH_TAC `(rho:real^3->real) w + m0 < sq * s1` THEN UNDISCH_TAC `&0 < m0` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < t / sq /\ t / sq <= (dE:B->real) p / &2` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN
      UNDISCH_TAC `abs(sq * (dE:B->real) p - (rho:real^3->real) w) < m0 / &8` THEN
      UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) w` THEN UNDISCH_TAC `t < m0 / &8` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:B`; `t / sq`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_var t) = "s1" with Failure _ -> false)) (concl th) &&
      not(can (find_term (fun t -> try fst(dest_var t) = "delta" with Failure _ -> false)) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `zz:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `sq * mfd_dist (top,atlas) (g:B->real^3^3) p zz = t` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < sq` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    USE_THEN "Nc" (MP_TAC o SPECL [`n:num`; `w:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `zz:B` o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[ASSUME `(phi:num->real^3->B) ((sig:num->num) n) w = p`;
                ASSUME `sqrt((Q:num->real)((sig:num->num) n)) = sq`;
                ASSUME `sq * mfd_dist (top,atlas) (g:B->real^3^3) p zz = t`;
                ASSUME `(zz:B) IN topspace top`] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `t < rho0 / &2` THEN UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `yy:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `yy:real^3` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `(dE:B->real) zz = dE p - t / sq` THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `&0 < sq` THEN CONV_TAC REAL_FIELD] THEN
    SUBGOAL_THEN
     `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w yy
      < &3 / &4 * (c1 * min rw del)`
      ASSUME_TAC THENL
     [UNDISCH_TAC
       `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                  open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w yy <=
        &3 / &2 * t` THEN
      UNDISCH_TAC `t < c1 * min rw del / &2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c1 * min rw del <= c1 * rw /\ c1 * min rw del <= c1 * del`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      UNDISCH_TAC `&0 < c1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(yy:real^3) IN ball(vec 0,rb) /\ yy IN ball(w,rw)` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      USE_THEN "out" (MP_TAC o SPEC `yy:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC
       `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                  open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w yy
        < &3 / &4 * (c1 * min rw del)` THEN
      UNDISCH_TAC `c1 * min rw del <= c1 * rw` THEN
      SUBGOAL_THEN `&0 < c1 * rw` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "in" (MP_TAC o SPEC `yy:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[IN_CBALL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `c1:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c1 * dist(w:real^3,yy) <=
                 mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                           open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w yy` THEN
    UNDISCH_TAC
     `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w yy
      < &3 / &4 * (c1 * min rw del)` THEN
    UNDISCH_TAC `c1 * min rw del <= c1 * del` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n w. sqrt((Q:num->real)((sig:num->num) n)) *
           (dE:B->real)((phi:num->real^3->B) (sig n) w)`;
    `rho:real^3->real`;
    `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),open_set_atlas (ball(vec 0,rb)))
              (G0:real^3->real^3^3)`;
    `cball(vec 0:real^3,r / &2)`; `cball(w:real^3,&3 / &4 * del)`; `C:real`; `w:real^3`;
    `t:real`; `y:num->real^3`; `N0:num`] P2BK_RAY_LIMIT) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL];
      MAP_EVERY UNDISCH_TAC [`cball(w:real^3,&3 / &4 * del) SUBSET ball(vec 0,rf)`;
                             `ball(vec 0:real^3,rf) SUBSET cball(vec 0,r / &2)`] THEN
      SET_TAC[];
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC;
      USE_THEN "unif" ACCEPT_TAC;
      USE_THEN "rlip" ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`p:real^3`; `q:real^3`] THEN STRIP_TAC THEN
      USE_THEN "eu" (MP_TAC o SPECL [`p:real^3`; `q:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "tri" ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`p:real^3`; `q:real^3`] THEN STRIP_TAC THEN
      USE_THEN "ds" (MP_TAC o SPECL [`p:real^3`; `q:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN USE_THEN "yn" (MP_TAC o SPEC `n:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ABBREV_TAC `e1 = min (&1 / &2) (e / (&2 * t))` THEN
    SUBGOAL_THEN `&0 < e1 /\ e1 <= &1 / &2 /\ e1 <= e / (&2 * t)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "e1" THEN
      SUBGOAL_THEN `&0 < e / (&2 * t)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "cmp" (MP_TAC o SPEC `e1:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Nk:num` (LABEL_TAC "Nk")) THEN
    EXISTS_TAC `Nk + N0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "yn" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `Nk + N0 <= n:num` THEN ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(y:num->real^3) n IN ball(vec 0,r) /\ (y:num->real^3) n IN cball(vec 0,r / &2) /\
                  (w:real^3) IN ball(vec 0,r)`
      STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(y:num->real^3) n IN cball(w,&3 / &4 * del)`;
        `cball(w:real^3,&3 / &4 * del) SUBSET ball(vec 0,rf)`;
        `ball(vec 0:real^3,rf) SUBSET cball(vec 0,r / &2)`;
        `cball(vec 0:real^3,r / &2) SUBSET ball(vec 0,r)`; `(w:real^3) IN ball(vec 0,rf)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "Nk" (MP_TAC o SPECL [`n:num`; `w:real^3`; `(y:num->real^3) n`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `Nk + N0 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `dd = mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                               open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w
                      ((y:num->real^3) n)` THEN
    SUBGOAL_THEN `&0 <= dd` ASSUME_TAC THENL
     [EXPAND_TAC "dd" THEN USE_THEN "ds" (MP_TAC o SPECL [`w:real^3`; `(y:num->real^3) n`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `e1 * dd <= &1 / &2 * dd` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dd <= &2 * t` ASSUME_TAC THENL
     [UNDISCH_TAC `abs(t - dd) <= e1 * dd` THEN UNDISCH_TAC `e1 * dd <= &1 / &2 * dd` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `e1 * dd <= e / (&2 * t) * (&2 * t)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `e / (&2 * t) * (&2 * t) = e` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    UNDISCH_TAC `abs(t - dd) <= e1 * dd` THEN
    UNDISCH_TAC `e1 * dd <= e / (&2 * t) * (&2 * t)` THEN
    UNDISCH_TAC `e / (&2 * t) * (&2 * t) = e` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(z:real^3) IN cball(w,&3 / &4 * del)`;
                           `cball(w:real^3,&3 / &4 * del) SUBSET ball(vec 0,rf)`] THEN
    SET_TAC[]]);;

(* Along sig, points with a bounded rescaled dE are eventually near the end. *)

let P2BK_LCDATA_DE_SMALL = prove
 (`!top atlas (g:B->real^3^3) dE s1 x Q m0 M0 phi G0 r0 rb (sig:num->num) Rb s.
     p2bk_lcdata (top,atlas) g dE s1 x Q m0 M0 phi G0 r0 rb /\
     (!m n. m < n ==> sig m < sig n) /\ &0 < Rb /\ &0 < s
     ==> ?N. !n v. N <= n /\ sqrt(Q(sig n)) * dE(phi (sig n) v) <= Rb
                   ==> dE(phi (sig n) v) <= s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_lcdata]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(s * m0) / Rb` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_var t) = "x" with Failure _ -> false)) (concl th) &&
    not(can (find_term (fun t -> try fst(dest_var t) = "M0" with Failure _ -> false)) (concl th)) &&
    not(can (find_term (fun t -> try fst(dest_var t) = "phi" with Failure _ -> false)) (concl th)))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kx:num` (LABEL_TAC "kx")) THEN EXISTS_TAC `kx:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `v:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `kx <= (sig:num->num) n` ASSUME_TAC THENL
   [MP_TAC(ISPEC `sig:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN UNDISCH_TAC `kx <= n:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `sq = sqrt((Q:num->real)((sig:num->num) n))` THEN
  SUBGOAL_THEN `&0 < sq` ASSUME_TAC THENL
   [EXPAND_TAC "sq" THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `m0 <= sq * (dE:B->real)((x:num->B) ((sig:num->num) n)) /\
                dE(x(sig n)) < (s * m0) / Rb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "sq" THEN ASM_MESON_TAC[];
      USE_THEN "kx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Rb < sq * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `m0:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `m0 * Rb <= (sq * (dE:B->real)((x:num->B) ((sig:num->num) n))) * Rb`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `sq * ((dE:B->real)((x:num->B) ((sig:num->num) n)) * Rb) < sq * (s * m0)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(dE:B->real)((x:num->B) ((sig:num->num) n)) < (s * m0) / Rb` THEN
      SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < Rb`];
      ALL_TAC] THEN
    UNDISCH_TAC `m0 * Rb <= (sq * (dE:B->real)((x:num->B) ((sig:num->num) n))) * Rb` THEN
    UNDISCH_TAC `sq * ((dE:B->real)((x:num->B) ((sig:num->num) n)) * Rb) < sq * (s * m0)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `sq:real` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `sq * (dE:B->real)((phi:num->real^3->B) ((sig:num->num) n) v) <= Rb` THEN
  UNDISCH_TAC `Rb < sq * s` THEN REAL_ARITH_TAC);;

let P2BK_LE_ADD_EPS = prove
 (`!a b c. (!d. &0 < d ==> a <= b + c + d) ==> a <= b + c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a - (b + c)) / &2`) THEN
  UNDISCH_TAC `b + c < a` THEN REAL_ARITH_TAC);;

(* The exact triangle inequality of the limit comparison angles near vec 0. *)

let P2BK_LCLIM_ANGLE = prove
 (`!top atlas (g:B->real^3^3) dE s1 x Q m0 M0 phi G0 r0 rb r rk rho0 C sig rho w y z.
     p2bk_lcdata (top,atlas) g dE s1 x Q m0 M0 phi G0 r0 rb /\
     p2bk_lclim (top,atlas) g dE Q phi G0 rb r rk rho0 C sig rho /\
     w IN ball(vec 0,min (r / &4) (m0 / (&8 * C))) /\
     y IN ball(vec 0,min (r / &4) (m0 / (&8 * C))) /\
     z IN ball(vec 0,min (r / &4) (m0 / (&8 * C)))
     ==> p2bk_cang (rho w) (rho z)
           (mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                      open_set_atlas (ball(vec 0,rb))) G0 w z) <=
         p2bk_cang (rho w) (rho y)
           (mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                      open_set_atlas (ball(vec 0,rb))) G0 w y) +
         p2bk_cang (rho y) (rho z)
           (mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                      open_set_atlas (ball(vec 0,rb))) G0 y z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `dE:B->real`; `s1:real`; `x:num->B`; `Q:num->real`; `m0:real`; `M0:real`;
                 `phi:num->real^3->B`; `G0:real^3->real^3^3`; `r0:real`; `rb:real`; `r:real`;
                 `rk:real`; `rho0:real`; `C:real`; `sig:num->num`; `rho:real^3->real`]
    P2BK_LCLIM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ds") (CONJUNCTS_THEN2 (LABEL_TAC "tri")
    (CONJUNCTS_THEN2 (LABEL_TAC "rlip") ASSUME_TAC))) THEN
  UNDISCH_TAC `p2bk_lclim (top,atlas) (g:B->real^3^3) dE Q phi G0 rb r rk rho0 C sig rho` THEN
  REWRITE_TAC[p2bk_lclim] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sigm") (CONJUNCTS_THEN2 (LABEL_TAC "eu")
    (CONJUNCTS_THEN2 (LABEL_TAC "cmp") (LABEL_TAC "unif")))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_lcdata]) THEN
  ABBREV_TAC `rf = min (r / &4) (m0 / (&8 * C))` THEN
  SUBGOAL_THEN `&0 < rf /\ rf <= r / &4 /\ C * rf <= m0 / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rf" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * m0 / (&8 * C)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,rf) SUBSET cball(vec 0,r / &2) /\
                cball(vec 0:real^3,r / &2) SUBSET ball(vec 0,r) /\
                ball(vec 0:real^3,r) SUBSET ball(vec 0,r0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET cball(vec 0,rk)` THEN
    REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN
    UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `rf <= r / &4` THEN UNDISCH_TAC `rk < rb` THEN
    UNDISCH_TAC `rb < r0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* pointwise facts on ball(vec 0,rf) *)
  SUBGOAL_THEN
   `!v. v IN ball(vec 0:real^3,rf)
        ==> v IN cball(vec 0,r / &2) /\ v IN ball(vec 0,r) /\ &7 / &8 * m0 <= (rho:real^3->real) v`
    (LABEL_TAC "pt") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^3) IN cball(vec 0,r / &2) /\ v IN ball(vec 0,r)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "rlip" (MP_TAC o SPECL [`vec 0:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "eu" (MP_TAC o SPECL [`vec 0:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `C * dist(vec 0:real^3,v) <= m0 / &8` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * rf` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(v:real^3) IN ball(vec 0,rf)` THEN
      REWRITE_TAC[IN_BALL_0; DIST_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `m0 <= (rho:real^3->real)(vec 0)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v v'. v IN ball(vec 0:real^3,rf) /\ v' IN ball(vec 0,rf)
           ==> mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                         open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) v v' <= m0 / &4`
    (LABEL_TAC "dsm") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "eu" (MP_TAC o SPECL [`v:real^3`; `v':real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * dist(v:real^3,v')` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * (&2 * rf)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(v:real^3) IN ball(vec 0,rf)` THEN UNDISCH_TAC `(v':real^3) IN ball(vec 0,rf)` THEN
      REWRITE_TAC[IN_BALL_0] THEN CONV_TAC NORM_ARITH;
      UNDISCH_TAC `C * rf <= m0 / &8` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < (rho:real^3->real) w /\ &0 < rho y /\ &0 < rho z /\
    abs(rho w - rho z) <= mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                                    open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w z /\
    mfd_dist (subtopology euclidean (ball(vec 0,rb)),open_set_atlas (ball(vec 0,rb))) G0 w z
      <= rho w + rho z /\
    abs(rho w - rho y) <= mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                    open_set_atlas (ball(vec 0,rb))) G0 w y /\
    mfd_dist (subtopology euclidean (ball(vec 0,rb)),open_set_atlas (ball(vec 0,rb))) G0 w y
      <= rho w + rho y /\
    abs(rho y - rho z) <= mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                    open_set_atlas (ball(vec 0,rb))) G0 y z /\
    mfd_dist (subtopology euclidean (ball(vec 0,rb)),open_set_atlas (ball(vec 0,rb))) G0 y z
      <= rho y + rho z`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(w:real^3) IN cball(vec 0,r / &2) /\ (y:real^3) IN cball(vec 0,r / &2) /\
                  (z:real^3) IN cball(vec 0,r / &2)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&7 / &8 * m0 <= (rho:real^3->real) w /\ &7 / &8 * m0 <= rho y /\
                  &7 / &8 * m0 <= rho z` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "pt" (MP_TAC o SPEC `w:real^3`);
        USE_THEN "pt" (MP_TAC o SPEC `y:real^3`);
        USE_THEN "pt" (MP_TAC o SPEC `z:real^3`)] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]; ASM_REWRITE_TAC[]; SIMP_TAC[];
                      ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w z <= m0 / &4 /\
      mfd_dist (subtopology euclidean (ball(vec 0,rb)),open_set_atlas (ball(vec 0,rb))) G0 w y
        <= m0 / &4 /\
      mfd_dist (subtopology euclidean (ball(vec 0,rb)),open_set_atlas (ball(vec 0,rb))) G0 y z
        <= m0 / &4 /\
      abs((rho:real^3->real) w - rho z) <=
        mfd_dist (subtopology euclidean (ball(vec 0,rb)),open_set_atlas (ball(vec 0,rb))) G0 w z /\
      abs(rho w - rho y) <=
        mfd_dist (subtopology euclidean (ball(vec 0,rb)),open_set_atlas (ball(vec 0,rb))) G0 w y /\
      abs(rho y - rho z) <=
        mfd_dist (subtopology euclidean (ball(vec 0,rb)),open_set_atlas (ball(vec 0,rb))) G0 y z`
      STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "dsm" MATCH_MP_TAC; USE_THEN "dsm" MATCH_MP_TAC; USE_THEN "dsm" MATCH_MP_TAC;
        USE_THEN "rlip" MATCH_MP_TAC; USE_THEN "rlip" MATCH_MP_TAC; USE_THEN "rlip" MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < m0` THEN UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) w` THEN
    UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) y` THEN
    UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) z` THEN
    UNDISCH_TAC `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                           open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w z <= m0 / &4` THEN
    UNDISCH_TAC `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                           open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w y <= m0 / &4` THEN
    UNDISCH_TAC `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                           open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) y z <= m0 / &4` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN ball(vec 0:real^3,rf)
        ==> ((\n. sqrt((Q:num->real)((sig:num->num) n)) *
                  (dE:B->real)((phi:num->real^3->B) (sig n) v)) ---> (rho:real^3->real) v)
            sequentially`
    (LABEL_TAC "Fl") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "unif" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pt" (MP_TAC o SPEC `v:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. p IN ball(vec 0:real^3,rf) /\ q IN ball(vec 0,rf)
          ==> ((\n. sqrt((Q:num->real)((sig:num->num) n)) *
                    mfd_dist (top,atlas) (g:B->real^3^3) ((phi:num->real^3->B) (sig n) p)
                      (phi (sig n) q)) --->
               mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                         open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) p q)
              sequentially`
    (LABEL_TAC "Dl") THENL
   [MAP_EVERY X_GEN_TAC [`p:real^3`; `q:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ABBREV_TAC `dpq = mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                                open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) p q` THEN
    SUBGOAL_THEN `&0 <= dpq` ASSUME_TAC THENL
     [EXPAND_TAC "dpq" THEN USE_THEN "ds" (MP_TAC o SPECL [`p:real^3`; `q:real^3`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    ABBREV_TAC `e1 = min (&1 / &2) (e / (dpq + &1))` THEN
    SUBGOAL_THEN `&0 < e1 /\ e1 <= &1 / &2 /\ e1 * (dpq + &1) <= e` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < e / (dpq + &1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= dpq` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [EXPAND_TAC "e1" THEN UNDISCH_TAC `&0 < e / (dpq + &1)` THEN REAL_ARITH_TAC;
        EXPAND_TAC "e1" THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / (dpq + &1) * (dpq + &1)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
           [EXPAND_TAC "e1" THEN REAL_ARITH_TAC; UNDISCH_TAC `&0 <= dpq` THEN REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 <= dpq` THEN CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    USE_THEN "cmp" (MP_TAC o SPEC `e1:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o SPECL [`n:num`; `p:real^3`; `q:real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `e1 * dpq < e` MP_TAC THENL
     [UNDISCH_TAC `e1 * (dpq + &1) <= e` THEN UNDISCH_TAC `&0 < e1` THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BK_LE_ADD_EPS THEN X_GEN_TAC `delta:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\n w. sqrt((Q:num->real)((sig:num->num) n)) *
           (dE:B->real)((phi:num->real^3->B) (sig n) w)`;
    `rho:real^3->real`;
    `\n p q. sqrt((Q:num->real)((sig:num->num) n)) *
             mfd_dist (top,atlas) (g:B->real^3^3) ((phi:num->real^3->B) (sig n) p)
               (phi (sig n) q)`;
    `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),open_set_atlas (ball(vec 0,rb)))
              (G0:real^3->real^3^3)`;
    `w:real^3`; `y:real^3`; `z:real^3`; `delta:real`] P2BK_ANGLE_LIMIT) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "Fl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "Fl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "Fl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "Dl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "Dl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "Dl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `delta:real` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "p2bk_cang" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ang"))) THEN
  USE_THEN "unif" (MP_TAC o SPEC `m0 / &8`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0 < m0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nu:num` (LABEL_TAC "Nu")) THEN
  USE_THEN "cmp" (MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `Nc:num` (LABEL_TAC "Nc")) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `dE:B->real`; `s1:real`; `x:num->B`; `Q:num->real`; `m0:real`; `M0:real`;
                 `phi:num->real^3->B`; `G0:real^3->real^3^3`; `r0:real`; `rb:real`;
                 `sig:num->num`; `(rho:real^3->real) w + rho y + rho z + m0`; `s0:real`]
    P2BK_LCDATA_DE_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < (rho:real^3->real) w` THEN UNDISCH_TAC `&0 < (rho:real^3->real) y` THEN
    UNDISCH_TAC `&0 < (rho:real^3->real) z` THEN UNDISCH_TAC `&0 < m0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nd:num` (LABEL_TAC "Nd")) THEN
  EXISTS_TAC `Nu + Nc + Nd:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `Nu <= n /\ Nc <= n /\ Nd <= n:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `Nu + Nc + Nd <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `sq = sqrt((Q:num->real)((sig:num->num) n))` THEN
  SUBGOAL_THEN `&0 < sq` ASSUME_TAC THENL
   [EXPAND_TAC "sq" THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN ball(vec 0:real^3,rf)
        ==> abs(sq * (dE:B->real)((phi:num->real^3->B) ((sig:num->num) n) v) - (rho:real^3->real) v)
            < m0 / &8 /\
            dE(phi (sig n) v) <= s0 /\ phi (sig n) v IN topspace top`
    (LABEL_TAC "pp") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^3) IN cball(vec 0,r / &2) /\ v IN ball(vec 0,r0)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `abs(sq * (dE:B->real)((phi:num->real^3->B) ((sig:num->num) n) v) -
                      (rho:real^3->real) v) < m0 / &8`
      ASSUME_TAC THENL
     [EXPAND_TAC "sq" THEN USE_THEN "Nu" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(rho:real^3->real) v <= rho w + m0 / &4` ASSUME_TAC THENL
     [SUBGOAL_THEN
       `abs((rho:real^3->real) v - rho w) <=
        mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                  open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) v w /\
        mfd_dist (subtopology euclidean (ball(vec 0,rb)),open_set_atlas (ball(vec 0,rb))) G0 v w
        <= m0 / &4` MP_TAC THENL
       [CONJ_TAC THENL [USE_THEN "rlip" MATCH_MP_TAC; USE_THEN "dsm" MATCH_MP_TAC] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "Nd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs(sq * (dE:B->real)((phi:num->real^3->B) ((sig:num->num) n) v) -
                       (rho:real^3->real) v) < m0 / &8` THEN
      UNDISCH_TAC `(rho:real^3->real) v <= rho w + m0 / &4` THEN
      UNDISCH_TAC `&0 < (rho:real^3->real) y` THEN UNDISCH_TAC `&0 < (rho:real^3->real) z` THEN
      UNDISCH_TAC `&0 < m0` THEN EXPAND_TAC "sq" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P2BK_LCDATA_IN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                            `dE:B->real`; `s1:real`; `x:num->B`; `Q:num->real`; `m0:real`;
                            `M0:real`; `G0:real^3->real^3^3`; `r0:real`; `rb:real`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. p IN ball(vec 0:real^3,rf) /\ q IN ball(vec 0,rf)
          ==> abs(sq * mfd_dist (top,atlas) (g:B->real^3^3) ((phi:num->real^3->B) ((sig:num->num) n) p)
                         (phi (sig n) q) -
                  mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                            open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) p q)
              <= &1 / &2 * mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                     open_set_atlas (ball(vec 0,rb))) G0 p q /\
              abs((dE:B->real)(phi (sig n) p) - dE(phi (sig n) q)) <=
              mfd_dist (top,atlas) g (phi (sig n) p) (phi (sig n) q)`
    (LABEL_TAC "pq") THENL
   [MAP_EVERY X_GEN_TAC [`p:real^3`; `q:real^3`] THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "Nc" (MP_TAC o SPECL [`n:num`; `p:real^3`; `q:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "sq" THEN SIMP_TAC[];
      USE_THEN "pp" (MP_TAC o SPEC `p:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "pp" (MP_TAC o SPEC `q:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(phi:num->real^3->B) ((sig:num->num) n) p`;
                                    `(phi:num->real^3->B) ((sig:num->num) n) q`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable" with Failure _ -> false))
            (concl th) &&
        can (find_term (fun t -> try fst(dest_var t) = "dE" with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  USE_THEN "pp" (MP_TAC o SPEC `w:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "pp" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "pp" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "pq" (MP_TAC o SPECL [`w:real^3`; `z:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "pq" (MP_TAC o SPECL [`w:real^3`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "pq" (MP_TAC o SPECL [`y:real^3`; `z:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&7 / &8 * m0 <= (rho:real^3->real) w /\ &7 / &8 * m0 <= rho y /\
                &7 / &8 * m0 <= rho z` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "pt" (MP_TAC o SPEC `w:real^3`);
      USE_THEN "pt" (MP_TAC o SPEC `y:real^3`);
      USE_THEN "pt" (MP_TAC o SPEC `z:real^3`)] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]; ASM_REWRITE_TAC[]; SIMP_TAC[];
                    ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
              open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w z <= m0 / &4 /\
    mfd_dist (subtopology euclidean (ball(vec 0,rb)),open_set_atlas (ball(vec 0,rb))) G0 w y
      <= m0 / &4 /\
    mfd_dist (subtopology euclidean (ball(vec 0,rb)),open_set_atlas (ball(vec 0,rb))) G0 y z
      <= m0 / &4`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "dsm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `a = (phi:num->real^3->B) ((sig:num->num) n) w` THEN
  ABBREV_TAC `b = (phi:num->real^3->B) ((sig:num->num) n) y` THEN
  ABBREV_TAC `c = (phi:num->real^3->B) ((sig:num->num) n) z` THEN
  SUBGOAL_THEN
   `abs(sq * (dE:B->real) a - sq * dE c) <= sq * mfd_dist (top,atlas) (g:B->real^3^3) a c /\
    abs(sq * dE a - sq * dE b) <= sq * mfd_dist (top,atlas) g a b /\
    abs(sq * dE b - sq * dE c) <= sq * mfd_dist (top,atlas) g b c`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_LMUL_EQ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[P2BK_CANG_SCALE] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `abs(sq * (dE:B->real) a - (rho:real^3->real) w) < m0 / &8` THEN
    UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) w` THEN UNDISCH_TAC `&0 < m0` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `abs(sq * (dE:B->real) b - (rho:real^3->real) y) < m0 / &8` THEN
    UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) y` THEN UNDISCH_TAC `&0 < m0` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `abs(sq * (dE:B->real) c - (rho:real^3->real) z) < m0 / &8` THEN
    UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) z` THEN UNDISCH_TAC `&0 < m0` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `abs(sq * mfd_dist (top,atlas) (g:B->real^3^3) a c -
                     mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                               open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w z)
                 <= &1 / &2 * mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                        open_set_atlas (ball(vec 0,rb))) G0 w z` THEN
    UNDISCH_TAC `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                           open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w z <= m0 / &4` THEN
    UNDISCH_TAC `abs(sq * (dE:B->real) a - (rho:real^3->real) w) < m0 / &8` THEN
    UNDISCH_TAC `abs(sq * (dE:B->real) c - (rho:real^3->real) z) < m0 / &8` THEN
    UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) w` THEN
    UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) z` THEN UNDISCH_TAC `&0 < m0` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `abs(sq * mfd_dist (top,atlas) (g:B->real^3^3) a b -
                     mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                               open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w y)
                 <= &1 / &2 * mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                        open_set_atlas (ball(vec 0,rb))) G0 w y` THEN
    UNDISCH_TAC `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                           open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w y <= m0 / &4` THEN
    UNDISCH_TAC `abs(sq * (dE:B->real) a - (rho:real^3->real) w) < m0 / &8` THEN
    UNDISCH_TAC `abs(sq * (dE:B->real) b - (rho:real^3->real) y) < m0 / &8` THEN
    UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) w` THEN
    UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) y` THEN UNDISCH_TAC `&0 < m0` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `abs(sq * mfd_dist (top,atlas) (g:B->real^3^3) b c -
                     mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                               open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) y z)
                 <= &1 / &2 * mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                        open_set_atlas (ball(vec 0,rb))) G0 y z` THEN
    UNDISCH_TAC `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                           open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) y z <= m0 / &4` THEN
    UNDISCH_TAC `abs(sq * (dE:B->real) b - (rho:real^3->real) y) < m0 / &8` THEN
    UNDISCH_TAC `abs(sq * (dE:B->real) c - (rho:real^3->real) z) < m0 / &8` THEN
    UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) y` THEN
    UNDISCH_TAC `&7 / &8 * m0 <= (rho:real^3->real) z` THEN UNDISCH_TAC `&0 < m0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "ang" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `sq:real` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`abs(sq * (dE:B->real) a - (rho:real^3->real) w) < m0 / &8`;
    `abs(sq * (dE:B->real) b - (rho:real^3->real) y) < m0 / &8`;
    `abs(sq * (dE:B->real) c - (rho:real^3->real) z) < m0 / &8`;
    `&7 / &8 * m0 <= (rho:real^3->real) w`; `&7 / &8 * m0 <= (rho:real^3->real) y`;
    `&7 / &8 * m0 <= (rho:real^3->real) z`; `&0 < m0`;
    `abs((rho:real^3->real) w - rho y) <=
     mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
               open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w y`;
    `abs((rho:real^3->real) y - rho z) <=
     mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
               open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) y z`;
    `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
               open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w y <= m0 / &4`;
    `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
               open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) y z <= m0 / &4`] THEN
  REAL_ARITH_TAC);;

(* The main theorem: the limit function rho satisfies the hypotheses of      *)
(* P2BK_CONE_REGULAR_STATEMENT on a ball about vec 0 in the open-set         *)
(* manifold ball(vec 0,rb) with the limit metric G0.                         *)

let P2BK_LIMIT_CONE = prove
 (`!top atlas (g:B->real^3^3) dE s1 x Q m0 M0 phi G0 r0 rb.
     p2bk_lcdata (top,atlas) g dE s1 x Q m0 M0 phi G0 r0 rb
     ==> ?r (rho:real^3->real).
           &0 < r /\ r < rb /\
           (!w. w IN ball(vec 0,r) ==> &0 < rho w) /\
           (!w w'. w IN ball(vec 0,r) /\ w' IN ball(vec 0,r)
                   ==> mfd_joinable (subtopology euclidean (ball(vec 0,rb)),
                                     open_set_atlas (ball(vec 0,rb))) w w' /\
                       abs(rho w - rho w') <=
                       mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                 open_set_atlas (ball(vec 0,rb))) G0 w w') /\
           (!w. w IN ball(vec 0,r)
                ==> ?r'. &0 < r' /\
                         !t. &0 < t /\ t < r'
                             ==> ?y. y IN ball(vec 0,r) /\
                                     mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                               open_set_atlas (ball(vec 0,rb))) G0 w y = t /\
                                     rho y = rho w - t) /\
           (!w y z. w IN ball(vec 0,r) /\ y IN ball(vec 0,r) /\ z IN ball(vec 0,r)
                    ==> p2bk_cang (rho w) (rho z)
                          (mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                     open_set_atlas (ball(vec 0,rb))) G0 w z) <=
                        p2bk_cang (rho w) (rho y)
                          (mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                     open_set_atlas (ball(vec 0,rb))) G0 w y) +
                        p2bk_cang (rho y) (rho z)
                          (mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                     open_set_atlas (ball(vec 0,rb))) G0 y z))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BK_LCDATA_LIMIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `rk:real` (X_CHOOSE_THEN `rho0:real`
    (X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `sig:num->num`
    (X_CHOOSE_TAC `rho:real^3->real`)))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `dE:B->real`; `s1:real`; `x:num->B`; `Q:num->real`; `m0:real`; `M0:real`;
                 `phi:num->real^3->B`; `G0:real^3->real^3^3`; `r0:real`; `rb:real`; `r:real`;
                 `rk:real`; `rho0:real`; `C:real`; `sig:num->num`; `rho:real^3->real`]
    P2BK_LCLIM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ds") (CONJUNCTS_THEN2 (LABEL_TAC "tri")
    (CONJUNCTS_THEN2 (LABEL_TAC "rlip") ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2bk_lclim]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sigm") (CONJUNCTS_THEN2 (LABEL_TAC "eu")
    (CONJUNCTS_THEN2 (LABEL_TAC "cmp") (LABEL_TAC "unif")))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_lcdata]) THEN
  ABBREV_TAC `rf = min (r / &4) (m0 / (&8 * C))` THEN
  SUBGOAL_THEN `&0 < rf /\ rf <= r / &4 /\ C * rf <= m0 / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rf" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * m0 / (&8 * C)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,rf) SUBSET cball(vec 0,r / &2) /\ r / &2 < rb`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET cball(vec 0,rk)` THEN
    REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN
    UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `rf <= r / &4` THEN UNDISCH_TAC `rk < rb` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`rf:real`; `rho:real^3->real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `rf <= r / &4` THEN UNDISCH_TAC `r / &2 < rb` THEN UNDISCH_TAC `&0 < r` THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN cball(vec 0,r / &2)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "rlip" (MP_TAC o SPECL [`vec 0:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "eu" (MP_TAC o SPECL [`vec 0:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `C * dist(vec 0:real^3,w) <= m0 / &8` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * rf` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^3) IN ball(vec 0,rf)` THEN
      REWRITE_TAC[IN_BALL_0; DIST_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `m0 <= (rho:real^3->real)(vec 0)` THEN UNDISCH_TAC `&0 < m0` THEN
    REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`w:real^3`; `w':real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN cball(vec 0,r / &2) /\ (w':real^3) IN cball(vec 0,r / &2)`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "eu" (MP_TAC o SPECL [`w:real^3`; `w':real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "rlip" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `dE:B->real`; `s1:real`; `x:num->B`; `Q:num->real`; `m0:real`; `M0:real`;
                   `phi:num->real^3->B`; `G0:real^3->real^3^3`; `r0:real`; `rb:real`; `r:real`;
                   `rk:real`; `rho0:real`; `C:real`; `sig:num->num`; `rho:real^3->real`;
                   `w:real^3`] P2BK_LCLIM_RAY) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`w:real^3`; `y:real^3`; `z:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BK_LCLIM_ANGLE THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `dE:B->real`; `s1:real`; `x:num->B`; `Q:num->real`;
                          `m0:real`; `M0:real`; `phi:num->real^3->B`; `r0:real`; `r:real`; `rk:real`;
                          `rho0:real`; `C:real`; `sig:num->num`] THEN
    ASM_REWRITE_TAC[]]);;

