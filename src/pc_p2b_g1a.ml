(* ========================================================================= *)
(* Unit pc_p2b_g1a (Part 2B): the first half of G1 of MT Prop 9.20           *)
(* (statements of pc_p2b_w920g): a subsequence and a limit linf of the       *)
(* rescaled reduced lengths l(tau_k t, phi_k y), with locally uniform        *)
(* convergence (p2bg_conv), from Cor 9.10 (Claim 9.15, Cor 9.16, Lipschitz   *)
(* bounds) and the C^0 convergence of the rescaled metrics in charts of the  *)
(* limit.                                                                    *)
(*                                                                           *)
(* First Claim 9.15 and the time Lipschitz bound from Cor 9.10 (3).          *)
(* ========================================================================= *)

needs "src/pc_p2b_c910.ml";;
needs "src/pc_p2b_gpb.ml";;
needs "src/pc_apx_local.ml";;

prioritize_real();;
type_invention_error := true;;

(* MT Claim 9.15: l(tau t, q) <= (3/2)(t + 1/t^2) when l(tau, q) <= 3/2.     *)

let P2BX_CLAIM_9_15 = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p tau q t.
     P2B_COR_9_10_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ q IN topspace top /\
     &0 < tau /\ p2b_klx (top,atlas) g p tau q <= &3 / &2 /\ &0 < t
     ==> p2b_klx (top,atlas) g p (tau * t) q <= &3 / &2 * (t + inv(t pow 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C910") STRIP_ASSUME_TAC) THEN
  USE_THEN "C910" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                   `atlas:((B->bool)#(B->real^3))->bool`;
                                   `g:real->B->real^3^3`; `p:B`] o
                   REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PT") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "MO"))) THEN
  SUBGOAL_THEN `&0 <= p2b_klx (top,atlas) (g:real->B->real^3^3) p (tau * t) q /\
                &0 <= p2b_klx (top,atlas) g p tau q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "PT" (MP_TAC o SPECL [`tau * t:real`; `q:B`]);
      USE_THEN "PT" (MP_TAC o SPECL [`tau:real`; `q:B`])] THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(t pow 2) /\ &0 < t pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `&1 <= t \/ t <= &1`) THENL
   [USE_THEN "MO" (MP_TAC o SPECL [`q:B`; `tau:real`; `tau * t:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
    SUBGOAL_THEN `t * p2b_klx (top,atlas) (g:real->B->real^3^3) p tau q <= t * &3 / &2`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    USE_THEN "MO" (MP_TAC o SPECL [`q:B`; `tau * t:real`; `tau:real`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `&0 < tau pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `p2b_klx (top,atlas) (g:real->B->real^3^3) p (tau * t) q <=
                  inv(t pow 2) * &3 / &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(t pow 2) * p2b_klx (top,atlas) (g:real->B->real^3^3) p tau q` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `t pow 2 * p2b_klx (top,atlas) (g:real->B->real^3^3) p (tau * t) q <=
                     p2b_klx (top,atlas) g p tau q` THEN
        UNDISCH_TAC `&0 < t pow 2` THEN
        SPEC_TAC(`p2b_klx (top,atlas) (g:real->B->real^3^3) p (tau * t) q`,`a:real`) THEN
        SPEC_TAC(`p2b_klx (top,atlas) (g:real->B->real^3^3) p tau q`,`b:real`) THEN
        SPEC_TAC(`t pow 2`,`u:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 <= t` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC]]);;

(* The time Lipschitz bound of Cor 9.10 (3) at a point. *)

let P2BX_KLX_TIME_LIP = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p q t1 t2 B.
     P2B_COR_9_10_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ q IN topspace top /\
     &0 < t1 /\ t1 <= t2 /\
     p2b_klx (top,atlas) g p t1 q <= B /\ p2b_klx (top,atlas) g p t2 q <= B
     ==> abs(p2b_klx (top,atlas) g p t2 q - p2b_klx (top,atlas) g p t1 q) <=
         (t2 - t1) * (B / t1 + &2 * t2 * B / t1 pow 2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C910") STRIP_ASSUME_TAC) THEN
  USE_THEN "C910" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                   `atlas:((B->bool)#(B->real^3))->bool`;
                                   `g:real->B->real^3^3`; `p:B`] o
                   REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PT") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "MO"))) THEN
  USE_THEN "MO" (MP_TAC o SPECL [`q:B`; `t1:real`; `t2:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= p2b_klx (top,atlas) (g:real->B->real^3^3) p t1 q /\
                &0 <= p2b_klx (top,atlas) g p t2 q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "PT" (MP_TAC o SPECL [`t1:real`; `q:B`]);
      USE_THEN "PT" (MP_TAC o SPECL [`t2:real`; `q:B`])] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);
    ALL_TAC] THEN
  ABBREV_TAC `a = p2b_klx (top,atlas) (g:real->B->real^3^3) p t1 q` THEN
  ABBREV_TAC `b = p2b_klx (top,atlas) (g:real->B->real^3^3) p t2 q` THEN
  SUBGOAL_THEN `&0 < t1 pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `b - a <= (t2 - t1) * (B / t1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `t1 * (b - a) <= (t2 - t1) * B` MP_TAC THENL
     [SUBGOAL_THEN `(t2 - t1) * a <= (t2 - t1) * B` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a - b <= (t2 - t1) * (&2 * t2 * B / t1 pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `t1 pow 2 * (a - b) <= (t2 - t1) * (&2 * t2 * B)` MP_TAC THENL
     [SUBGOAL_THEN `(t2 pow 2 - t1 pow 2) * b <= (t2 - t1) * (&2 * t2 * B)` MP_TAC THENL
       [SUBGOAL_THEN `t2 pow 2 - t1 pow 2 = (t2 - t1) * (t2 + t1)` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(t2 + t1) * B` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (t2 - t1) * (B / t1) /\ &0 <= (t2 - t1) * (&2 * t2 * B / t1 pow 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The diagonal extraction.  If every sequence of indices tending to         *)
(* infinity has a subsequence along which f is uniformly Cauchy on S i, then *)
(* one subsequence converges uniformly on every S i.                         *)
(* ------------------------------------------------------------------------- *)

(* A sequence of indices that does not tend to infinity has a constant      *)
(* subsequence.                                                             *)

let P2BX_BOUNDED_CONST_SUBSEQ = prove
 (`!(r:num->num) N.
     (!n0. ?n. n0 <= n /\ r n < N)
     ==> ?k v. (!m n:num. m < n ==> k m < k n) /\ !n:num. r(k n) = v:num`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?v. INFINITE {n | (r:num->num) n = v}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INFINITE; GSYM NOT_FORALL_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE {n | (r:num->num) n < N}` MP_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `UNIONS (IMAGE (\v. {n | (r:num->num) n = v}) {v | v < N})` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
        ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT];
        REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]];
      REWRITE_TAC[GSYM INFINITE; num_INFINITE_EQ; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INFINITE_ENUMERATE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`k:num->num`; `v:num`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN
  UNDISCH_TAC `IMAGE (k:num->num) (:num) = {n | (r:num->num) n = v}` THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN MESON_TAC[]);;

let P2BX_DIAG_SUBSEQ = prove
 (`!(f:num->X->real) (S:num->X->bool).
     (!i (r:num->num).
        (!N. ?n0. !n. n0 <= n ==> N <= r n)
        ==> ?k:num->num. (!m n:num. m < n ==> k m < k n) /\
                !e. &0 < e
                    ==> ?N. !m n x. N <= m /\ N <= n /\ x IN S i
                                    ==> abs(f (r (k m)) x - f (r (k n)) x) < e)
     ==> ?(sub:num->num) (L:X->real). (!m n:num. m < n ==> sub m < sub n) /\
                 !i e. &0 < e
                       ==> ?N. !n:num x. N <= n /\ x IN S i ==> abs(f (sub n) x - L x) < e`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  MP_TAC(ISPEC `\i (r:num->num).
                  !e. &0 < e
                      ==> ?N. !m n x. N <= m /\ N <= n /\ x IN (S:num->X->bool) i
                                      ==> abs((f:num->X->real) (r m) x - f (r n) x) < e`
         SUBSEQUENCE_DIAGONALIZATION_LEMMA) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `r:num->num`] THEN
      ASM_CASES_TAC `!N. ?n0. !n. n0 <= n ==> N <= (r:num->num) n` THENL
       [USE_THEN "H" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_EXISTS_THM; NOT_IMP;
                                            NOT_LE]) THEN
        DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
        MP_TAC(ISPECL [`r:num->num`; `N:num`] P2BX_BOUNDED_CONST_SUBSEQ) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num->num` THEN
        DISCH_THEN(X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN
        ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0]];
      MAP_EVERY X_GEN_TAC [`i:num`; `r:num->num`; `k1:num->num`; `k2:num->num`; `N0:num`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P1") (LABEL_TAC "K12")) THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "P1" (fun th -> MP_TAC(MP (SPEC `e:real` th) (ASSUME `&0 < e`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
      EXISTS_TAC `N0 + N1:num` THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:X`] THEN
      STRIP_TAC THEN
      USE_THEN "K12" (MP_TAC o SPEC `m:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `m':num` STRIP_ASSUME_TAC) THEN
      USE_THEN "K12" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `n':num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\n:num. n`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UC"))) THEN
  EXISTS_TAC `sub:num->num` THEN
  EXISTS_TAC `\x:X. drop(@l. ((\n. lift((f:num->X->real) (sub n) x)) --> l) sequentially)` THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`i:num`; `e:real`] THEN DISCH_TAC THEN
  USE_THEN "UC" (MP_TAC o SPECL [`i:num`; `e / &2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:X`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?l. ((\n. lift((f:num->X->real) (sub n) x)) --> l) sequentially`
  MP_TAC THENL
   [REWRITE_TAC[CONVERGENT_EQ_CAUCHY; cauchy; GE; DIST_LIFT] THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    USE_THEN "UC" (fun th -> MP_TAC(MP (SPECL [`i:num`; `d:real`] th) (ASSUME `&0 < d`))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN
  ABBREV_TAC `ll = @l. ((\n. lift((f:num->X->real) (sub n) x)) --> l) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `MAX M N`) THEN REWRITE_TAC[ARITH_RULE `M <= MAX M N`] THEN
  USE_THEN "N" (MP_TAC o SPECL [`n:num`; `MAX M N`; `x:X`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dist; GSYM LIFT_SUB; NORM_LIFT; LIFT_DROP] THEN
  SUBGOAL_THEN `norm(lift((f:num->X->real) (sub (MAX M N)) x) - ll) =
                abs(f (sub (MAX M N)) x - drop ll)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
    REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The setting unfolded (backward times t of the limit, flows                *)
(* g(-tau k t)/tau k), chart representatives of the embeddings, and the      *)
(* C^0 convergence of the rescaled metrics in a fixed chart c of the limit   *)
(* (from the order-0 distance at the points, in the preferred charts, by the *)
(* chart change of pc_p2b_gpb).                                              *)
(* ========================================================================= *)

let P2BX_SETUP_FACTS = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi.
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> (?kappa. p2b_kappa_solution kappa (top,atlas) g) /\ p IN topspace top /\
         (!k. &0 < tau k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\
         (!k. q k IN topspace top /\ p2b_klx (top,atlas) g p (tau k) (q k) <= &3 / &2) /\
         hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ xl IN topspace top' /\
         connected_space top' /\
         (!k. open_in top' (W k) /\ xl IN W k /\ compact_in top' (top' closure_of W k) /\
              top' closure_of W k SUBSET W (SUC k)) /\
         UNIONS {W k | k IN (:num)} = topspace top' /\
         (!k. phi k xl = q k) /\
         (!a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g') /\
         (!s. s < &1 ==> mfd_complete (top',atlas') (g' s)) /\
         (!s y v1 v2. s < &1 /\ y IN topspace top' /\ ~collinear {vec 0,v1,v2}
                      ==> &0 <= mfd_sectional atlas' (g' s) y v1 v2) /\
         (!t1 t2 K m eta.
             &0 < t1 /\ t1 <= t2 /\ compact_in top' K /\ &0 < eta
             ==> ?k0. !k. k0 <= k
                    ==> K SUBSET W k /\
                        (?psi. mfd_diffeo top' atlas' (W k) top atlas
                                          (IMAGE (phi k) (W k)) (phi k) psi) /\
                        !t y. t1 <= t /\ t <= t2 /\ y IN K
                              ==> lck_dist2 m
                                    (metric_local atlas' (chart_at atlas' y) (g'(&1 - t)))
                                    (\z. inv(tau k) %%
                                         rfs_pullback atlas (phi k o chart_inv (chart_at atlas' y))
                                           (g(--(tau k * t))) z)
                                    (SND(chart_at atlas' y) y) < eta)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bg_setup; p2c_flow_limit_with] THEN BETA_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!t1 t2 K m eta.
      &0 < t1 /\ t1 <= t2 /\ compact_in top' K /\ &0 < eta
      ==> ?k0. !k. k0 <= k
             ==> K SUBSET W k /\
                 (?psi. mfd_diffeo top' atlas' (W k) top atlas
                                   (IMAGE ((phi:num->B->A) k) (W k)) (phi k) psi) /\
                 !t y. t1 <= t /\ t <= t2 /\ y IN K
                       ==> lck_dist2 m
                             (metric_local atlas' (chart_at atlas' y) ((g':real->B->real^3^3)(&1 - t)))
                             (\z. inv(tau k) %%
                                  rfs_pullback atlas (phi k o chart_inv (chart_at atlas' y))
                                    ((g:real->A->real^3^3)(--(tau k * t))) z)
                             (SND(chart_at atlas' y) y) < eta`
  (fun th -> ASM_REWRITE_TAC[th] THEN ASM_MESON_TAC[]) THEN
  MAP_EVERY X_GEN_TAC [`t1:real`; `t2:real`; `K:B->bool`; `m:num`; `eta:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&1 - t2`; `&1 - t1`; `K:B->bool`; `m:num`; `eta:real`] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2"))
                         (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
  BETA_TAC THEN DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. --(tau (k:num)) + (&1 - t) / inv(tau k) = --(tau k * t)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[real_div; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau(k:num) * t1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "D") (LABEL_TAC "L"))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "D" (MP_TAC o SPEC `&1 - t1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> --x <= &0`];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:B`] THEN STRIP_TAC THEN
  USE_THEN "L" (MP_TAC o SPECL [`&1 - t`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Chart representatives of an embedding are differentiable. *)

let P2BX_DIFFEO_CHART_DIFF = prove
 (`!(top':B topology) atlas' W (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) W'
    (f:B->A) f' (c':(B->bool)#(B->real^N)) y.
     smooth_manifold_atlas top' atlas' /\ smooth_manifold_atlas top atlas /\
     mfd_diffeo top' atlas' W top atlas W' f f' /\ c' IN atlas' /\ y IN FST c' /\ y IN W
     ==> (SND(chart_at atlas (f y)) o f o chart_inv c') differentiable at (SND c' y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `(f:B->A) y IN topspace top` ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:B->A) y IN W'` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2 o
                GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(f:B->A) y`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `W:B->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W':A->bool`;
                 `f:B->A`; `f':A->B`; `FST(c':(B->bool)#(B->real^N))`; `SND(c':(B->bool)#(B->real^N))`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:B->A) y))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:B->A) y))`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (SND(c':(B->bool)#(B->real^N)))
                {x | x IN FST c' INTER W /\
                     (f:B->A) x IN FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (f y))}` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]);;

(* The C^0 convergence in a fixed chart c of the limit, as a relative      *)
(* bound on quadratic forms, uniformly on compact parts of the chart image *)
(* and compact backward-time intervals in (0,inf).                          *)

let P2BX_G1_C0 = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi c K t1 t2 e.
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     c IN atlas' /\ compact K /\ K SUBSET IMAGE (SND c) (FST c) /\
     &0 < t1 /\ t1 <= t2 /\ &0 < e
     ==> ?k0. !k. k0 <= k
            ==> IMAGE (chart_inv c) K SUBSET W k /\
                !x t w. x IN K /\ t1 <= t /\ t <= t2
                        ==> abs(w dot ((inv(tau k) %%
                                        rfs_pullback atlas (phi k o chart_inv c)
                                          (g(--(tau k * t))) x) ** w) -
                                w dot (metric_local atlas' c (g'(&1 - t)) x ** w))
                            <= e * (w dot (metric_local atlas' c (g'(&1 - t)) x ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `compact_in top' (IMAGE (chart_inv (c:(B->bool)#(B->real^3))) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas':((B->bool)#(B->real^3))->bool`;
                          `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`]
                  MFD_PARAM_CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`t1:real`; `t2:real`; `IMAGE (chart_inv (c:(B->bool)#(B->real^3))) K`; `0`; `e pow 2`] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2"))
                         (concl th))) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `psi:A->B`) (LABEL_TAC "L"))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`; `w:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) x IN FST c /\ SND c (chart_inv c x) = x`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `y = chart_inv (c:(B->bool)#(B->real^3)) x` THEN
  SUBGOAL_THEN `(y:B) IN IMAGE (chart_inv (c:(B->bool)#(B->real^3))) K` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN W (k:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top'` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `y:B`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c' = chart_at (atlas':((B->bool)#(B->real^3))->bool) y` THEN
  ABBREV_TAC `J = matrix(chart_jac (c:(B->bool)#(B->real^3)) c' y)` THEN
  (* the limit metric is a metric at the time 1 - t *)
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - t))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `--t:real` o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "ricci_flow_on"))
                           (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c':(B->bool)#(B->real^3))) (FST c'))
                 (metric_local atlas' c' ((g':real->B->real^3^3)(&1 - t)))`
  MP_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  REWRITE_TAC[metric_field] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND(c':(B->bool)#(B->real^3)) y IN IMAGE (SND c') (FST c')` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the order-0 distance in the preferred chart c' *)
  REMOVE_THEN "L" (MP_TAC o SPECL [`t:real`; `y:B`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `sqrt(lck_dist2 0 (metric_local atlas' (c':(B->bool)#(B->real^3)) ((g':real->B->real^3^3)(&1 - t)))
           (\z. inv(tau(k:num)) %%
                rfs_pullback atlas ((phi:num->B->A) k o chart_inv c')
                  ((g:real->A->real^3^3)(--(tau k * t))) z)
           (SND c' y)) <= e`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  (* transfer to the chart c *)
  SUBGOAL_THEN
   `rfs_pullback atlas ((phi:num->B->A) k o chart_inv (c:(B->bool)#(B->real^3)))
      ((g:real->A->real^3^3)(--(tau k * t))) x =
    transp J ** rfs_pullback atlas (phi k o chart_inv c') (g(--(tau k * t))) (SND c' y) ** J`
  SUBST1_TAC THENL
   [EXPAND_TAC "J" THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `SND(c:(B->bool)#(B->real^3)) y = x`)) THEN
    MATCH_MP_TAC P2BX_RFS_PULLBACK_TRANS THEN
    EXISTS_TAC `top':B topology` THEN EXISTS_TAC `atlas':((B->bool)#(B->real^3))->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BX_DIFFEO_CHART_DIFF THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `(W:num->B->bool) k`; `top:A topology`;
                          `IMAGE ((phi:num->B->A) k) (W k)`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_local atlas' (c:(B->bool)#(B->real^3)) ((g':real->B->real^3^3)(&1 - t)) x =
    transp J ** metric_local atlas' c' (g'(&1 - t)) (SND c' y) ** J`
  SUBST1_TAC THENL
   [EXPAND_TAC "J" THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `SND(c:(B->bool)#(B->real^3)) y = x`)) THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                   `FST(c':(B->bool)#(B->real^3))`; `SND(c':(B->bool)#(B->real^3))`;
                   `(g':real->B->real^3^3)(&1 - t)`; `y:B`] METRIC_LOCAL_JAC) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN
  MP_TAC(ISPECL [`inv(tau(k:num)) %%
                  rfs_pullback atlas ((phi:num->B->A) k o chart_inv (c':(B->bool)#(B->real^3)))
                    ((g:real->A->real^3^3)(--(tau k * t))) (SND c' y)`;
                 `metric_local atlas' (c':(B->bool)#(B->real^3)) ((g':real->B->real^3^3)(&1 - t))
                    (SND c' y)`;
                 `J:real^3^3`; `e:real`] P2BX_QF_CONGRUENCE) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `u:real^3` THEN
    MP_TAC(ISPECL [`metric_local atlas' (c':(B->bool)#(B->real^3)) ((g':real->B->real^3^3)(&1 - t))`;
                   `\z. inv(tau(k:num)) %%
                        rfs_pullback atlas ((phi:num->B->A) k o chart_inv (c':(B->bool)#(B->real^3)))
                          ((g:real->A->real^3^3)(--(tau k * t))) z`;
                   `SND(c':(B->bool)#(B->real^3)) y`; `u:real^3`] P2BX_LCK0_QF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `b * q <= e * q ==> a <= b * q ==> a <= e * q`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `u:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

(* ========================================================================= *)
(* The embeddings read in charts of the limit are parametrizations;          *)
(* distances along pushed chart segments; bounds of the limit metric on      *)
(* compact chart parts; the spatial Lipschitz bound of sqrt l in limit-chart *)
(* coordinates (MT Cor 9.10 (2) with the C^0 bound).                         *)
(* ========================================================================= *)

let P2BX_PARAM_EMBED = prove
 (`!(top':B topology) atlas' W (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) W'
    (f:B->A) f' (c:(B->bool)#(B->real^N)).
     smooth_manifold_atlas top' atlas' /\ smooth_manifold_atlas top atlas /\
     mfd_diffeo top' atlas' W top atlas W' f f' /\ c IN atlas'
     ==> mfd_param top atlas (IMAGE (SND c) (FST c INTER W)) (f o chart_inv c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top' (FST(c:(B->bool)#(B->real^N)) INTER W)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[mfd_diffeo];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                        `W:B->bool`; `W':A->bool`; `f':A->B`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^N))) (FST c)` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                     `FST(c:(B->bool)#(B->real^N))`; `SND(c:(B->bool)#(B->real^N))`]
                    MFD_PARAM_CHART_INV) THEN ASM_REWRITE_TAC[PAIR];
      MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      SET_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `y:B` THEN STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* The distance between the images of the ends of a chart segment under a  *)
(* parametrization, from a bound on the pulled-back metric along it.        *)

let P2BX_PUSH_SEGMENT_DIST = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) p q C.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ mfd_param top atlas s e /\
     segment[p,q] SUBSET s /\ &0 <= C /\
     (!y. y IN segment[p,q] ==> (q - p) dot (rfs_pullback atlas e g y ** (q - p)) <= C)
     ==> mfd_dist (top,atlas) g (e p) (e q) <= sqrt C`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean s) (open_set_atlas (s:real^N->bool))`
  ASSUME_TAC THENL [MATCH_MP_TAC OPEN_SET_ATLAS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool,(\x:real^N. x)) IN open_set_atlas s` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field s (rfs_pullback atlas (e:real^N->A) (g:A->real^N^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas s)
                  (rfs_pullback atlas (e:real^N->A) (g:A->real^N^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`; `open_set_atlas (s:real^N->bool)`;
                 `s:real^N->bool`; `\x:real^N. x`; `p:real^N`; `q:real^N`] GRGD_CHART_SEGMENT) THEN
  ASM_REWRITE_TAC[IMAGE_ID] THEN BETA_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `s:real^N->bool`; `e:real^N->A`;
                 `rfs_pullback atlas (e:real^N->A) (g:A->real^N^N)`;
                 `\t. chart_inv (s:real^N->bool,(\x:real^N. x)) (p + t % (q - p))`;
                 `&0`; `&1`] MFD_PARAM_C1_CURVE_LENGTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[rfs_pullback]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `(e:real^N->A) o (\t. chart_inv (s:real^N->bool,(\x:real^N. x)) (p + t % (q - p)))`;
                 `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[o_THM] THEN BETA_TAC THEN
  SUBGOAL_THEN `(p:real^N) IN s /\ q IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[MFDM_CHART_INV_ID; VECTOR_ARITH `p + &0 % (q - p) = p:real^N`;
               VECTOR_ARITH `p + &1 % (q - p) = q:real^N`] THEN
  MATCH_MP_TAC(REAL_ARITH `l <= c ==> d <= l ==> d <= c`) THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,&1]) (\t:real. sqrt C)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN
      EXISTS_TAC `subtopology euclidean (s:real^N->bool)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `rfs_pullback atlas (e:real^N->A) (g:A->real^N^N)`;
                   `\t. chart_inv (s:real^N->bool,(\x:real^N. x)) (p + t % (q - p))`;
                   `&0`; `&1`; `t:real`] GRGD_OPEN_SET_SPEED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `t:real` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    SIMP_TAC[REAL_INTEGRAL_CONST; REAL_POS] THEN REAL_ARITH_TAC]);;

(* A quadratic form is bounded by the entries. *)

let P2BX_QF_LE_ENTRIES = prove
 (`!(A:real^N^N) B w.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) ==> abs(A$i$j) <= B)
     ==> w dot (A ** w) <= (&(dimindex(:N)) * &(dimindex(:N)) * B) * norm w pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ONORM_LE_MATRIX_COMPONENT) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(w:real^N) * norm((A:real^N^N) ** w)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`w:real^N`; `(A:real^N^N) ** w`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(m:real) * (x * x) = x * (m * x)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `onorm(\x. (A:real^N^N) ** x) * norm(w:real^N)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BETA_RULE(CONJUNCT1(MATCH_MP ONORM (ISPEC `A:real^N^N` MATRIX_VECTOR_MUL_LINEAR)))];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]]);;

(* ========================================================================= *)
(* Bounds of the limit metric on compact chart parts and the spatial         *)
(* Lipschitz bound of sqrt l in limit-chart coordinates, uniform in k (MT    *)
(* Cor 9.10 (2) along pushed segments).                                      *)
(* ========================================================================= *)

let P2BX_LIMIT_METRIC_BOUND = prove
 (`!(top':B topology) atlas' (g':real->B->real^3^3) c D t1 t2.
     (!a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g') /\ c IN atlas' /\
     compact D /\ D SUBSET IMAGE (SND c) (FST c) /\ &0 < t1 /\ t1 <= t2
     ==> ?Lam. &0 <= Lam /\
               !x t v. x IN D /\ t1 <= t /\ t <= t2
                       ==> v dot (metric_local atlas' c (g'(&1 - t)) x ** v) <= Lam * norm v pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `--t2:real`; `&1`; `g':real->B->real^3^3`; `c:(B->bool)#(B->real^3)`]
         (REWRITE_RULE[P2B_FLOW_CHART_STATEMENT]
           (ISPECL [`w:B->bool`; `(:3)`] P2B_FLOW_CHART))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o CONJUNCT1) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `compact ((D:real^3->bool) PCROSS interval[lift t1,lift t2]) /\
    ((D:real^3->bool) PCROSS interval[lift t1,lift t2]) SUBSET
    p2bw_cdom (c:(B->bool)#(B->real^3)) (&1 - --t2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; p2bw_cdom; IN_ELIM_THM;
                FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT STRIP_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(vectorize:real^3^3->real^(3,3)finite_prod) o
                  p2bw_cmet atlas' (c:(B->bool)#(B->real^3)) (&1) (g':real->B->real^3^3)`;
                 `(D:real^3->bool) PCROSS interval[lift t1,lift t2]`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&3 * &3 * B` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`metric_local atlas' (c:(B->bool)#(B->real^3)) ((g':real->B->real^3^3)(&1 - t)) x`;
                 `B:real`; `v:real^3`] P2BX_QF_LE_ENTRIES) THEN
  REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((vectorize:real^3^3->real^(3,3)finite_prod)
                     (metric_local atlas' (c:(B->bool)#(B->real^3)) ((g':real->B->real^3^3)(&1 - t)) x))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC P2BX_ENTRY_LE_VECTORIZE THEN ASM_REWRITE_TAC[DIMINDEX_3]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (x:real^3) (lift t)`) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; p2bw_cmet;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_REWRITE_TAC[]);;

(* Arithmetic for the spatial constant. *)

let P2BX_SPATIAL_ARITH = prove
 (`!tk t t1 Lam n.
     &0 < tk /\ &0 < t1 /\ t1 <= t /\ &0 <= Lam /\ &0 <= n
     ==> sqrt(&3 / (&4 * (tk * t))) * sqrt(tk * (&3 / &2 * (Lam * n pow 2))) <=
         sqrt(&9 * Lam / (&8 * t1)) * n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &3 / (&4 * (tk * t)) /\ &0 <= tk * (&3 / &2 * (Lam * n pow 2)) /\
                &0 <= &9 * Lam / (&8 * t)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SQRT_MUL] THEN
  SUBGOAL_THEN `&3 / (&4 * (tk * t)) * tk * (&3 / &2 * (Lam * n pow 2)) =
                (&9 * Lam / (&8 * t)) * n pow 2`
  SUBST1_TAC THENL
   [MAP_EVERY (fun th -> MP_TAC th) [ASSUME `&0 < tk`; ASSUME `&0 < t`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[ISPECL [`&9 * Lam / (&8 * t)`; `n pow 2`] SQRT_MUL] THEN
  ASM_SIMP_TAC[POW_2_SQRT] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;

(* The spatial bound: in a compact convex part D of the chart image of c,   *)
(* sqrt l(tau k t, phi k (chart_inv c x)) is L-Lipschitz in x for all k     *)
(* large, uniformly for t in [t1,t2].                                         *)

let P2BX_G1_SPATIAL = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi c D t1 t2.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     c IN atlas' /\ compact D /\ convex D /\ D SUBSET IMAGE (SND c) (FST c) /\
     &0 < t1 /\ t1 <= t2
     ==> ?L k0. &0 <= L /\
                !k. k0 <= k
                    ==> IMAGE (chart_inv c) D SUBSET W k /\
                        !x x' t. x IN D /\ x' IN D /\ t1 <= t /\ t <= t2
                                 ==> sqrt(p2b_klx (top,atlas) g p (tau k * t)
                                                  (phi k (chart_inv c x'))) <=
                                     sqrt(p2b_klx (top,atlas) g p (tau k * t)
                                                  (phi k (chart_inv c x))) +
                                     L * norm(x' - x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C910") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `c:(B->bool)#(B->real^3)`; `D:real^3->bool`;
                 `t1:real`; `t2:real`] P2BX_LIMIT_METRIC_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `c:(B->bool)#(B->real^3)`; `D:real^3->bool`; `t1:real`; `t2:real`;
                 `&1 / &2`] P2BX_G1_C0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "C0")) THEN
  SUBGOAL_THEN `?k1:num. !k. k1 <= k
                       ==> ?psi. mfd_diffeo (top':B topology)
                                   (atlas':((B->bool)#(B->real^3))->bool) (W k)
                                   (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
                                   (IMAGE ((phi:num->B->A) k) (W k)) (phi k) psi`
  (X_CHOOSE_THEN `k1:num` (LABEL_TAC "DF")) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`&1`; `&1`; `{xl:B}`; `0`; `&1`] o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2"))
                           (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01; COMPACT_IN_SING] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `sqrt(&9 * Lam / (&8 * t1))` THEN EXISTS_TAC `k0 + k1:num` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REMOVE_THEN "C0" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C0")) THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "DF" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `x':real^3`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < tau(k:num) * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s = IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER W(k:num))` THEN
  SUBGOAL_THEN `mfd_param top atlas s ((phi:num->B->A) k o chart_inv (c:(B->bool)#(B->real^3)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC P2BX_PARAM_EMBED THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `IMAGE ((phi:num->B->A) k) (W k)`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(D:real^3->bool) SUBSET s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[SUBSET; IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `chart_inv (c:(B->bool)#(B->real^3)) z` THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `IMAGE (chart_inv (c:(B->bool)#(B->real^3))) D SUBSET W(k:num)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^3,x'] SUBSET D` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN D
        ==> (phi:num->B->A) k (chart_inv (c:(B->bool)#(B->real^3)) z) IN topspace top`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [mfd_diffeo] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the distance bound along the pushed segment *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3)(--(tau(k:num) * t))`; `s:real^3->bool`;
                 `(phi:num->B->A) k o chart_inv (c:(B->bool)#(B->real^3))`;
                 `x:real^3`; `x':real^3`;
                 `tau(k:num) * (&3 / &2 * (Lam * norm(x' - x:real^3) pow 2))`]
                P2BX_PUSH_SEGMENT_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[];
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_LT_IMP_LE; REAL_LE_DIV; REAL_POS];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN D` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "C0" (MP_TAC o SPECL [`y:real^3`; `t:real`; `x' - x:real^3`]) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `t:real`; `x' - x:real^3`] o
      check (fun th -> can (find_term ((=) `Lam:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `inv(tau(k:num)) *
      ((x' - x) dot (rfs_pullback atlas ((phi:num->B->A) k o chart_inv (c:(B->bool)#(B->real^3)))
                       ((g:real->A->real^3^3)(--(tau k * t))) y ** (x' - x))) <=
      &3 / &2 * (Lam * norm(x' - x:real^3) pow 2)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o
      CONJ (MATCH_MP REAL_LT_IMP_LE (SPEC `k:num` (ASSUME `!k:num. &0 < tau k`)))) THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  (* Cor 9.10 (2) at backward time tau k * t *)
  USE_THEN "C910" (MP_TAC o SPECL [`kappa:real`; `top:A topology`;
                                   `atlas:((A->bool)#(A->real^3))->bool`;
                                   `g:real->A->real^3^3`; `p:A`] o
                   REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`tau(k:num) * t`;
                             `(phi:num->B->A) k (chart_inv (c:(B->bool)#(B->real^3)) x)`;
                             `(phi:num->B->A) k (chart_inv (c:(B->bool)#(B->real^3)) x')`] o
             CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= l + b ==> a <= l + c`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&3 / (&4 * (tau(k:num) * t))) *
              sqrt(tau k * (&3 / &2 * (Lam * norm(x' - x:real^3) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2BX_SPATIAL_ARITH THEN ASM_REWRITE_TAC[NORM_POS_LE]);;

(* ========================================================================= *)
(* Uniform bounds of l(tau k t, phi k y) on compact sets of the limit (MT    *)
(* Cor 9.16 in the form needed here): the spatial bound propagates a         *)
(* pointwise bound over a chart ball, Claim 9.15 bounds the base point, and  *)
(* the limit is connected.                                                   *)
(* ========================================================================= *)

let P2BX_BALL_PROPAGATE = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi t1 t2 y0.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     &0 < t1 /\ t1 <= t2 /\ y0 IN topspace top'
     ==> ?U. open_in top' U /\ y0 IN U /\
             !y1 C1 k1. y1 IN U /\
                        (!k t. k1 <= k /\ t1 <= t /\ t <= t2
                               ==> p2b_klx (top,atlas) g p (tau k * t) (phi k y1) <= C1)
                        ==> ?C k0. !k y t. k0 <= k /\ y IN U /\ t1 <= t /\ t <= t2
                                           ==> y IN W k /\
                                               p2b_klx (top,atlas) g p (tau k * t) (phi k y)
                                               <= C`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `y0:B`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas':((B->bool)#(B->real^3))->bool) y0` THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND(c:(B->bool)#(B->real^3)) y0 IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `SND(c:(B->bool)#(B->real^3)) y0` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL] o
    check (fun th -> concl th = `open(IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c))`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `c:(B->bool)#(B->real^3)`; `cball(SND(c:(B->bool)#(B->real^3)) y0,r)`;
                 `t1:real`; `t2:real`] P2BX_G1_SPATIAL) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; CONVEX_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `{y:B | y IN FST(c:(B->bool)#(B->real^3)) /\ SND c y IN ball(SND c y0,r)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `atlas':((B->bool)#(B->real^3))->bool` THEN
    REWRITE_TAC[OPEN_BALL; ETA_AX; PAIR] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y1:B`; `C1:real`; `k1:num`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `(sqrt C1 + L * &2 * r) pow 2` THEN EXISTS_TAC `k1 + k2:num` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:B`; `t:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term ((=) `L:real`)) (concl th) && is_forall (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL
    [`SND(c:(B->bool)#(B->real^3)) y1`; `SND(c:(B->bool)#(B->real^3)) y`; `t:real`])) THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (chart_inv (c:(B->bool)#(B->real^3))) (cball(SND c y0,r)) SUBSET
                 W(k:num)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `SND(c:(B->bool)#(B->real^3)) y`) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  ABBREV_TAC `F0 = p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                            (g:real->A->real^3^3) (p:A) (tau(k:num) * t) ((phi:num->B->A) k y)` THEN
  ABBREV_TAC `F1 = p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                            (g:real->A->real^3^3) (p:A) (tau(k:num) * t) ((phi:num->B->A) k y1)` THEN
  SUBGOAL_THEN `F1 <= C1` ASSUME_TAC THENL
   [EXPAND_TAC "F1" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `F0 < &0` THENL
   [MATCH_MP_TAC(REAL_ARITH `x < &0 /\ &0 <= y ==> x <= y`) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
  SUBGOAL_THEN `norm(SND(c:(B->bool)#(B->real^3)) y - SND c y1) <= &2 * r` ASSUME_TAC THENL
   [UNDISCH_TAC `SND(c:(B->bool)#(B->real^3)) y IN ball(SND c y0,r)` THEN
    UNDISCH_TAC `SND(c:(B->bool)#(B->real^3)) y1 IN ball(SND c y0,r)` THEN
    REWRITE_TAC[IN_BALL] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt F0 <= sqrt C1 + L * &2 * r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt F1 + L * norm(SND(c:(B->bool)#(B->real^3)) y - SND c y1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
    ASM_SIMP_TAC[SQRT_MONO_LE; REAL_LE_LMUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `sqrt F0`; `sqrt C1 + L * &2 * r`] REAL_POW_LE2) THEN
  ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2]);;

(* A finite family of sets, each with its own bound and threshold, has a    *)
(* common bound and threshold when the property is monotone in both.        *)

let P2BX_FINITE_UNIFORM = prove
 (`!(P:(B->bool)->real->num->bool) V.
     FINITE V /\ (!U C k0 C' k0'. P U C k0 /\ C <= C' /\ k0 <= k0' ==> P U C' k0') /\
     (!U. U IN V ==> ?C k0. P U C k0)
     ==> ?C k0. !U. U IN V ==> P U C k0`,
  GEN_TAC THEN
  ASM_CASES_TAC `!U C k0 C' k0'. (P:(B->bool)->real->num->bool) U C k0 /\ C <= C' /\ k0 <= k0'
                                 ==> P U C' k0'` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`U0:B->bool`; `V:(B->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `C1:real` (X_CHOOSE_TAC `k1:num`)) ASSUME_TAC) THEN
  REMOVE_THEN "IH" MP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (X_CHOOSE_TAC `k0:num`)) THEN
  EXISTS_TAC `max C0 C1` THEN EXISTS_TAC `MAX k0 k1` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`C1:real`; `k1:num`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ARITH_TAC];
    X_GEN_TAC `U:B->bool` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`C0:real`; `k0:num`] THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ARITH_TAC]]);;

(* The uniform bound on compact sets of the limit. *)

let P2BX_G1_BOUND = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi K t1 t2.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     compact_in top' K /\ &0 < t1 /\ t1 <= t2
     ==> ?C k0. !k y t. k0 <= k /\ y IN K /\ t1 <= t /\ t <= t2
                        ==> y IN W k /\
                            p2b_klx (top,atlas) g p (tau k * t) (phi k y) <= C`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C910") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  ABBREV_TAC
   `P = \U:B->bool C k0. !k y t. k0 <= k /\ y IN U /\ t1 <= t /\ t <= t2
                                 ==> y IN (W:num->B->bool) k /\
                                     p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                                             (g:real->A->real^3^3) (p:A) ((tau:num->real) k * t)
                                             ((phi:num->B->A) k y) <= C` THEN
  SUBGOAL_THEN `!U C k0 C' k0'. (P:(B->bool)->real->num->bool) U C k0 /\ C <= C' /\ k0 <= k0'
                                ==> P U C' k0'` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `y:B`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the propagation step in terms of P *)
  SUBGOAL_THEN
   `!y0. y0 IN topspace top'
         ==> ?U. open_in top' U /\ y0 IN U /\
                 !y1 C1 k1. y1 IN U /\
                            (!k t. k1 <= k /\ t1 <= t /\ t <= t2
                                   ==> p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                                         (g:real->A->real^3^3) (p:A) ((tau:num->real) k * t)
                                         ((phi:num->B->A) k y1) <= C1)
                            ==> ?C k0. (P:(B->bool)->real->num->bool) U C k0`
  (LABEL_TAC "PR") THENL
   [X_GEN_TAC `y0:B` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
    MATCH_MP_TAC P2BX_BALL_PROPAGATE THEN
    MAP_EVERY EXISTS_TAC [`q:num->A`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `g':real->B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the good set is open and closed *)
  ABBREV_TAC `S = {y:B | y IN topspace top' /\
                         ?U C k0. open_in top' U /\ y IN U /\
                                  (P:(B->bool)->real->num->bool) U C k0}` THEN
  SUBGOAL_THEN `(xl:B) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "PR" (MP_TAC o SPEC `xl:B`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `U:B->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`xl:B`; `&3 / &2 * (t2 + inv(t1 pow 2))`; `0`] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`k:num`; `t:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 / &2 * (t + inv(t pow 2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_CLAIM_9_15 THEN
      EXISTS_TAC `u:A->bool` THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `S = topspace (top':B topology)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `S:B->bool` o GEN_REWRITE_RULE I [CONNECTED_SPACE_CLOPEN_IN] o
      check (fun th -> concl th = `connected_space (top':B topology)`)) THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
     [ALL_TAC; UNDISCH_TAC `(xl:B) IN S` THEN SET_TAC[]] THEN
    SUBGOAL_THEN `(S:B->bool) SUBSET topspace top'` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
      UNDISCH_TAC `(y:B) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `U:B->bool` (X_CHOOSE_THEN `C:real`
          (X_CHOOSE_THEN `k0:num` STRIP_ASSUME_TAC)))) THEN
      EXISTS_TAC `U:B->bool` THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `z:B` THEN DISCH_TAC THEN
      CONJ_TAC THENL
       [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (U:B->bool)`)) THEN
        UNDISCH_TAC `(z:B) IN U` THEN SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`U:B->bool`; `C:real`; `k0:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[closed_in] THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:B` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    USE_THEN "PR" (MP_TAC o SPEC `y:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:B->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `U:B->bool` THEN ASM_REWRITE_TAC[SUBSET; IN_DIFF] THEN
    X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (U:B->bool)`)) THEN
      UNDISCH_TAC `(z:B) IN U` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~((y:B) IN S)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:B) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `U':B->bool` (X_CHOOSE_THEN `C':real`
        (X_CHOOSE_THEN `k':num` STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `U:B->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`z:B`; `C':real`; `k':num`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `t:real`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(P:(B->bool)->real->num->bool) U' C' k'` THEN EXPAND_TAC "P" THEN
    DISCH_THEN(MP_TAC o SPECL [`k:num`; `z:B`; `t:real`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* compactness *)
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [compact_in] o
    check (fun th -> concl th = `compact_in (top':B topology) K`)) THEN
  DISCH_THEN(MP_TAC o SPEC
   `{U:B->bool | open_in top' U /\ ?C k0. (P:(B->bool)->real->num->bool) U C k0}`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:B) IN S` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(MATCH_MP COMPACT_IN_SUBSET_TOPSPACE (ASSUME `compact_in (top':B topology) K`)) THEN
      UNDISCH_TAC `(y:B) IN K` THEN SET_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(B->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`P:(B->bool)->real->num->bool`; `V:(B->bool)->bool`] P2BX_FINITE_UNIFORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(V:(B->bool)->bool) SUBSET
                 {U | open_in top' U /\ ?C k0. (P:(B->bool)->real->num->bool) U C k0}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`k:num`; `y:B`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?U:B->bool. U IN V /\ y IN U` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:B->bool) SUBSET UNIONS V` THEN UNDISCH_TAC `(y:B) IN K` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `U:B->bool`) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "P" THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* On a compact convex chart part D and a backward-time interval [t1,t2],    *)
(* the functions (x,t) -> l(tau k t, phi k (chart_inv c x)) are bounded      *)
(* and uniformly Lipschitz for k large (Cor 9.10 (2), (3) with the uniform   *)
(* bound).                                                                   *)
(* ========================================================================= *)

let P2BX_SQRT_DIFF_ARITH = prove
 (`!a b C d. &0 <= a /\ a <= C /\ &0 <= b /\ b <= C /\ abs(sqrt a - sqrt b) <= d
             ==> abs(a - b) <= &2 * sqrt C * d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a - b = (sqrt a - sqrt b) * (sqrt a + sqrt b)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(x - y) * (x + y) = x pow 2 - y pow 2`] THEN
    ASM_SIMP_TAC[SQRT_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(sqrt a + sqrt b) <= &2 * sqrt C` ASSUME_TAC THENL
   [MP_TAC(SPECL [`a:real`; `C:real`] SQRT_MONO_LE) THEN
    MP_TAC(SPECL [`b:real`; `C:real`] SQRT_MONO_LE) THEN
    MP_TAC(SPEC `a:real` SQRT_POS_LE) THEN MP_TAC(SPEC `b:real` SQRT_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&2 * s * d = d * (&2 * s)`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let P2BX_TIME_ARITH = prove
 (`!tk t t' t1 t2 C.
     &0 < tk /\ &0 < t1 /\ t1 <= t /\ t <= t' /\ t' <= t2 /\ &0 <= C
     ==> (tk * t' - tk * t) * (C / (tk * t) + &2 * (tk * t') * C / (tk * t) pow 2) <=
         (C / t1 + &2 * t2 * C / t1 pow 2) * abs(t - t')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(tk * t' - tk * t) * (C / (tk * t) + &2 * (tk * t') * C / (tk * t) pow 2) =
    (t' - t) * (C / t + &2 * t' * C / t pow 2)`
  SUBST1_TAC THENL
   [MAP_EVERY (fun th -> MP_TAC th) [ASSUME `&0 < tk`; ASSUME `&0 < t`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(t - t') = t' - t` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]]);;

let P2BX_G1_PIECE_BOUNDS = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi c D t1 t2.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     c IN atlas' /\ compact D /\ convex D /\ D SUBSET IMAGE (SND c) (FST c) /\
     &0 < t1 /\ t1 <= t2
     ==> ?C b k0. &0 <= C /\ &0 <= b /\
                  !k. k0 <= k
                      ==> IMAGE (chart_inv c) D SUBSET W k /\
                          (!x t. x IN D /\ t1 <= t /\ t <= t2
                                 ==> &0 <= p2b_klx (top,atlas) g p (tau k * t)
                                                   (phi k (chart_inv c x)) /\
                                     p2b_klx (top,atlas) g p (tau k * t)
                                             (phi k (chart_inv c x)) <= C) /\
                          (!x x' t t'. x IN D /\ x' IN D /\ t1 <= t /\ t <= t2 /\
                                       t1 <= t' /\ t' <= t2
                                       ==> abs(p2b_klx (top,atlas) g p (tau k * t)
                                                       (phi k (chart_inv c x)) -
                                               p2b_klx (top,atlas) g p (tau k * t')
                                                       (phi k (chart_inv c x'))) <=
                                           b * (norm(x - x') + abs(t - t')))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C910") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `c:(B->bool)#(B->real^3)`; `D:real^3->bool`; `t1:real`; `t2:real`]
                P2BX_G1_SPATIAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (X_CHOOSE_THEN `k1:num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `compact_in top' (IMAGE (chart_inv (c:(B->bool)#(B->real^3))) D)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas':((B->bool)#(B->real^3))->bool`;
                          `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`]
                  MFD_PARAM_CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `IMAGE (chart_inv (c:(B->bool)#(B->real^3))) D`; `t1:real`; `t2:real`]
                P2BX_G1_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (X_CHOOSE_THEN `k2:num` (LABEL_TAC "BD"))) THEN
  SUBGOAL_THEN `?k3:num. !k. k3 <= k
                       ==> ?psi. mfd_diffeo (top':B topology)
                                   (atlas':((B->bool)#(B->real^3))->bool) (W k)
                                   (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
                                   (IMAGE ((phi:num->B->A) k) (W k)) (phi k) psi`
  (X_CHOOSE_THEN `k3:num` (LABEL_TAC "DF")) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`&1`; `&1`; `{xl:B}`; `0`; `&1`] o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2"))
                           (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01; COMPACT_IN_SING] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C = max C0 (&0)` THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL [EXPAND_TAC "C" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * sqrt C * L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C / t1 + &2 * t2 * C / t1 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`C:real`; `&2 * sqrt C * L + (C / t1 + &2 * t2 * C / t1 pow 2)`; `k1 + k2 + k3:num`] THEN
  ASM_SIMP_TAC[REAL_LE_ADD] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term ((=) `L:real`)) (concl th) && is_forall (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SP")) THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "DF" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `psi:A->B`)] THEN
  (* points and values *)
  SUBGOAL_THEN
   `!x. x IN D
        ==> (phi:num->B->A) k (chart_inv (c:(B->bool)#(B->real^3)) x) IN topspace top`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [mfd_diffeo] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `IMAGE (chart_inv (c:(B->bool)#(B->real^3))) D SUBSET W(k:num)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x t. x IN D /\ t1 <= t /\ t <= t2
          ==> &0 <= p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau(k:num) * t)
                            ((phi:num->B->A) k (chart_inv (c:(B->bool)#(B->real^3)) x)) /\
              p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau k * t) (phi k (chart_inv c x)) <= C`
  (LABEL_TAC "B") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "C910" (MP_TAC o SPECL [`kappa:real`; `top:A topology`;
                                     `atlas:((A->bool)#(A->real^3))->bool`;
                                     `g:real->A->real^3^3`; `p:A`] o
                     REWRITE_RULE[P2B_COR_9_10_STATEMENT]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`tau(k:num) * t`;
                                 `(phi:num->B->A) k (chart_inv (c:(B->bool)#(B->real^3)) x)`] o
                 CONJUNCT1) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0:real` THEN
      CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "C" THEN REAL_ARITH_TAC] THEN
      USE_THEN "BD" (MP_TAC o SPECL [`k:num`; `chart_inv (c:(B->bool)#(B->real^3)) x`;
                                     `t:real`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `x':real^3`; `t:real`; `t':real`] THEN STRIP_TAC THEN
  (* the spatial part at time t *)
  SUBGOAL_THEN
   `abs(p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau(k:num) * t)
          ((phi:num->B->A) k (chart_inv (c:(B->bool)#(B->real^3)) x)) -
        p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau k * t) (phi k (chart_inv c x'))) <=
    &2 * sqrt C * (L * norm(x - x'))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_SQRT_DIFF_ARITH THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b + d /\ b <= a + d ==> abs(a - b) <= d`) THEN
    CONJ_TAC THENL
     [USE_THEN "SP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[NORM_SUB] THEN USE_THEN "SP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the time part at the point x' *)
  SUBGOAL_THEN
   `abs(p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau(k:num) * t)
          ((phi:num->B->A) k (chart_inv (c:(B->bool)#(B->real^3)) x')) -
        p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau k * t') (phi k (chart_inv c x'))) <=
    (C / t1 + &2 * t2 * C / t1 pow 2) * abs(t - t')`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!s s'. t1 <= s /\ s <= s' /\ s' <= t2
             ==> abs(p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau(k:num) * s')
                       ((phi:num->B->A) k (chart_inv (c:(B->bool)#(B->real^3)) x')) -
                     p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau k * s) (phi k (chart_inv c x'))) <=
                 (C / t1 + &2 * t2 * C / t1 pow 2) * abs(s - s')`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(tau(k:num) * s' - tau k * s) *
                  (C / (tau k * s) + &2 * (tau k * s') * C / (tau k * s) pow 2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2BX_KLX_TIME_LIP THEN
        MAP_EVERY EXISTS_TAC [`u:A->bool`; `kappa:real`] THEN
        ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
          USE_THEN "B" (MP_TAC o SPECL [`x':real^3`; `s:real`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          USE_THEN "B" (MP_TAC o SPECL [`x':real^3`; `s':real`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
        MATCH_MP_TAC P2BX_TIME_ARITH THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISJ_CASES_TAC(REAL_ARITH `t <= t' \/ t' <= t`) THENL
     [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ABS_SUB] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `abs(t - t') = abs(t' - t)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 * sqrt C * L) * abs(t - t') /\
                &0 <= (C / t1 + &2 * t2 * C / t1 pow 2) * norm(x - x':real^3)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
    ALL_TAC] THEN
  UNDISCH_TAC
   `abs(p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau(k:num) * t)
          ((phi:num->B->A) k (chart_inv (c:(B->bool)#(B->real^3)) x)) -
        p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau k * t) (phi k (chart_inv c x'))) <=
    &2 * sqrt C * (L * norm(x - x'))` THEN
  UNDISCH_TAC
   `abs(p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau(k:num) * t)
          ((phi:num->B->A) k (chart_inv (c:(B->bool)#(B->real^3)) x')) -
        p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A) (tau k * t') (phi k (chart_inv c x'))) <=
    (C / t1 + &2 * t2 * C / t1 pow 2) * abs(t - t')` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Extraction on one chart piece by Arzela-Ascoli (ARZELA_ASCOLI_LIPSCHITZ   *)
(* in the chart coordinates (x,t)), along any sequence of indices tending to *)
(* infinity.                                                                 *)
(* ========================================================================= *)

let P2BX_PIECE_EXTRACT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi c D t1 t2 (r:num->num).
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     c IN atlas' /\ compact D /\ convex D /\ D SUBSET IMAGE (SND c) (FST c) /\
     &0 < t1 /\ t1 <= t2 /\ (!N. ?n0. !n. n0 <= n ==> N <= r n)
     ==> ?k:num->num.
            (!m n. m < n ==> k m < k n) /\
            !e. &0 < e
                ==> ?N. !m n x t.
                          N <= m /\ N <= n /\ x IN D /\ t1 <= t /\ t <= t2
                          ==> abs(p2b_klx (top,atlas) g p (tau(r(k m)) * t)
                                          (phi (r(k m)) (chart_inv c x)) -
                                  p2b_klx (top,atlas) g p (tau(r(k n)) * t)
                                          (phi (r(k n)) (chart_inv c x))) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `c:(B->bool)#(B->real^3)`; `D:real^3->bool`; `t1:real`; `t2:real`]
                P2BX_G1_PIECE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `b:real`
    (X_CHOOSE_THEN `k0:num` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n0:num` o SPEC `k0:num` o check (fun th ->
    can (find_term ((=) `r:num->num`)) (concl th) && is_forall (concl th))) THEN
  ABBREV_TAC
   `h = \(m:num) (z:real^(3,1)finite_sum).
          lift(p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                 (g:real->A->real^3^3) (p:A)
                 ((tau:num->real)((r:num->num)(n0 + m)) * drop(sndcart z))
                 ((phi:num->B->A) (r(n0 + m)) (chart_inv (c:(B->bool)#(B->real^3)) (fstcart z))))` THEN
  SUBGOAL_THEN `!m:num. (k0:num) <= (r:num->num)(n0 + m)` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num->real^(3,1)finite_sum->real^1`;
                 `(D:real^3->bool) PCROSS interval[lift t1,lift t2]`;
                 `cball(vec 0:real^1,C)`; `&2 * b`] ARZELA_ASCOLI_LIPSCHITZ) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL];
      REWRITE_TAC[BOUNDED_CBALL];
      X_GEN_TAC `m:num` THEN REWRITE_TAC[FORALL_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real^1`] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(h:num->real^(3,1)finite_sum->real^1) m (pastecart x s)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[PASTECART_IN_PCROSS]; ALL_TAC] THEN
      EXPAND_TAC "h" THEN
      REWRITE_TAC[IN_CBALL_0; NORM_LIFT; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; LIFT_DROP]) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r(n0 + m:num):num` o check (fun th ->
        can (find_term ((=) `b:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `drop s`] o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      X_GEN_TAC `m:num` THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_PCROSS] THEN
      MAP_EVERY (fun v -> X_GEN_TAC v THEN DISCH_TAC)
        [`x:real^3`; `s:real^1`; `x':real^3`; `s':real^1`] THEN
      EXPAND_TAC "h" THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; GSYM LIFT_SUB; NORM_LIFT] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; LIFT_DROP]) THEN
      SUBGOAL_THEN
       `norm(x - x':real^3) <= norm(pastecart x s - pastecart x' (s':real^1)) /\
        abs(drop s - drop s') <= norm(pastecart x s - pastecart x' (s':real^1))`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[PASTECART_SUB; GSYM DROP_SUB; GSYM NORM_1] THEN
        MP_TAC(ISPEC `pastecart (x - x':real^3) (s - s':real^1)` NORM_FSTCART) THEN
        MP_TAC(ISPEC `pastecart (x - x':real^3) (s - s':real^1)` NORM_SNDCART) THEN
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `b * (norm(x - x':real^3) + abs(drop s - drop s'))` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `r(n0 + m:num):num` o check (fun th ->
          can (find_term ((=) `b:real`)) (concl th) && is_forall (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `x':real^3`; `drop s`; `drop s'`] o
                   CONJUNCT2 o CONJUNCT2) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `b * u <= b * (&2 * nn) ==> b * u <= (&2 * b) * nn`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gg:real^(3,1)finite_sum->real^1`
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k':num->num` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `\m:num. (n0:num) + (k':num->num) m` THEN BETA_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[LT_ADD_LCANCEL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2` o check (fun th ->
    can (find_term ((=) `gg:real^(3,1)finite_sum->real^1`)) (concl th) &&
    is_forall (concl th) && not (can (find_term ((=) `b:real`)) (concl th)))) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:real^3`; `t:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`m:num`; `pastecart (x:real^3) (lift t)`] th) THEN
    MP_TAC(SPECL [`n:num`; `pastecart (x:real^3) (lift t)`] th)) THEN
  ASM_REWRITE_TAC[GE; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  EXPAND_TAC "h" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REWRITE_TAC[GSYM NORM_LIFT; LIFT_SUB] THEN CONV_TAC NORM_ARITH);;

(* ========================================================================= *)
(* Extraction on finite unions of chart pieces, chart-ball covers of compact *)
(* sets, the exhaustion, the diagonal extraction over the compact sets       *)
(* closure(W i) x [1/(i+1),i+1], and the G1 convergence p2bg_conv.           *)
(* ========================================================================= *)

let P2BX_UNION_EXTRACT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi t1 t2.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     &0 < t1 /\ t1 <= t2
     ==> !V. FINITE V /\
             (!U. U IN V ==> ?c x0 r0. c IN atlas' /\ &0 < r0 /\
                                       cball(x0,r0) SUBSET IMAGE (SND c) (FST c) /\
                                       U SUBSET IMAGE (chart_inv c) (cball(x0,r0)))
             ==> !r:num->num.
                   (!N. ?n0. !n. n0 <= n ==> N <= r n)
                   ==> ?k:num->num.
                         (!m n. m < n ==> k m < k n) /\
                         !e. &0 < e
                             ==> ?N. !m n y t.
                                       N <= m /\ N <= n /\ y IN UNIONS V /\
                                       t1 <= t /\ t <= t2
                                       ==> abs(p2b_klx (top,atlas) g p (tau(r(k m)) * t)
                                                       (phi (r(k m)) y) -
                                               p2b_klx (top,atlas) g p (tau(r(k n)) * t)
                                                       (phi (r(k n)) y)) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; UNIONS_0; FORALL_IN_INSERT; UNIONS_INSERT; IN_UNION] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `\n:num. n` THEN SIMP_TAC[] THEN MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U0:B->bool`; `V:(B->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:(B->bool)#(B->real^3)`
    (X_CHOOSE_THEN `x0:real^3` (X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
  REMOVE_THEN "IH" MP_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `r:num->num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "K1"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `c:(B->bool)#(B->real^3)`; `cball(x0:real^3,r0)`; `t1:real`; `t2:real`;
                 `\n:num. (r:num->num) ((k1:num->num) n)`] P2BX_PIECE_EXTRACT) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; CONVEX_CBALL] THEN BETA_TAC THEN ANTS_TAC THENL
   [X_GEN_TAC `M:num` THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `n1:num` o SPEC `M:num` o check (fun th ->
      can (find_term ((=) `r:num->num`)) (concl th) && is_forall (concl th) &&
      not (can (find_term ((=) `k1:num->num`)) (concl th)))) THEN
    EXISTS_TAC `n1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    ASM_MESON_TAC[MONOTONE_BIGGER];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "K2"))) THEN
  EXISTS_TAC `\m:num. (k1:num->num) ((k2:num->num) m)` THEN BETA_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `k1:num->num`)) (concl th) && is_forall (concl th))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REMOVE_THEN "K1" (MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  REMOVE_THEN "K2" (MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `MAX N1 N2` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `y:B`; `t:real`] THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= m <=> a <= m /\ b <= m`] THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `?x. x IN cball(x0:real^3,r0) /\ y = chart_inv (c:(B->bool)#(B->real^3)) x`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `U0 SUBSET IMAGE (chart_inv (c:(B->bool)#(B->real^3))) (cball(x0,r0))` THEN
      UNDISCH_TAC `(y:B) IN U0` THEN REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `k2:num->num`)) (concl th) && is_forall (concl th) &&
      can (find_term ((=) `e:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`(k2:num->num) m`; `(k2:num->num) n`; `y:B`; `t:real`] o
      check (fun th -> can (find_term ((=) `N1:num`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `N1 <= (k2:num->num) m /\ N1 <= k2 n` (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THENL
     [EXISTS_TAC `m:num`; EXISTS_TAC `n:num`] THEN
    ASM_MESON_TAC[MONOTONE_BIGGER]]);;

(* Finite covers of compact sets by chart pieces. *)

let P2BX_CHART_COVER = prove
 (`!(top':B topology) (atlas':((B->bool)#(B->real^N))->bool) K.
     smooth_manifold_atlas top' atlas' /\ compact_in top' K
     ==> ?V. FINITE V /\ K SUBSET UNIONS V /\
             !U. U IN V ==> ?c x0 r0. c IN atlas' /\ &0 < r0 /\
                                      cball(x0,r0) SUBSET IMAGE (SND c) (FST c) /\
                                      U SUBSET IMAGE (chart_inv c) (cball(x0,r0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC
   `{{y:B | y IN FST c /\ SND c y IN ball(x0,r0)} | c,x0,r0 |
     c IN (atlas':((B->bool)#(B->real^N))->bool) /\ &0 < r0 /\
     cball(x0:real^N,r0) SUBSET IMAGE (SND c) (FST c)}` o
    CONJUNCT2 o GEN_REWRITE_RULE I [compact_in]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC GRGD_CHART_PREIMAGE_OPEN THEN
      EXISTS_TAC `atlas':((B->bool)#(B->real^N))->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL; ETA_AX; PAIR];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:B) IN topspace top'` ASSUME_TAC THENL
     [MP_TAC(MATCH_MP COMPACT_IN_SUBSET_TOPSPACE (ASSUME `compact_in (top':B topology) K`)) THEN
      UNDISCH_TAC `(y:B) IN K` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `y:B`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `chart_at (atlas':((B->bool)#(B->real^N))->bool) y`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SND(chart_at (atlas':((B->bool)#(B->real^N))->bool) y) y` o
      GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL] o
      check (fun th -> is_comb(concl th) && fst(dest_const(rator(concl th))) = "open")) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`chart_at (atlas':((B->bool)#(B->real^N))->bool) y`;
                          `SND(chart_at (atlas':((B->bool)#(B->real^N))->bool) y) y`;
                          `e:real`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `V:(B->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `U:B->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `U IN {{y:B | y IN FST c /\ SND c y IN ball(x0,r0)} | c,x0,r0 |
          c IN (atlas':((B->bool)#(B->real^N))->bool) /\ &0 < r0 /\
          cball(x0:real^N,r0) SUBSET IMAGE (SND c) (FST c)}` MP_TAC THENL
   [UNDISCH_TAC `(U:B->bool) IN V` THEN
    UNDISCH_TAC
     `(V:(B->bool)->bool) SUBSET
      {{y:B | y IN FST c /\ SND c y IN ball(x0,r0)} | c,x0,r0 |
       c IN (atlas':((B->bool)#(B->real^N))->bool) /\ &0 < r0 /\
       cball(x0:real^N,r0) SUBSET IMAGE (SND c) (FST c)}` THEN
    REWRITE_TAC[SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `c:(B->bool)#(B->real^N)` THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x0:real^N` THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r0:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  EXISTS_TAC `SND(c:(B->bool)#(B->real^N)) y` THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL]);;

(* The exhaustion: increasing, and compact sets lie in a tail of it. *)

let P2BX_EXHAUST_COMPACT = prove
 (`!(top:B topology) W K.
     (!k. open_in top (W k) /\ top closure_of W k SUBSET W (SUC k)) /\
     UNIONS {W k | k IN (:num)} = topspace top /\ compact_in top K
     ==> (!k k'. k <= k' ==> W k SUBSET W k') /\
         ?i. !k. i <= k ==> K SUBSET W k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k k'. k <= k' ==> (W:num->B->bool) k SUBSET W k'` ASSUME_TAC THENL
   [SUBGOAL_THEN `!k. (W:num->B->bool) k SUBSET W (SUC k)` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(top:B topology) closure_of W(k:num)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[LE_EXISTS] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
    SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; SUBSET_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(W:num->B->bool)(k + d)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `{(W:num->B->bool) k | k IN (:num)}` o
    CONJUNCT2 o GEN_REWRITE_RULE I [compact_in] o
    check (fun th -> is_comb(concl th) && can (find_term ((=) `K:B->bool`)) (concl th) &&
                     fst(dest_const(fst(strip_comb(concl th)))) = "compact_in")) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN
    MATCH_MP_TAC COMPACT_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(B->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`W:num->B->bool`; `(:num)`; `V:(B->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> ((p <=> q) ==> r)`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(V:(B->bool)->bool) SUBSET {(W:num->B->bool) k | k IN (:num)}` THEN
    REWRITE_TAC[SIMPLE_IMAGE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `s:num->bool` num_FINITE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN EXISTS_TAC `i:num` THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS V:B->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The diagonal extraction over the compact sets closure(W i) x [1/(i+1),    *)
(* i+1] and the convergence p2bg_conv of G1.                                 *)
(* ========================================================================= *)

let P2BX_G1_EXTRACT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> ?(sub:num->num) (L:B#real->real).
           (!m n:num. m < n ==> sub m < sub n) /\
           !i e. &0 < e
                 ==> ?N. !n y t. N <= n /\ y IN top' closure_of W i /\
                                 inv(&i + &1) <= t /\ t <= &i + &1
                                 ==> abs(p2b_klx (top,atlas) g p (tau(sub n) * t)
                                                 (phi (sub n) y) - L(y,t)) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL
   [`\n (z:B#real). p2b_klx (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                      (g:real->A->real^3^3) (p:A) ((tau:num->real) n * SND z)
                      ((phi:num->B->A) n (FST z))`;
    `\i:num. {(y,t) | y IN (top':B topology) closure_of (W:num->B->bool) i /\
                      inv(&i + &1) <= t /\ t <= &i + &1}`] P2BX_DIAG_SUBSEQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `r:num->num`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(top':B topology) closure_of (W:num->B->bool) i`] P2BX_CHART_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:(B->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < inv(&i + &1) /\ inv(&i + &1) <= &i + &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                   `inv(&i + &1)`; `&i + &1`] P2BX_UNION_EXTRACT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `V:(B->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `r:num->num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num->num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `y:B`; `t:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:B) IN (top':B topology) closure_of (W:num->B->bool) i` THEN
    UNDISCH_TAC `(top':B topology) closure_of (W:num->B->bool) i SUBSET UNIONS V` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `sub:num->num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `L:B#real->real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `e:real`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `e:real`]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:B`; `t:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `(y:B,t:real)`]) THEN
  ASM_REWRITE_TAC[IN_ELIM_PAIR_THM; FST; SND]);;

(* G1, first part: a subsequence and linf with locally uniform convergence. *)

let P2BX_G1_CONV = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> ?sub linf. p3_subseq sub /\ p2bg_conv (top,atlas) g p tau top' W phi sub linf`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`]
                P2BX_G1_EXTRACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `L:B#real->real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `sub:num->num` THEN EXISTS_TAC `\t:real y:B. (L:B#real->real)(y,t)` THEN
  ASM_REWRITE_TAC[p3_subseq; p2bg_conv] THEN
  MAP_EVERY X_GEN_TAC [`K:B->bool`; `t1:real`; `t2:real`; `e:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `W:num->B->bool`; `K:B->bool`] P2BX_EXHAUST_COMPACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `i0:num`)) THEN
  MP_TAC(SPEC `t2:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `n1:num`) THEN
  MP_TAC(SPEC `t1:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t2 <= &(i0 + n1 + n2) + &1 /\ inv(&(i0 + n1 + n2) + &1) <= t1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n1` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&n2)` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i0 + n1 + n2:num`; `e:real`] o check (fun th ->
    can (find_term ((=) `L:B#real->real`)) (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + i0 + n1 + n2:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `y:B`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN W(i0 + n1 + n2:num)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(K:B->bool) SUBSET W(i0 + n1 + n2:num)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(K:B->bool) SUBSET W((sub:num->num) m)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m:num` THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[MONOTONE_BIGGER]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    MP_TAC(ISPECL [`top':B topology`; `(W:num->B->bool)(i0 + n1 + n2)`] CLOSURE_OF_SUBSET) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

