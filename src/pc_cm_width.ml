(* ========================================================================= *)
(* Unit pc_cm_width: CM_CHAIN_CM_WIDTH_STATEMENT (:A) (pc_cm_stmts): the     *)
(* statement CM_GOOD_SWEEPOUT_STATEMENT (:A) from CM_TIGHTEN, CM_COMPACTNESS *)
(* and the other statements of the width chain, through the internal         *)
(* statements of pc_cmw_defs (proved in pc_cmw_pos, pc_cmw_p15, pc_cmw_reg). *)
(*                                                                           *)
(* First CM Thm 1.14 in the embedded picture (the contradiction with         *)
(* CM_COMPACTNESS for tightened sweepouts).                                  *)
(* ========================================================================= *)

needs "src/pc_cmw_defs.ml";;
needs "src/pc_cmw_p15.ml";;

prioritize_real();;
type_invention_error := true;;

let CMW_AH_MONO = prove
 (`!S (G:real^K->real^K^K) e0 e1 eta u.
        e1 <= e0 /\ cm_almost_harmonic S G e0 eta u
        ==> cm_almost_harmonic S G e1 eta u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_almost_harmonic] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CMW_SEQ_SQUEEZE = prove
 (`!x:num->real. (!k. &0 <= x k /\ x k <= inv(&k + &1)) ==> (x ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\k. inv(&k + &1)` THEN REWRITE_TAC[REALLIM_1_OVER_N_OFFSET] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN GEN_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`]);;

let CMW_PSI_NULL = prove
 (`!(Psi:real->real) xs.
        Psi real_continuous_on {x | &0 <= x} /\ Psi(&0) = &0 /\
        (!k. &0 <= xs k) /\ (xs ---> &0) sequentially
        ==> ((\k. Psi(xs k)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_continuous_on; IN_ELIM_THM; REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l")))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REMOVE_THEN "c" (MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "l" (MP_TAC o SPEC `dd:real`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]);;

let CMW_INV_ARITH = prove
 (`!k j. 2 * k + 2 <= j ==> inv(&j + &1) + inv(&2 * &k + &2) < inv(&k + &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv(&j + &1) <= inv(&2 * &k + &3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `2 * k + 2 <= j` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * &k + &3) < inv(&2 * &k + &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV2 THEN REWRITE_TAC[REAL_OF_NUM_LE; REAL_POS] THEN
    MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * &k + &2) + inv(&2 * &k + &2) = inv(&k + &1)` ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` REAL_POS) THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* CM Thm 1.14 in the embedded picture.  gt j are the input sweepouts       *)
(* (energies below W + 1/(j+1)), ga j their tightenings (energies at most    *)
(* those of gt j, almost harmonic where gt j has energy at least W/2, with  *)
(* values in the closed set TS).  For every e there are J and delta such     *)
(* that every slice of ga j, j >= J, of area above W - delta is e-close in  *)
(* area and in the Q-trace to a nonempty finite sum of harmonic spheres in  *)
(* TS.  Proof by contradiction with CM_COMPACTNESS (CM p. 10).               *)

let CMW_THM114 = prove
 (`!S (G:real^K->real^K^K) d TS (Q:real^K->real^K^K) W e0 (Psi:real->real)
     (gt:num->real^3->real->real^K) (ga:num->real^3->real->real^K) e.
     CM_COMPACTNESS_STATEMENT (:K) /\ cm_target S G d /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
     (!z. transp(Q z) = Q z) /\
     closed TS /\ &0 < W /\ &0 < e /\ &0 < e0 /\
     Psi real_continuous_on {x | &0 <= x} /\ Psi(&0) = &0 /\
     (!u. cm_smap S u ==> cm_sarea G u <= cm_sen G u) /\
     (!j. cm_sweep S (ga j) /\
          (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> ga j y t IN TS) /\
          (!t. t IN real_interval[&0,&1]
               ==> cm_sen G (\y. ga j y t) <= cm_sen G (\y. gt j y t) /\
                   cm_sen G (\y. gt j y t) < W + inv(&j + &1) /\
                   (W / &2 <= cm_sen G (\y. gt j y t)
                    ==> cm_almost_harmonic S G e0
                          (Psi(cm_sen G (\y. gt j y t) - cm_sen G (\y. ga j y t)))
                          (\y. ga j y t))))
     ==> ?J delta. &0 < delta /\
           !j t. J <= j /\ t IN real_interval[&0,&1] /\
                 W - delta < cm_sarea G (\y. ga j y t)
                 ==> ?m v. 1 <= m /\
                           (!i. 1 <= i /\ i <= m ==> cm_sharmonic S G (v i)) /\
                           (!i y. 1 <= i /\ i <= m /\ y IN sphere(vec 0,&1) ==> v i y IN TS) /\
                           abs(cm_sarea G (\y. ga j y t) -
                               sum(1..m) (\i. cm_sarea G (v i))) < e /\
                           abs(cm_strace G Q (\y. ga j y t) -
                               sum(1..m) (\i. cm_strace G Q (v i))) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[CM_COMPACTNESS_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eSU:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cpt"))) THEN
  ABBREV_TAC `e1 = min e0 (eSU / &2)` THEN
  SUBGOAL_THEN `&0 < e1 /\ e1 < eSU /\ e1 <= e0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!k. ?j t. 2 * k + 2 <= j /\ t IN real_interval[&0,&1] /\
              W - min (W / &2) (inv(&2 * &k + &2)) <
              cm_sarea G (\y. (ga:num->real^3->real->real^K) j y t) /\
              ~(?m v. 1 <= m /\
                      (!i. 1 <= i /\ i <= m ==> cm_sharmonic S G (v i)) /\
                      (!i y. 1 <= i /\ i <= m /\ y IN sphere(vec 0,&1) ==> v i y IN TS) /\
                      abs(cm_sarea G (\y. ga j y t) -
                          sum(1..m) (\i. cm_sarea G (v i))) < e /\
                      abs(cm_strace G Q (\y. ga j y t) -
                          sum(1..m) (\i. cm_strace G Q (v i))) < e)`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`2 * k + 2`; `min (W / &2) (inv(&2 * &k + &2))`]) THEN
    SUBGOAL_THEN `&0 < min (W / &2) (inv(&2 * &k + &2))` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_INV THEN MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN REWRITE_TAC[GSYM CONJ_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `jj:num->num` (X_CHOOSE_THEN `tt:num->real` (LABEL_TAC "ch"))) THEN
  SUBGOAL_THEN
   `!k. cm_smap S (\y. (ga:num->real^3->real->real^K) ((jj:num->num) k) y ((tt:num->real) k)) /\
        cm_sen G (\y. ga ((jj:num->num) k) y ((tt:num->real) k)) <= W + &1 /\
        cm_sen G (\y. ga ((jj:num->num) k) y ((tt:num->real) k)) - inv(&k + &1) <
        cm_sarea G (\y. ga ((jj:num->num) k) y ((tt:num->real) k)) /\
        W / &2 < cm_sarea G (\y. ga ((jj:num->num) k) y ((tt:num->real) k)) /\
        &0 <= cm_sen G (\y. (gt:num->real^3->real->real^K) ((jj:num->num) k) y ((tt:num->real) k)) -
              cm_sen G (\y. ga ((jj:num->num) k) y ((tt:num->real) k)) /\
        cm_sen G (\y. gt ((jj:num->num) k) y ((tt:num->real) k)) - cm_sen G (\y. ga ((jj:num->num) k) y ((tt:num->real) k))
        <= inv(&k + &1) /\
        cm_almost_harmonic S G e1
          (Psi(cm_sen G (\y. gt ((jj:num->num) k) y ((tt:num->real) k)) - cm_sen G (\y. ga ((jj:num->num) k) y ((tt:num->real) k))))
          (\y. ga ((jj:num->num) k) y ((tt:num->real) k))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "ch" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(jj:num->num) k` o
      check (fun th -> can (find_term ((=) `ga:num->real^3->real->real^K`)) (concl th) &&
                       is_forall(concl th) &&
                       can (find_term (fun u -> is_const u &&
                              fst(dest_const u) = "cm_almost_harmonic")) (concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `(tt:num->real) k`))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `cm_smap S (\y. (ga:num->real^3->real->real^K) ((jj:num->num) k) y ((tt:num->real) k))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `cm_sweep S ((ga:num->real^3->real->real^K) ((jj:num->num) k))` THEN
      REWRITE_TAC[cm_sweep] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o SPEC `(tt:num->real) k`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `cm_sarea G (\y. (ga:num->real^3->real->real^K) ((jj:num->num) k) y ((tt:num->real) k)) <=
      cm_sen G (\y. ga ((jj:num->num) k) y ((tt:num->real) k))`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`k:num`; `(jj:num->num) k`] CMW_INV_ARITH) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `min (W / &2) (inv(&2 * &k + &2)) <= W / &2 /\
                  min (W / &2) (inv(&2 * &k + &2)) <= inv(&2 * &k + &2)`
    STRIP_ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= inv(&((jj:num->num) k) + &1) /\ inv(&((jj:num->num) k) + &1) <= &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CMW_AH_MONO THEN EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "cpt" (MP_TAC o SPECL
   [`e1:real`; `W + &1`;
    `\k y. (ga:num->real^3->real->real^K) ((jj:num->num) k) y ((tt:num->real) k)`;
    `\k. (Psi:real->real)
           (cm_sen G (\y. (gt:num->real^3->real->real^K) ((jj:num->num) k) y ((tt:num->real) k)) -
            cm_sen G (\y. (ga:num->real^3->real->real^K) ((jj:num->num) k) y ((tt:num->real) k)))`;
    `TS:real^K->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMW_PSI_NULL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CMW_SEQ_SQUEEZE THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(jj:num->num) k` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `TS:real^K->bool`)) (concl th) &&
                         can (find_term ((=) `gt:num->real^3->real->real^K`)) (concl th))) THEN
      DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `(tt:num->real) k`] o CONJUNCT1 o CONJUNCT2) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "ch" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` (X_CHOOSE_THEN `m:num`
    (X_CHOOSE_THEN `v:num->real^3->real^K` (STRIP_ASSUME_TAC o BETA_RULE)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Q:real^K->real^K^K`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `W / &2 <= sum(1..m) (\i. cm_sarea G ((v:num->real^3->real^K) i))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
    EXISTS_TAC
     `\j. cm_sarea G (\y. (ga:num->real^3->real->real^K) ((jj:num->num)((r:num->num) j)) y
                            ((tt:num->real)(r j)))` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN BETA_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `(r:num->num) j` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `e1:real`)) (concl th))) THEN
    SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= m <=> ~(m = 0)`] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `W / &2 <= sum(1..0) (\i. cm_sarea G ((v:num->real^3->real^K) i))` THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC
   `((\j. cm_sarea G (\y. (ga:num->real^3->real->real^K) ((jj:num->num)((r:num->num) j)) y ((tt:num->real)(r j))))
     ---> sum(1..m) (\i. cm_sarea G ((v:num->real^3->real^K) i))) sequentially` THEN
  UNDISCH_TAC
   `((\j. cm_strace G Q (\y. (ga:num->real^3->real->real^K) ((jj:num->num)((r:num->num) j)) y
                              ((tt:num->real)(r j))))
     ---> sum(1..m) (\i. cm_strace G Q ((v:num->real^3->real^K) i))) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  USE_THEN "ch" (MP_TAC o SPEC `(r:num->num) (N1 + N2)`) THEN
  REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `v:num->real^3->real^K`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* ========================================================================= *)
(* From the embedded picture back to the Part 4 forms (harmonic spheres,   *)
(* sweep areas); the slice bridge CMW_P4_SLICE and CMW_EMB_INV_SPHERE live *)
(* in pc_cmw_p15.                                                          *)
(* ========================================================================= *)

(* Harmonic spheres of the embedded picture with values in f(U) are Part 4 *)
(* harmonic spheres in U, with the same area and trace.                    *)

let CMW_P4_HARMONIC = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d
   (R:A->real^N^N) (Q:real^K->real^K^K) U (v:real^3->real^K).
     cm_emb (top,atlas) g f G d /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
     (!z. transp(Q z) = Q z) /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c R w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                Q(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     U SUBSET topspace top /\
     cm_sharmonic (IMAGE f (topspace top)) G v /\
     (!y. y IN sphere(vec 0,&1) ==> v y IN IMAGE f U)
     ==> p4_harmonic_sphere (top,atlas) g U (mfd_emb_inv top f o v) /\
         p4_s2_area atlas g (mfd_emb_inv top f o v) = cm_sarea G v /\
         p4_s2_trint atlas g R (mfd_emb_inv top f o v) = cm_strace G Q v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  SUBGOAL_THEN
   `!y. y IN sphere(vec 0,&1) ==> (v:real^3->real^K) y IN IMAGE (f:A->real^K) (topspace top)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `f:A->real^K`; `v:real^3->real^K`]
                CMW_EMB_INV_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext (v:real^3->real^K))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cm_sharmonic (IMAGE (f:A->real^K) (topspace top)) G v` THEN
    SIMP_TAC[cm_sharmonic; smooth_map_on];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->real^K`]
                CM_EMB_TO_P4) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `R:A->real^N^N`;
                 `Q:real^K->real^K^K`; `mfd_emb_inv top (f:A->real^K) o (v:real^3->real^K)`]
                CM_P4_BRIDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (f:A->real^K) (topspace top)`; `G:real^K->real^K^K`;
                 `Q:real^K->real^K^K`;
                 `(f:A->real^K) o (mfd_emb_inv top f o (v:real^3->real^K))`;
                 `v:real^3->real^K`] CM_SPHERE_ONLY) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                 `mfd_emb_inv top (f:A->real^K) o (v:real^3->real^K)`] CM_SHARMONIC_EQ) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[p4_harmonic_sphere] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o
    check (fun th -> can (find_term ((=) `U:A->bool`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `x:A`] CMW_EMB_INV_F) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* A uniform bound on the slice areas bounds the sweep area.                *)

let CMW_SWEEP_AREA_LE = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (sigma:real^3->real->A) B.
        (!t. t IN real_interval[&0,&1] ==> p4_s2_area atlas g (\y. sigma y t) <= B)
        ==> p4_sweep_area atlas g sigma <= B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_sweep_area] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `p4_s2_area (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                           (\y. (sigma:real^3->real->A) y (&0))` THEN
    EXISTS_TAC `&0` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* The width is an infimum; positivity of the width.                         *)
(* ========================================================================= *)

let CMW_WIDTH_APPROX = prove
 (`!top atlas (g:A->real^N^N) U e.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        p4_cm_adm (top,atlas) U /\ &0 < e
        ==> ?sigma. p4_sweepout_in (top,atlas) U sigma /\
                    p4_sweep_area atlas g sigma < p4_cm_width (top,atlas) g U + e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  MP_TAC(ISPEC
   `{p4_sweep_area (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                   (sigma:real^3->real->A) |
     sigma | p4_sweepout_in (top,atlas) U sigma}`
   INF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `p4_cm_adm (top,atlas:((A->bool)#(A->real^N))->bool) U` THEN
      REWRITE_TAC[p4_cm_adm; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN MESON_TAC[];
      EXISTS_TAC `&0` THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      REWRITE_TAC[p4_sweepout_in] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P4_SWEEP_AREA_POS THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `p4_cm_width (top,atlas:((A->bool)#(A->real^N))->bool)
                                        (g:A->real^N^N) U + e` o CONJUNCT2) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; GSYM p4_cm_width] THEN
  ASM_MESON_TAC[REAL_ARITH `&0 < e ==> ~(w + e <= w:real)`]);;

let CMW_POSITIVE = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d U.
        CMW_P15_STATEMENT (:A) (:K) /\ CMW_POS_STATEMENT (:K) /\
        cm_emb (top,atlas) g f G d /\ U IN connected_components_of top /\
        p4_cm_adm (top,atlas) U
        ==> &0 < p4_cm_width (top,atlas) g U`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "p15") (CONJUNCTS_THEN2 (LABEL_TAC "pos")
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  REMOVE_THEN "pos" (MP_TAC o SPECL [`IMAGE (f:A->real^K) (topspace top)`;
                                     `G:real^K->real^K^K`; `d:real`] o
                     REWRITE_RULE[CMW_POS_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pos"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `U:A->bool`] P4_WIDTH_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `U:A->bool`; `e / &2`] CMW_WIDTH_APPROX) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:real^3->real->A` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "p15" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
    `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `U:A->bool`;
    `sigma:real^3->real->A`; `e / &2`] o REWRITE_RULE[CMW_P15_STATEMENT]) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^3->real->real^K` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "pos" (MP_TAC o SPEC `W:real^3->real->real^K`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun u -> is_const u &&
                              fst(dest_const u) = "cm_sharmonic")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real->real^K`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                 `U:A->bool`; `W:real^3->real->real^K`; `\y:real^3 t:real. (c:real->real^K) t`]
                CMW_EMB_ESSENTIAL_HOMOTOPIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology (top:A topology) U`;
                 `\t. mfd_emb_inv (top:A topology) (f:A->real^K) ((c:real->real^K) t)`]
                CMW_ESSENTIAL_CONST_SLICES) THEN
  REWRITE_TAC[]);;

(* ========================================================================= *)
(* The input sweepouts (Prop 1.5 for nearly optimal sweepouts) and the       *)
(* transfer of the regularized output back to the manifold.                  *)
(* ========================================================================= *)

let CMW_CHOOSE_GT = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d U.
        CMW_P15_STATEMENT (:A) (:K) /\ cm_emb (top,atlas) g f G d /\
        U IN connected_components_of top /\ p4_cm_adm (top,atlas) U
        ==> ?gt:num->real^3->real->real^K.
              !j. cm_sweep (IMAGE f (topspace top)) (gt j) /\
                  (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                         ==> gt j y t IN IMAGE f U) /\
                  (!t. t IN real_interval[&0,&1]
                       ==> cm_sen G (\y. gt j y t) <
                           p4_cm_width (top,atlas) g U + inv(&j + &1) /\
                           ~cm_sharmonic (IMAGE f (topspace top)) G (\y. gt j y t)) /\
                  p4_essential (subtopology top U)
                    (p4_susp (\y t. mfd_emb_inv top f (gt j y t)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "p15") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
  SUBGOAL_THEN `&0 < inv(&j + &1) / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `U:A->bool`; `inv(&j + &1) / &2`] CMW_WIDTH_APPROX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:real^3->real->A` STRIP_ASSUME_TAC) THEN
  USE_THEN "p15" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
    `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `U:A->bool`;
    `sigma:real^3->real->A`; `inv(&j + &1) / &2`] o REWRITE_RULE[CMW_P15_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `W:real^3->real->real^K` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun u -> is_const u &&
                            fst(dest_const u) = "cm_sharmonic")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The regularized output, pulled back: a Part 4 sweepout of U, with the   *)
(* Part 4 areas and Ricci traces of the slices equal to the CM ones.        *)

let CMW_FINAL = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d U (Q:real^K->real^K^K)
     (ga:real^3->real->real^K) (Wp:real^3->real->real^K) mu rr.
     cm_emb (top,atlas) g f G d /\ U IN connected_components_of top /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
     (!z. transp(Q z) = Q z) /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c (mfd_ricci_matrix atlas g) w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                Q(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     (!z p. z IN IMAGE f (topspace top) /\ p IN IMAGE f U /\ dist(z,p) < rr
            ==> z IN IMAGE f U) /\
     mu <= rr /\
     (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> ga y t IN IMAGE f U) /\
     p4_essential (subtopology top U) (p4_susp (\y t. mfd_emb_inv top f (ga y t))) /\
     continuously_differentiable 1
       {x:real^(3,1)finite_sum |
          ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
       (\x. Wp (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) /\
     (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
             ==> Wp y (&0) = Wp y' (&0) /\ Wp y (&1) = Wp y' (&1)) /\
     (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
            ==> Wp y t IN IMAGE f (topspace top) /\ norm(Wp y t - ga y t) < mu) /\
     cm_shomotopic (IMAGE f (topspace top)) ga Wp
     ==> (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                ==> Wp y t IN IMAGE f U) /\
         p4_sweepout_in (top,atlas) U (\y t. mfd_emb_inv top f (Wp y t)) /\
         !t. t IN real_interval[&0,&1]
             ==> p4_s2_area atlas g (\y. mfd_emb_inv top f (Wp y t)) =
                 cm_sarea G (\y. Wp y t) /\
                 p4_s2_trint atlas g (mfd_ricci_matrix atlas g)
                   (\y. mfd_emb_inv top f (Wp y t)) =
                 cm_strace G Q (\y. Wp y t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`]
                CMW_COMPONENT_CLOPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
          ==> (Wp:real^3->real->real^K) y t IN IMAGE (f:A->real^K) U`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(ga:real^3->real->real^K) y t` THEN ASM_SIMP_TAC[dist] THEN
    TRANS_TAC REAL_LTE_TRANS `mu:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[p4_sweepout_in] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                     `Wp:real^3->real->real^K`] CM_SWEEP_EQ) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `t:real`] o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `Wp:real^3->real->real^K`)) (concl th) &&
                         can (find_term ((=) `U:A->bool`)) (concl th) &&
                         not (can (find_term ((=) `ga:real^3->real->real^K`)) (concl th)))) THEN
      ASM_REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `f:A->real^K`; `x:A`] CMW_EMB_INV_F) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                     `U:A->bool`; `ga:real^3->real->real^K`; `Wp:real^3->real->real^K`]
                    CMW_EMB_ESSENTIAL_HOMOTOPIC) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                   `mfd_ricci_matrix atlas (g:A->real^3^3)`; `Q:real^K->real^K^K`;
                   `Wp:real^3->real->real^K`; `t:real`] CMW_P4_SLICE) THEN
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Good sweepouts (CM Thm 1.14 with Prop 1.5, D.1 and the bridges), for one  *)
(* metric with positive width.                                               *)
(* ========================================================================= *)

let CMW_GOOD = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d U.
     CMW_P15_STATEMENT (:A) (:K) /\ CMW_REG_STATEMENT (:K) /\
     CM_TIGHTEN_STATEMENT (:K) /\ CM_COMPACTNESS_STATEMENT (:K) /\
     cm_emb (top,atlas) g f G d /\ U IN connected_components_of top /\
     p4_cm_adm (top,atlas) U /\ &0 < p4_cm_width (top,atlas) g U
     ==> !e. &0 < e
             ==> ?dd. &0 < dd /\
                     !e'. &0 < e'
                          ==> ?sigma. p4_sweepout_in (top,atlas) U sigma /\
                                      p4_sweep_area atlas g sigma
                                      < p4_cm_width (top,atlas) g U + e' /\
                                      !t. t IN real_interval[&0,&1] /\
                                          p4_cm_width (top,atlas) g U - dd
                                          < p4_s2_area atlas g (\y. sigma y t)
                                          ==> ?n v. 1 <= n /\
                                                (!i. 1 <= i /\ i <= n
                                                     ==> p4_harmonic_sphere (top,atlas) g U
                                                           (v i)) /\
                                                abs(p4_s2_area atlas g (\y. sigma y t) -
                                                    sum(1..n) (\i. p4_s2_area atlas g (v i)))
                                                < e /\
                                                abs(p4_s2_trint atlas g
                                                      (mfd_ricci_matrix atlas g)
                                                      (\y. sigma y t) -
                                                    sum(1..n) (\i. p4_s2_trint atlas g
                                                                (mfd_ricci_matrix atlas g)
                                                                (v i)))
                                                < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "p15") (CONJUNCTS_THEN2 (LABEL_TAC "reg")
    (CONJUNCTS_THEN2 (LABEL_TAC "tight") (CONJUNCTS_THEN2 (LABEL_TAC "cpt")
      STRIP_ASSUME_TAC)))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                 `U:A->bool`] CMW_COMPONENT_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `rr:real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`]
                CM_AMBIENT_RICCI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:real^K->real^K^K` STRIP_ASSUME_TAC) THEN
  USE_THEN "reg" (MP_TAC o SPECL [`IMAGE (f:A->real^K) (topspace top)`;
                                  `G:real^K->real^K^K`; `d:real`] o
                  REWRITE_RULE[CMW_REG_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ae") (LABEL_TAC "d1")) THEN
  USE_THEN "tight" (MP_TAC o SPECL [`IMAGE (f:A->real^K) (topspace top)`;
                                    `G:real^K->real^K^K`; `d:real`] o
                    REWRITE_RULE[CM_TIGHTEN_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `Psi:real->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tg"))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                 `U:A->bool`] CMW_CHOOSE_GT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gt:num->real^3->real->real^K` (LABEL_TAC "gt")) THEN
  ABBREV_TAC `W = p4_cm_width (top,atlas) (g:A->real^3^3) U` THEN
  SUBGOAL_THEN
   `?ga:num->real^3->real->real^K.
      !j. cm_sweep (IMAGE (f:A->real^K) (topspace top)) (ga j) /\
          cm_shomotopic (IMAGE f (topspace top)) (gt j) (ga j) /\
          (!t. t IN real_interval[&0,&1]
               ==> cm_sen G (\y. ga j y t) <= cm_sen G (\y. gt j y t)) /\
          (!t. t IN real_interval[&0,&1] /\ W / &2 <= cm_sen G (\y. gt j y t)
               ==> cm_almost_harmonic (IMAGE f (topspace top)) G e0
                     (Psi(cm_sen G (\y. gt j y t) - cm_sen G (\y. ga j y t)))
                     (\y. ga j y t))`
  (X_CHOOSE_THEN `ga:num->real^3->real->real^K` (LABEL_TAC "ga")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
    USE_THEN "tg" (MP_TAC o SPECL [`(gt:num->real^3->real->real^K) j`; `W:real`]) THEN
    ANTS_TAC THENL
     [USE_THEN "gt" (MP_TAC o SPEC `j:num`) THEN ASM_SIMP_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
               ==> (ga:num->real^3->real->real^K) j y t IN IMAGE (f:A->real^K) U) /\
        p4_essential (subtopology top U)
          (p4_susp (\y t. mfd_emb_inv top f (ga j y t)))`
  (LABEL_TAC "gaU") THENL
   [X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                   `U:A->bool`; `(gt:num->real^3->real->real^K) j`;
                   `(ga:num->real^3->real->real^K) j`] CMW_EMB_ESSENTIAL_HOMOTOPIC) THEN
    USE_THEN "gt" (MP_TAC o SPEC `j:num`) THEN USE_THEN "ga" (MP_TAC o SPEC `j:num`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:A->real^K) (topspace top)`; `G:real^K->real^K^K`; `d:real`;
                 `IMAGE (f:A->real^K) U`; `Q:real^K->real^K^K`; `W:real`; `e0:real`;
                 `Psi:real->real`; `gt:num->real^3->real->real^K`;
                 `ga:num->real^3->real->real^K`; `e / &2`] CMW_THM114) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_HALF] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `j:num` THEN USE_THEN "ga" (MP_TAC o SPEC `j:num`) THEN
      USE_THEN "gt" (MP_TAC o SPEC `j:num`) THEN USE_THEN "gaU" (MP_TAC o SPEC `j:num`) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num` (X_CHOOSE_THEN `delta:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "close")))) THEN
  EXISTS_TAC `delta / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `e':real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e' / &2` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `j = J + N:num` THEN
  SUBGOAL_THEN `inv(&j + &1) < e' / &2 /\ J <= j` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "j" THEN ARITH_TAC] THEN
    TRANS_TAC REAL_LET_TRANS `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    UNDISCH_TAC `~(N = 0)` THEN EXPAND_TAC "j" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_EQ] THEN
    MP_TAC(SPEC `N:num` REAL_POS) THEN MP_TAC(SPEC `J:num` REAL_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `mu = min (min (e' / &2) (delta / &2)) (min (e / &2) rr)` THEN
  SUBGOAL_THEN
   `&0 < mu /\ mu <= e' / &2 /\ mu <= delta / &2 /\ mu <= e / &2 /\ mu <= rr`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "mu" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "d1" (MP_TAC o SPECL [`Q:real^K->real^K^K`;
                                 `(ga:num->real^3->real->real^K) j`; `mu:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "ga" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Wp:real^3->real->real^K` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                 `U:A->bool`; `Q:real^K->real^K^K`; `(ga:num->real^3->real->real^K) j`;
                 `Wp:real^3->real->real^K`; `mu:real`; `rr:real`] CMW_FINAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "gaU" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq"))) THEN
  EXISTS_TAC `\y t. mfd_emb_inv top (f:A->real^K) ((Wp:real^3->real->real^K) y t)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> abs(cm_sarea G (\y. (Wp:real^3->real->real^K) y t) -
                cm_sarea G (\y. (ga:num->real^3->real->real^K) j y t)) < mu /\
            abs(cm_strace G Q (\y. Wp y t) - cm_strace G Q (\y. ga j y t)) < mu /\
            cm_sarea G (\y. ga j y t) <= cm_sen G (\y. ga j y t) /\
            cm_sen G (\y. ga j y t) <= cm_sen G (\y. (gt:num->real^3->real->real^K) j y t) /\
            cm_sen G (\y. gt j y t) < W + inv(&j + &1)`
  (LABEL_TAC "facts") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `mu:real`)) (concl th) &&
                       can (find_term (fun u -> is_const u &&
                              fst(dest_const u) = "cm_strace")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "ae" MATCH_MP_TAC THEN
      USE_THEN "ga" (MP_TAC o SPEC `j:num`) THEN
      REWRITE_TAC[cm_sweep] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT1) THEN
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[];
      USE_THEN "ga" (MP_TAC o SPEC `j:num`) THEN ASM_SIMP_TAC[];
      USE_THEN "gt" (MP_TAC o SPEC `j:num`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `W + inv(&j + &1) + mu` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CMW_SWEEP_AREA_LE THEN BETA_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "eq" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`) o
                   SPEC `t:real`) THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    USE_THEN "facts" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`) o
                      SPEC `t:real`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  USE_THEN "eq" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`) o
                 SPEC `t:real`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                                        REWRITE_TAC[th]) (fun th -> REWRITE_TAC[th])) THEN
  USE_THEN "facts" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`) o
                    SPEC `t:real`) THEN
  STRIP_TAC THEN
  USE_THEN "close" (MP_TAC o SPECL [`j:num`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `v:num->real^3->real^K`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= m
        ==> p4_harmonic_sphere (top,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) U
              (mfd_emb_inv top (f:A->real^K) o (v:num->real^3->real^K) i) /\
            p4_s2_area atlas g (mfd_emb_inv top f o v i) = cm_sarea G (v i) /\
            p4_s2_trint atlas g (mfd_ricci_matrix atlas g) (mfd_emb_inv top f o v i) =
            cm_strace G Q (v i)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMW_P4_HARMONIC THEN
    EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`]
                  CMW_COMPONENT_CLOPEN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`m:num`; `\i. mfd_emb_inv top (f:A->real^K) o (v:num->real^3->real^K) i`] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `sum(1..m) (\i. p4_s2_area (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
                     (mfd_emb_inv top (f:A->real^K) o (v:num->real^3->real^K) i)) =
    sum(1..m) (\i. cm_sarea G (v i)) /\
    sum(1..m) (\i. p4_s2_trint atlas g (mfd_ricci_matrix atlas g)
                     (mfd_emb_inv top f o v i)) =
    sum(1..m) (\i. cm_strace G Q (v i))`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* CM_GOOD_SWEEPOUT_STATEMENT from the internal statements, CM_TIGHTEN and   *)
(* CM_COMPACTNESS (embedding into real^7 by CM_EMB_EXISTS).                  *)
(* ========================================================================= *)

let CMW_GOOD_SWEEPOUT_FROM = prove
 (`CMW_P15_STATEMENT (:A) (:7) /\ CMW_POS_STATEMENT (:7) /\ CMW_REG_STATEMENT (:7) /\
   CM_TIGHTEN_STATEMENT (:7) /\ CM_COMPACTNESS_STATEMENT (:7)
   ==> CM_GOOD_SWEEPOUT_STATEMENT (:A)`,
  STRIP_TAC THEN REWRITE_TAC[CM_GOOD_SWEEPOUT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `U:A->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(topspace (top:A topology) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] NONEMPTY_CONNECTED_COMPONENTS_OF) THEN
    MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`] (INST_TYPE [`:7`,`:K`] CM_EMB_EXISTS)) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; DIMINDEX_CONV `dimindex(:7)`] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^7` (X_CHOOSE_THEN `G:real^7->real^7^7`
    (X_CHOOSE_TAC `d:real`))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `f:A->real^7`; `G:real^7->real^7^7`; `d:real`;
                 `U:A->bool`] CMW_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(INST_TYPE [`:7`,`:K`] CMW_GOOD) THEN
  MAP_EVERY EXISTS_TAC [`f:A->real^7`; `G:real^7->real^7^7`; `d:real`] THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* The chain statement CM_CHAIN_CM_WIDTH_STATEMENT (:A) from                 *)
(* CMW_GOOD_SWEEPOUT_FROM and the three internal theorems CMW_P15            *)
(* (pc_cmw_p15), CMW_POS (pc_cmw_pos) and CMW_REG (pc_cmw_reg).              *)
(* ========================================================================= *)

let CM_CHAIN_CM_WIDTH = prove
 (`CM_CHAIN_CM_WIDTH_STATEMENT (:A)`,
  REWRITE_TAC[CM_CHAIN_CM_WIDTH_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC CMW_GOOD_SWEEPOUT_FROM THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMW_P15 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMW_POS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMW_REG THEN ASM_REWRITE_TAC[]]);;

let CM_CHAIN_CM_WIDTH_ALL = prove
 (`!aa:A->bool. CM_CHAIN_CM_WIDTH_STATEMENT aa`,
  GEN_TAC THEN MP_TAC CM_CHAIN_CM_WIDTH THEN REWRITE_TAC[CM_CHAIN_CM_WIDTH_STATEMENT]);;

