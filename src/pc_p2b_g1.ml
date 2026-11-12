(* ========================================================================= *)
(* Unit pc_p2b_g1 (Part 2B): the route theorem P2B_W920_G1_ROUTE of the      *)
(* statements-only unit pc_p2b_w920g: W3 and Cor 9.10 give G1 (MT Section    *)
(* 2.2 with Claim 9.15 and Cor 9.16): a subsequence and linf with locally    *)
(* uniform convergence (pc_p2b_g1a), and on every chart box of the limit the *)
(* chart data of the local limit lemma for a tail of the subsequence         *)
(* (pc_p2b_g1b: members and weak forms; pc_p2b_g1c: convergence and uniform  *)
(* bounds).                                                                  *)
(* ========================================================================= *)

needs "src/pc_p2b_g1c.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The chart data on a box and the route.                                    *)
(* ========================================================================= *)

let P2BX_UNILIP_LOCLIP = prove
 (`!(om:real^(N,1)finite_sum->bool) f. p2bw_unilip om f ==> !n. wan_loclip om (f n)`,
  REWRITE_TAC[p2bw_unilip; wan_loclip] THEN MESON_TAC[]);;

let P2BX_G1_CDATA = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c om.
     P2B_REQ_P2A_WEAK_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p3_subseq sub /\ p2bg_conv (top,atlas) g p tau top' W phi sub linf /\
     c IN atlas' /\ p2bg_cbox c om
     ==> ?m0. p2bg_cdata (top,atlas) g p tau atlas' g' phi c om (\j. sub(m0 + j)) linf`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bg_cbox]) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(B->bool)#(B->real^3)`; `closure om:real^(3,1)finite_sum->bool`;
                 `closure om:real^(3,1)finite_sum->bool`] P2BX_BOX_COMPACT) THEN
  ASM_REWRITE_TAC[CLOSURE_CLOSURE; SUBSET_REFL; COMPACT_CLOSURE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                 `IMAGE fstcart (closure om:real^(3,1)finite_sum->bool)`] P2BX_BOX_MEMBERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "MB") o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                 `om:real^(3,1)finite_sum->bool`] P2BX_BOX_UNILIP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k2:num` (LABEL_TAC "UL")) THEN
  EXISTS_TAC `k1 + k2:num` THEN
  ABBREV_TAC `ix = \j:num. (sub:num->num)((k1 + k2) + j)` THEN
  SUBGOAL_THEN `!n. k1 <= (ix:num->num) n /\ k2 <= ix n /\ n <= ix n` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "ix" THEN
    MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[p3_subseq]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(k1 + k2) + n:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!N. ?n0. !n. n0 <= n ==> N <= (ix:num->num) n` ASSUME_TAC THENL
   [X_GEN_TAC `N:num` THEN EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "UL" (MP_TAC o SPEC `ix:num->num`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the members on the box *)
  SUBGOAL_THEN
   `!m. (\z. (vectorize:real^3^3->real^(3,3)finite_prod)
              (p2bg_smet atlas (g:real->A->real^3^3) tau (phi:num->B->A) c ix m z))
        continuous_on om /\
        (!z. z IN om
             ==> transp(p2bg_smet atlas g tau phi c ix m z) = p2bg_smet atlas g tau phi c ix m z /\
                 !v. ~(v = vec 0) ==> &0 < v dot (p2bg_smet atlas g tau phi c ix m z ** v)) /\
        (\z. lift(p2bg_sscal atlas g tau phi c ix m z)) continuous_on om /\
        (wan_loclip om (p2bg_sfun (top,atlas) g p tau phi c ix m)
         ==> p2bw_t1 om (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)) %%
                             matrix_inv(p2bg_smet atlas g tau phi c ix m z))
                        (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)))
                        (p2bg_sscal atlas g tau phi c ix m) (p2bg_sfun (top,atlas) g p tau phi c ix m) /\
             p2bw_t2 om (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)) %%
                             matrix_inv(p2bg_smet atlas g tau phi c ix m z))
                        (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)))
                        (p2bg_sscal atlas g tau phi c ix m) (p2bg_sfun (top,atlas) g p tau phi c ix m)) /\
        p2bw_tid om (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)) %%
                          matrix_inv(p2bg_smet atlas g tau phi c ix m z))
                     (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)))
                     (p2bg_sscal atlas g tau phi c ix m) (p2bg_sfun (top,atlas) g p tau phi c ix m)`
  (LABEL_TAC "MEM") THENL
   [X_GEN_TAC `m:num` THEN
    USE_THEN "MB" (MP_TAC o SPEC `(ix:num->num) m`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
    MP_TAC(ISPECL
     [`u:A->bool`; `kappa:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:real->A->real^3^3`; `p:A`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
      `(W:num->B->bool) ((ix:num->num) m)`; `(phi:num->B->A) ((ix:num->num) m)`; `psi:A->B`;
      `c:(B->bool)#(B->real^3)`; `(tau:num->real) ((ix:num->num) m)`;
      `--((tau:num->real) ((ix:num->num) m) * (t2 + &1))`; `om:real^(3,1)finite_sum->bool`;
      `p2bg_smet atlas (g:real->A->real^3^3) tau (phi:num->B->A) c ix m`;
      `p2bg_sscal atlas (g:real->A->real^3^3) tau (phi:num->B->A) c ix m`;
      `p2bg_sfun (top,atlas) (g:real->A->real^3^3) p tau (phi:num->B->A) c ix m`]
     P2BX_MEMBER_BOX) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; p2bg_smet; p2bg_sscal; p2bg_sfun; REAL_NEG_NEG] THEN
    SUBGOAL_THEN `&0 < (tau:num->real) ((ix:num->num) m)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> --x < &0`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^(3,1)finite_sum) IN closure om` ASSUME_TAC THENL
     [MP_TAC(ISPEC `om:real^(3,1)finite_sum->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `t1 <= drop(sndcart(z:real^(3,1)finite_sum)) /\ drop(sndcart z) <= t2`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)`
      ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET; FUN_IN_IMAGE]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum))` THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `IMAGE (chart_inv (c:(B->bool)#(B->real^3)))
                     (IMAGE fstcart (closure om:real^(3,1)finite_sum->bool)) SUBSET
                   (W:num->B->bool) ((ix:num->num) m)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[p2bg_cdata] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MATCH_MP_TAC P2BX_BOX_METRIC_CONV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `p:A`; `q:num->A`; `top':B topology`;
                          `xl:B`; `W:num->B->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BX_BOX_SCAL_CONV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `p:A`; `q:num->A`; `top':B topology`;
                          `xl:B`; `W:num->B->bool`] THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    EXPAND_TAC "ix" THEN MATCH_MP_TAC P2BX_BOX_FUN_CONV THEN
    MAP_EVERY EXISTS_TAC [`q:num->A`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `m:num` THEN USE_THEN "MEM" (MP_TAC o SPEC `m:num`) THEN
    FIRST_ASSUM(ASSUME_TAC o SPEC `m:num` o MATCH_MP P2BX_UNILIP_LOCLIP o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bw_unilip")) (concl th))) THEN
    ASM_SIMP_TAC[]]);;

(* The route: W3 and Cor 9.10 give G1. *)

let P2B_W920_G1_ROUTE = prove
 (`!(u:A->bool) (w:B->bool). P2B_W920_G1_ROUTE_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_W920_G1_ROUTE_STATEMENT; P2B_W920_G1_STATEMENT] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                       `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                       `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`]
                P2BX_G1_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `linf:real->B->real`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `linf:real->B->real`] THEN
  ASM_REWRITE_TAC[p2bg_g1out] THEN
  MAP_EVERY X_GEN_TAC [`c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`] THEN
  STRIP_TAC THEN MATCH_MP_TAC P2BX_G1_CDATA THEN
  MAP_EVERY EXISTS_TAC [`q:num->A`; `top':B topology`; `xl:B`; `W:num->B->bool`] THEN
  ASM_REWRITE_TAC[]);;

