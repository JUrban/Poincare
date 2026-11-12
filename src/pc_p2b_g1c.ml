(* ========================================================================= *)
(* Unit pc_p2b_g1c (Part 2B): convergence of the member data of the G1       *)
(* sequence on a chart box of the limit (vocabulary of pc_p2b_w920g):        *)
(* locally uniform convergence of the member metrics (from the C^0 chart     *)
(* convergence P2BX_G1_C0) and of the scalar curvatures                      *)
(* (LCK_CURVATURE_STABILITY), uniform Lipschitz bounds of the member reduced *)
(* distances (Cor 9.10 via P2BX_G1_PIECE_BOUNDS), and the locally uniform    *)
(* convergence of the reduced distances to linf.                             *)
(* ========================================================================= *)

needs "src/pc_p2b_g1b.ml";;
needs "src/pc_p2b_p920.ml";;
needs "src/pc_rfa_mfd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Compact subsets of chart boxes.                                           *)
(* ========================================================================= *)

let P2BX_BOX_COMPACT = prove
 (`!(c:(B->bool)#(B->real^N)) (om:real^(N,1)finite_sum->bool) k.
     closure om SUBSET {z | fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)} /\
     compact k /\ k SUBSET om
     ==> compact (IMAGE fstcart k) /\ IMAGE fstcart k SUBSET IMAGE (SND c) (FST c) /\
         ?t1 t2. &0 < t1 /\ t1 <= t2 /\
                 !z. z IN k ==> t1 <= drop(sndcart z) /\ drop(sndcart z) <= t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^(N,1)finite_sum. z IN k
                  ==> fstcart z IN IMAGE (SND(c:(B->bool)#(B->real^N))) (FST c) /\
                      &0 < drop(sndcart z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^(N,1)finite_sum) IN closure om` MP_TAC THENL
     [MP_TAC(ISPEC `om:real^(N,1)finite_sum->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
      UNDISCH_TAC `closure om SUBSET
                   {z:real^(N,1)finite_sum | fstcart z IN IMAGE (SND(c:(B->bool)#(B->real^N))) (FST c) /\
                                             &0 < drop(sndcart z)}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[LINEAR_FSTCART];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `k:real^(N,1)finite_sum->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`&1`; `&1`] THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE lift (IMAGE (\z:real^(N,1)finite_sum. drop(sndcart z)) k))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[LINEAR_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (\z:real^(N,1)finite_sum. drop(sndcart z)) k = {})` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\z:real^(N,1)finite_sum. drop(sndcart z)) k` COMPACT_ATTAINS_INF) THEN
  MP_TAC(ISPEC `IMAGE (\z:real^(N,1)finite_sum. drop(sndcart z)) k` COMPACT_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z2:real^(N,1)finite_sum` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:real^(N,1)finite_sum` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`drop(sndcart(z1:real^(N,1)finite_sum))`;
                        `drop(sndcart(z2:real^(N,1)finite_sum))`] THEN
  ASM_SIMP_TAC[]);;

(* Compact subsets of a limit chart are eventually inside the W k, where   *)
(* phi k is a diffeomorphism onto its image.                                 *)

let P2BX_BOX_MEMBERS = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi c K.
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     c IN atlas' /\ compact K /\ K SUBSET IMAGE (SND c) (FST c)
     ==> compact_in top' (IMAGE (chart_inv c) K) /\
         ?k0. !k. k0 <= k
                  ==> IMAGE (chart_inv c) K SUBSET W k /\
                      (?psi. mfd_diffeo top' atlas' (W k) top atlas
                                        (IMAGE (phi k) (W k)) (phi k) psi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
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
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`&1`; `&1`; `IMAGE (chart_inv (c:(B->bool)#(B->real^3))) K`; `0`; `&1`] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2"))
                         (concl th))) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The member metrics converge locally uniformly on a chart box to the limit *)
(* chart metric (cdata clause B).                                            *)
(* ========================================================================= *)

(* The limit chart data on a box. *)

let P2BX_BOX_LIMIT_DATA = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi c om.
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     c IN atlas' /\ p2bg_cbox c om
     ==> (\z. (vectorize:real^3^3->real^(3,3)finite_prod) (p2bw_cmet atlas' c (&1) g' z))
         continuous_on om /\
         (\z. lift(p2bw_cscal atlas' c (&1) g' z)) continuous_on om /\
         (!z. z IN om
              ==> transp(p2bw_cmet atlas' c (&1) g' z) = p2bw_cmet atlas' c (&1) g' z /\
                  !v. ~(v = vec 0) ==> &0 < v dot (p2bw_cmet atlas' c (&1) g' z ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_LIMIT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bg_cbox]) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `c:(B->bool)#(B->real^3)`;
                 `om:real^(3,1)finite_sum->bool`] (INST_TYPE [`:B`,`:A`] P2BX_LIMIT_CHART_DATA)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[P2B_FLOW_CHART] THEN
    MP_TAC(ISPEC `om:real^(3,1)finite_sum->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o check (fun th ->
      is_comb(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "vectorize")) (concl th))) THEN
    REWRITE_TAC[o_DEF];
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]]);;

let P2BX_BOX_METRIC_CONV = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi c om (ix:num->num).
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     c IN atlas' /\ p2bg_cbox c om /\ (!N. ?n0. !n. n0 <= n ==> N <= ix n)
     ==> p2bw_locunif_m om (p2bg_smet atlas g tau phi c ix) (p2bw_cmet atlas' c (&1) g')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[p2bw_locunif_m; p2bw_locunif] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`k:real^(3,1)finite_sum->bool`; `e:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                 `om:real^(3,1)finite_sum->bool`] P2BX_BOX_LIMIT_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bg_cbox]) THEN
  MP_TAC(ISPECL [`c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`;
                 `k:real^(3,1)finite_sum->bool`] P2BX_BOX_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC)))) THEN
  (* bounds of the diagonal entries of the limit metric on k *)
  SUBGOAL_THEN
   `!i'. 1 <= i' /\ i' <= dimindex(:3)
         ==> ?B. &0 <= B /\ !z. z IN k ==> abs(p2bw_cmet atlas' c (&1) (g':real->B->real^3^3) z$i'$i') <= B`
  MP_TAC THENL
   [X_GEN_TAC `i':num` THEN STRIP_TAC THEN MATCH_MP_TAC P2BW_CONT_BOUND THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `om:real^(3,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                        (p2bw_cmet atlas' c (&1) (g':real->B->real^3^3) z)) continuous_on om` THEN
    REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j:num` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Bj:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `Bi:real` STRIP_ASSUME_TAC) THEN
  (* the C^0 estimate *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                 `IMAGE fstcart (k:real^(3,1)finite_sum->bool)`; `t1:real`; `t2:real`;
                 `e / (Bi + Bj + &1)`] P2BX_G1_C0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "C0")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                 `IMAGE fstcart (k:real^(3,1)finite_sum->bool)`] P2BX_BOX_MEMBERS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "MB") o CONJUNCT2) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k0 + k1:num` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `ix:num->num`)) (concl th))) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^(3,1)finite_sum`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `k0 <= (ix:num->num) n /\ k1 <= ix n` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "MB" (MP_TAC o SPEC `(ix:num->num) n`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
  USE_THEN "C0" (MP_TAC o SPEC `(ix:num->num) n`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN IMAGE fstcart (k:real^(3,1)finite_sum->bool) /\
                t1 <= drop(sndcart z) /\ drop(sndcart z) <= t2`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(GEN `w:real^3`
    (MP (SPECL [`fstcart(z:real^(3,1)finite_sum)`; `drop(sndcart(z:real^(3,1)finite_sum))`;
                `w:real^3`] (CONJUNCT2 th))
        (ASSUME `fstcart(z:real^(3,1)finite_sum) IN IMAGE fstcart (k:real^(3,1)finite_sum->bool) /\
                 t1 <= drop(sndcart z) /\ drop(sndcart z) <= t2`)))) THEN
  (* symmetry of the member metric *)
  SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER W((ix:num->num) n))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)`
    ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET; FUN_IN_IMAGE]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum))` THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `IMAGE (chart_inv (c:(B->bool)#(B->real^3))) (IMAGE fstcart (k:real^(3,1)finite_sum->bool)) SUBSET
                 W((ix:num->num) n)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3)(--(tau((ix:num->num) n) * drop(sndcart(z:real^(3,1)finite_sum))))`;
                 `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER W((ix:num->num) n))`;
                 `(phi:num->B->A) ((ix:num->num) n) o chart_inv(c:(B->bool)#(B->real^3))`]
                APX_RFS_PULLBACK_FIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --x <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `t1:real` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC P2BX_PARAM_EMBED THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                            `IMAGE ((phi:num->B->A)((ix:num->num) n)) (W(ix n))`; `psi:A->B`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `fstcart(z:real^(3,1)finite_sum)` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `(z:real^(3,1)finite_sum) IN om` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p2bg_smet atlas (g:real->A->real^3^3) tau (phi:num->B->A) (c:(B->bool)#(B->real^3)) ix n z -
     p2bw_cmet atlas' c (&1) (g':real->B->real^3^3) z`;
    `p2bw_cmet atlas' (c:(B->bool)#(B->real^3)) (&1) (g':real->B->real^3^3) z`;
    `e / (Bi + Bj + &1)`; `i:num`; `j:num`] P2BX_ENTRY_FROM_QF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[TRANSP_MATRIX_SUB] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP th (ASSUME `(z:real^(3,1)finite_sum) IN om`))]) THEN
      REWRITE_TAC[p2bg_smet; TRANSP_MATRIX_CMUL] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^3` THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RSUB; p2bg_smet; p2bw_cmet] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `e / (Bi + Bj + &1)`)) (concl th))) THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_SUB_COMPONENT] THEN
  MATCH_MP_TAC(REAL_ARITH `y < e ==> x <= y ==> x < e`) THEN
  SUBGOAL_THEN `p2bw_cmet atlas' (c:(B->bool)#(B->real^3)) (&1) (g':real->B->real^3^3) z$i$i +
                p2bw_cmet atlas' c (&1) g' z$j$j <= Bi + Bj` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs x <= a /\ abs y <= b ==> x + y <= a + b`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Bi + Bj + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e * inv(Bi + Bj + &1) * (Bi + Bj) * inv(&2)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `e * inv(Bi + Bj + &1) * (Bi + Bj) * inv(&2) =
                e * ((Bi + Bj) / (Bi + Bj + &1)) / &2` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(Bi + Bj) / (Bi + Bj + &1) < &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (Bi + Bj) / (Bi + Bj + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e /\ e * r <= e * &1 ==> e * r / &2 < e`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The member reduced distances converge locally uniformly on a chart box to *)
(* linf (cdata clause E).                                                    *)
(* ========================================================================= *)

let P2BX_BOX_FUN_CONV = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c om m0.
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_conv (top,atlas) g p tau top' W phi sub linf /\
     c IN atlas' /\ p2bg_cbox c om
     ==> p2bw_locunif om (p2bg_sfun (top,atlas) g p tau phi c (\j. sub(m0 + j)))
                         (p2bw_cfun c linf)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bw_locunif] THEN
  MAP_EVERY X_GEN_TAC [`k:real^(3,1)finite_sum->bool`; `e:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bg_cbox]) THEN
  MP_TAC(ISPECL [`c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`;
                 `k:real^(3,1)finite_sum->bool`] P2BX_BOX_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                 `IMAGE fstcart (k:real^(3,1)finite_sum->bool)`] P2BX_BOX_MEMBERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`IMAGE (chart_inv (c:(B->bool)#(B->real^3))) (IMAGE fstcart (k:real^(3,1)finite_sum->bool))`;
    `t1:real`; `t2:real`; `e:real`] o REWRITE_RULE[p2bg_conv] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_conv")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `m1:num`) THEN EXISTS_TAC `m1:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^(3,1)finite_sum`] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bg_sfun; p2bw_cfun] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m0 + n:num`; `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum))`;
                                `drop(sndcart(z:real^(3,1)finite_sum))`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_ARITH_TAC; SIMP_TAC[]]);;

(* ========================================================================= *)
(* Uniform Lipschitz bounds of the member reduced distances on a chart box   *)
(* (cdata clause D), from the piecewise bounds of Cor 9.10                   *)
(* (P2BX_G1_PIECE_BOUNDS) on finitely many chart balls.                      *)
(* ========================================================================= *)

(* Piecewise bounds on a finite cover by half balls give a global          *)
(* Lipschitz bound (near points lie in one ball, far points use the bound). *)

let P2BX_PIECES_LIP = prove
 (`!(ff:real^(N,1)finite_sum->real) S J (cs:num->real^N) rs C b d.
     &0 < d /\ &0 <= C /\ &0 <= b /\
     (!j. 1 <= j /\ j <= J ==> d <= rs j / &2) /\
     (!z. z IN S ==> ?j. 1 <= j /\ j <= J /\ fstcart z IN ball(cs j, rs j / &2)) /\
     (!j z. 1 <= j /\ j <= J /\ z IN S /\ fstcart z IN cball(cs j, rs j)
            ==> &0 <= ff z /\ ff z <= C) /\
     (!j z w. 1 <= j /\ j <= J /\ z IN S /\ w IN S /\
              fstcart z IN cball(cs j, rs j) /\ fstcart w IN cball(cs j, rs j)
              ==> abs(ff z - ff w) <=
                  b * (norm(fstcart z - fstcart w) + abs(drop(sndcart z) - drop(sndcart w))))
     ==> !z w. z IN S /\ w IN S ==> abs(ff z - ff w) <= (&2 * b + &2 * C / d) * norm(z - w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`z:real^(N,1)finite_sum`; `w:real^(N,1)finite_sum`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^(N,1)finite_sum. y IN S
                  ==> ?j. 1 <= j /\ j <= J /\ fstcart y IN ball((cs:num->real^N) j, rs j / &2) /\
                          fstcart y IN cball(cs j, rs j)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^(N,1)finite_sum` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `fstcart(y:real^(N,1)finite_sum) IN ball((cs:num->real^N) j, rs j / &2)` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL] THEN
    SUBGOAL_THEN `d <= (rs:num->real) j / &2` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:real^(N,1)finite_sum`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^(N,1)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= (ff:real^(N,1)finite_sum->real) z /\ ff z <= C /\ &0 <= ff w /\ ff w <= C`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM((fun th -> MP_TAC(SPECL [`j:num`; `z:real^(N,1)finite_sum`] th) THEN
                            MP_TAC(SPECL [`j':num`; `w:real^(N,1)finite_sum`] th)) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `C:real`)) (concl th) &&
      not (can (find_term ((=) `b:real`)) (concl th)))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= norm(z - w:real^(N,1)finite_sum)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * C / d * norm(z - w:real^(N,1)finite_sum)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  ASM_CASES_TAC `norm(z - w:real^(N,1)finite_sum) < d` THENL
   [SUBGOAL_THEN `norm(fstcart(z:real^(N,1)finite_sum) - fstcart w) <= norm(z - w) /\
                  abs(drop(sndcart(z:real^(N,1)finite_sum)) - drop(sndcart w)) <= norm(z - w)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM FSTCART_SUB; GSYM SNDCART_SUB; GSYM DROP_SUB; NORM_FSTCART] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(sndcart(z - w:real^(N,1)finite_sum))` THEN
      REWRITE_TAC[NORM_SNDCART] THEN REWRITE_TAC[NORM_REAL; GSYM drop; REAL_LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `fstcart(w:real^(N,1)finite_sum) IN cball((cs:num->real^N) j, rs j)` ASSUME_TAC THENL
     [UNDISCH_TAC `fstcart(z:real^(N,1)finite_sum) IN ball((cs:num->real^N) j, rs j / &2)` THEN
      REWRITE_TAC[IN_BALL; IN_CBALL] THEN
      SUBGOAL_THEN `d <= (rs:num->real) j / &2` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`(cs:num->real^N) j`; `fstcart(z:real^(N,1)finite_sum)`;
                     `fstcart(w:real^(N,1)finite_sum)`] DIST_TRIANGLE) THEN
      REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `z:real^(N,1)finite_sum`; `w:real^(N,1)finite_sum`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `b:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= c ==> a <= x ==> a <= y + c`) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b * u <= b * (&2 * n) ==> b * u <= &2 * b * n`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C <= C / d * norm(z - w:real^(N,1)finite_sum)` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * b * norm(z - w:real^(N,1)finite_sum)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC);;

let P2BX_BOX_UNILIP = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi c om.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     c IN atlas' /\ p2bg_cbox c om
     ==> ?k0. !ix:num->num. (!n. k0 <= ix n)
                ==> p2bw_unilip om (p2bg_sfun (top,atlas) g p tau phi c ix)`,
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
  MP_TAC(ISPECL [`IMAGE fstcart (closure om:real^(3,1)finite_sum->bool)`;
                 `\(x:real^3) r. cball(x,r) SUBSET IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)`]
                P2BX_FINITE_BALL_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `open(IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c))` THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num` (X_CHOOSE_THEN `cs:num->real^3`
    (X_CHOOSE_THEN `rs:num->real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= J
        ==> ?C b k0. &0 <= C /\ &0 <= b /\
                  !k. k0 <= k
                      ==> IMAGE (chart_inv (c:(B->bool)#(B->real^3))) (cball((cs:num->real^3) j, rs j))
                            SUBSET W k /\
                          (!x t. x IN cball(cs j, rs j) /\ t1 <= t /\ t <= t2
                                 ==> &0 <= p2b_klx (top,atlas) (g:real->A->real^3^3) p (tau k * t)
                                                   ((phi:num->B->A) k (chart_inv c x)) /\
                                     p2b_klx (top,atlas) g p (tau k * t)
                                             (phi k (chart_inv c x)) <= C) /\
                          (!x x' t t'. x IN cball(cs j, rs j) /\ x' IN cball(cs j, rs j) /\
                                       t1 <= t /\ t <= t2 /\ t1 <= t' /\ t' <= t2
                                       ==> abs(p2b_klx (top,atlas) g p (tau k * t)
                                                       (phi k (chart_inv c x)) -
                                               p2b_klx (top,atlas) g p (tau k * t')
                                                       (phi k (chart_inv c x'))) <=
                                           b * (norm(x - x') + abs(t - t')))`
  (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                   `c:(B->bool)#(B->real^3)`; `cball((cs:num->real^3) j, rs j)`;
                   `t1:real`; `t2:real`] P2BX_G1_PIECE_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[COMPACT_CBALL; CONVEX_CBALL] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:num->real` (X_CHOOSE_THEN `b:num->real`
    (X_CHOOSE_THEN `k0:num->num` (LABEL_TAC "PB")))) THEN
  MP_TAC(ISPECL [`k0:num->num`; `1..J`] UPPER_BOUND_FINITE_SET) THEN
  MP_TAC(ISPECL [`C:num->real`; `1..J`] UPPER_BOUND_FINITE_SET_REAL) THEN
  MP_TAC(ISPECL [`b:num->real`; `1..J`] UPPER_BOUND_FINITE_SET_REAL) THEN
  MP_TAC(ISPECL [`\j. &2 / (rs:num->real) j`; `1..J`] UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_TAC `Ar:real`) THEN DISCH_THEN(X_CHOOSE_TAC `bm:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `Cm:real`) THEN DISCH_THEN(X_CHOOSE_TAC `K0:num`) THEN
  EXISTS_TAC `K0:num` THEN X_GEN_TAC `ix:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[p2bw_unilip] THEN X_GEN_TAC `kk:real^(3,1)finite_sum->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `&2 * abs bm + &2 * abs Cm / inv(abs Ar + &1)` THEN
  X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN `!z:real^(3,1)finite_sum. z IN kk ==> z IN closure om` ASSUME_TAC THENL
   [MP_TAC(ISPEC `om:real^(3,1)finite_sum->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. 1 <= j /\ j <= J ==> &0 < (rs:num->real) j` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2bg_sfun (top,atlas) (g:real->A->real^3^3) p tau (phi:num->B->A)
                    (c:(B->bool)#(B->real^3)) (ix:num->num) n`;
                 `closure om:real^(3,1)finite_sum->bool`; `J:num`; `cs:num->real^3`;
                 `rs:num->real`; `abs Cm`; `abs bm`; `inv(abs Ar + &1)`] P2BX_PIECES_LIP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_ABS_POS; REAL_LT_INV_EQ] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Ar:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < (rs:num->real) j` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SPEC_TAC(`(rs:num->real) j`,`r:real`) THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 / r)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_INV_DIV; REAL_LE_REFL]];
      X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
      SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                    UNIONS (IMAGE (\j. ball((cs:num->real^3) j, rs j / &2)) (1..J))` MP_TAC THENL
       [UNDISCH_TAC `IMAGE fstcart (closure om:real^(3,1)finite_sum->bool) SUBSET
                     UNIONS (IMAGE (\j. ball((cs:num->real^3) j, rs j / &2)) (1..J))` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_NUMSEG] THEN MESON_TAC[]];
      MAP_EVERY X_GEN_TAC [`j:num`; `z:real^(3,1)finite_sum`] THEN STRIP_TAC THEN
      USE_THEN "PB" (MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `(ix:num->num) n` o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `K0:num` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`fstcart(z:real^(3,1)finite_sum)`;
                                 `drop(sndcart(z:real^(3,1)finite_sum))`] o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[p2bg_sfun] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C:num->real) j` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`j:num`; `z:real^(3,1)finite_sum`; `w:real^(3,1)finite_sum`] THEN
      STRIP_TAC THEN
      USE_THEN "PB" (MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `(ix:num->num) n` o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `K0:num` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`fstcart(z:real^(3,1)finite_sum)`; `fstcart(w:real^(3,1)finite_sum)`;
                                 `drop(sndcart(z:real^(3,1)finite_sum))`;
                                 `drop(sndcart(w:real^(3,1)finite_sum))`] o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[p2bg_sfun] THEN
      MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS]]];
    ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`z:real^(3,1)finite_sum`; `w:real^(3,1)finite_sum`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^(3,1)finite_sum`; `w:real^(3,1)finite_sum`]) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The member scalar curvatures converge locally uniformly on a chart box to *)
(* the limit chart scalar curvature (cdata clause C):                        *)
(* LCK_CURVATURE_STABILITY at order 2 in the charts at the points of the     *)
(* limit, with a uniform bound of the curvature of the limit flow on compact *)
(* sets (RFA_RMD2_CONTINUOUS).                                               *)
(* ========================================================================= *)

(* A flow on (a,b) for every a < b is a flow from each a < b. *)

let P2BX_RF_ON_FROM = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) b (g:real->A->real^N^N) a.
     (!a. a < b ==> ricci_flow_on (top,atlas) a b g) /\ a < b
     ==> ricci_flow_from (top,atlas) a b g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ricci_flow_from] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a - &1`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ricci_flow_on]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`&1`; `\z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
                (metric_local atlas c ((g:real->A->real^N^N)(drop(fstcart z))) (sndcart z))`] THEN
  REWRITE_TAC[REAL_LT_01; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* A uniform bound of the curvature of the limit flow on compact sets of    *)
(* space and time.                                                           *)

let P2BX_RMD2_UNIF = prove
 (`!(top':B topology) atlas' (g':real->B->real^N^N) K t1 t2.
     (!a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g') /\
     compact_in top' K /\ &0 < t1 /\ t1 <= t2
     ==> ?B. !y t. y IN K /\ t1 <= t /\ t <= t2 ==> rfa_rmd2 0 atlas' (g'(&1 - t)) y <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `--t2`; `&1`;
                 `g':real->B->real^N^N`] RFA_RMD2_CONTINUOUS) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC P2BX_RF_ON_FROM THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[SUBTOPOLOGY_TOPSPACE]) THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology euclideanreal {t | --t2 <= t /\ t < &1}) (top':B topology)`;
    `euclideanreal`;
    `\z:real#B. rfa_rmd2 0 atlas' ((g':real->B->real^N^N) (FST z)) (SND z)`;
    `real_interval[&1 - t2,&1 - t1] CROSS (K:B->bool)`] IMAGE_COMPACT_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_CROSS; COMPACT_IN_SUBTOPOLOGY;
                    COMPACT_IN_EUCLIDEANREAL_INTERVAL] THEN
    REPEAT DISJ2_TAC THEN REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS; IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `t:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&1 - t`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Scalar curvature of the rescaled members along compact sets of the      *)
(* limit, uniformly in time (the scalar part of LIM_CURV_KEY, uniform).    *)

let P2BX_G1_SCAL = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi K t1 t2 alpha.
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     compact_in top' K /\ &0 < t1 /\ t1 <= t2 /\ &0 < alpha
     ==> ?k0. !k y t. k0 <= k /\ y IN K /\ t1 <= t /\ t <= t2
                      ==> abs(tau k * mfd_scalar atlas (g(--(tau k * t))) (phi k y) -
                              mfd_scalar atlas' (g'(&1 - t)) y) <= alpha`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `K:B->bool`; `t1:real`; `t2:real`] P2BX_RMD2_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  MP_TAC(ISPECL [`abs B + &1`; `alpha:real`] (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "STAB"))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t1:real`; `t2:real`; `K:B->bool`; `2`; `eta pow 2`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:B`; `t:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi:A->B`)
    (MP_TAC o SPECL [`t:real`; `y:B`]))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top' /\ y IN W(k:num)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IN_SUBSET_TOPSPACE o check (fun th ->
      concl th = `compact_in (top':B topology) K`)) THEN
    UNDISCH_TAC `(K:B->bool) SUBSET W(k:num)` THEN UNDISCH_TAC `(y:B) IN K` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `y:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3) (&1 - t))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `--t2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ricci_flow_on")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) (--(tau(k:num) * t)))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --x <= &0`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s = IMAGE (SND(chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B)))
                        (FST(chart_at atlas' y) INTER W(k:num))` THEN
  SUBGOAL_THEN `mfd_param top atlas (s:real^3->bool)
                  ((phi:num->B->A) k o chart_inv (chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC P2BX_PARAM_EMBED THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `IMAGE ((phi:num->B->A) k) (W k)`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) (--(tau(k:num) * t))`; `s:real^3->bool`;
                 `(phi:num->B->A) k o chart_inv (chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B))`]
                APX_RFS_PULLBACK_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `SND(chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B)) y IN s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `open(s:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^3->bool) SUBSET
                IMAGE (SND(chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B))) (FST(chart_at atlas' y))`
  ASSUME_TAC THENL [EXPAND_TAC "s" THEN SET_TAC[]; ALL_TAC] THEN
  USE_THEN "STAB" (MP_TAC o SPECL
   [`s:real^3->bool`;
    `metric_local atlas' (chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B))
                  ((g':real->B->real^3^3) (&1 - t))`;
    `\z. inv(tau(k:num)) %%
         rfs_pullback atlas ((phi:num->B->A) k o chart_inv (chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B)))
                      ((g:real->A->real^3^3) (--(tau k * t))) z`;
    `SND(chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B)) y`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B)))
                        (FST(chart_at atlas' y))` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `riemannian_metric atlas' ((g':real->B->real^3^3) (&1 - t))` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; ETA_AX];
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:B`; `t:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `B:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[rfa_rmd2] THEN
      MATCH_MP_TAC(REAL_ARITH `B <= (abs B + &1) pow 2 ==> x <= B ==> x <= (abs B + &1) pow 2`) THEN
      MATCH_MP_TAC(REAL_ARITH `abs B + &1 <= (abs B + &1) pow 2 ==> B <= (abs B + &1) pow 2`) THEN
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 * a <= a * a ==> a <= a * a`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`s:real^3->bool`;
                 `rfs_pullback atlas ((phi:num->B->A) k o
                                      chart_inv (chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B)))
                               ((g:real->A->real^3^3) (--(tau(k:num) * t)))`;
                 `inv(tau(k:num))`;
                 `SND(chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B)) y`] LSCALAR_SCALE) THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_INV_INV; real_div] THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) (--(tau(k:num) * t))`; `s:real^3->bool`;
                 `(phi:num->B->A) k o chart_inv (chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B))`;
                 `SND(chart_at (atlas':((B->bool)#(B->real^3))->bool) (y:B)) y`]
                APX_PULLBACK_SCALAR_GEN) THEN
  ASM_SIMP_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mfd_scalar] THEN REAL_ARITH_TAC);;

let P2BX_BOX_SCAL_CONV = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi c om (ix:num->num).
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     c IN atlas' /\ p2bg_cbox c om /\ (!N. ?n0. !n. n0 <= n ==> N <= ix n)
     ==> p2bw_locunif om (p2bg_sscal atlas g tau phi c ix) (p2bw_cscal atlas' c (&1) g')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bw_locunif] THEN
  MAP_EVERY X_GEN_TAC [`k:real^(3,1)finite_sum->bool`; `e:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bg_cbox]) THEN
  MP_TAC(ISPECL [`c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`;
                 `k:real^(3,1)finite_sum->bool`] P2BX_BOX_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                 `IMAGE fstcart (k:real^(3,1)finite_sum->bool)`] P2BX_BOX_MEMBERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `IMAGE (chart_inv (c:(B->bool)#(B->real^3))) (IMAGE fstcart (k:real^(3,1)finite_sum->bool))`;
                 `t1:real`; `t2:real`; `e / &2`] P2BX_G1_SCAL) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "SC")) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k0:num` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `ix:num->num`)) (concl th))) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^(3,1)finite_sum`] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bg_sscal; p2bw_cscal] THEN
  USE_THEN "SC" (MP_TAC o SPECL [`(ix:num->num) n`;
                                 `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum))`;
                                 `drop(sndcart(z:real^(3,1)finite_sum))`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ASM_REAL_ARITH_TAC]);;

