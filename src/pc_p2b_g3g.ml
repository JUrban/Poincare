(* ========================================================================= *)
(* Unit pc_p2b_g3g: G3, the weak equation, the limit argument.  For a        *)
(* nonnegative smooth test psi in a chart box: P1 at M F_R - Psi, linearity  *)
(* and P3 give M times the cut bound below W(psi); letting R go to infinity  *)
(* gives W(psi) >= 0, hence W(psi) = 0 with the subsolution inequality;      *)
(* then general tests and p2bg_weq.                                          *)
(* ========================================================================= *)

needs "src/pc_p2b_g3f.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* One step of the limit argument: for a nonnegative test psi in a chart     *)
(* box, M times the lower bound at F_R is at most the weak form of psi (P1   *)
(* at M F_R - Psi, linearity, P3).                                           *)
(* ========================================================================= *)

(* The cut-off, the moved test and their combination are locally Lipschitz *)
(* on every chart box.                                                       *)

let P2BX_TF_LOCLIP = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c om c0 psi kp (eta:real->real) R M.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     c IN atlas' /\ p2bg_cbox c om /\ &0 < R /\
     smooth_map_on (:real^1) (\s. lift(eta(drop s))) /\
     c0 IN atlas' /\ smooth_map_on (:real^(3,1)finite_sum) (\z. lift(psi z)) /\
     compact kp /\ IMAGE fstcart kp SUBSET IMAGE (SND c0) (FST c0) /\
     (!z. ~(z IN kp) ==> psi z = &0)
     ==> wan_loclip om (p2bw_cfun c (p2bx_fcut top' eta R linf)) /\
         wan_loclip om (p2bw_cfun c (p2bx_mfun c0 psi)) /\
         wan_loclip om (p2bw_cfun c (\t x. M * p2bx_fcut top' eta R linf t x - p2bx_mfun c0 psi t x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN `open(om:real^(3,1)finite_sum->bool) /\
                om SUBSET {z | fstcart z IN IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox (c:(B->bool)#(B->real^3)) om` THEN REWRITE_TAC[p2bg_cbox] THEN
    MP_TAC(ISPEC `om:real^(3,1)finite_sum->bool` CLOSURE_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`] P2BX_BOX_CSUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_loclip om (p2bw_cfun (c:(B->bool)#(B->real^3))
                  (p2bx_fcut top' eta R (linf:real->B->real)))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_FCUT_LOCLIP THEN
    EXISTS_TAC `atlas':((B->bool)#(B->real^3))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_loclip om (p2bw_cfun (c:(B->bool)#(B->real^3)) (p2bx_mfun c0 psi))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_MFUN_LOCLIP THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `kp:real^(3,1)finite_sum->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[P2BX_CFUN_LINCOMB] THEN
  MATCH_MP_TAC P2BX_LOCLIP_LINCOMB THEN ASM_REWRITE_TAC[ETA_AX]);;

let P2BX_BOX_STEP = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V K Wo a b k c om Ks rho
    c0 om0 psi kp eta deta M R.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ open_in top' Wo /\ Wo SUBSET K /\
     &0 < a /\ &0 < R /\ &0 < M /\
     c0 IN atlas' /\ p2bg_cbox c0 om0 /\
     smooth_map_on (:real^(3,1)finite_sum) (\z. lift(psi z)) /\
     (!z. &0 <= psi z /\ psi z <= M) /\
     compact kp /\ kp SUBSET om0 /\ (!z. ~(z IN kp) ==> psi z = &0) /\
     smooth_map_on (:real^1) (\s. lift(eta(drop s))) /\
     (!t. (eta has_real_derivative deta t) (atreal t)) /\ (!s. deta real_continuous atreal s) /\
     (!t. ~(eta t = &0) ==> a <= t /\ t <= b) /\ (!t. ~(deta t = &0) ==> a <= t /\ t <= b) /\
     (!t. &0 <= eta t) /\
     (!z. z IN kp ==> eta(drop(sndcart z)) = &1 /\ p2bw_cfun c0 linf z <= R /\
                      a <= drop(sndcart z) /\ drop(sndcart z) <= b) /\
     (!t x. x IN topspace top' /\ a <= t /\ t <= b /\ linf t x < &2 * R ==> x IN Wo)
     ==> M * (--drop(integral (interval[lift a,lift b])
                       (\y. lift(deta(drop y) * p2bx_islice (top',atlas') g' linf R (drop y)))) -
              &6 / a * (V * drop(integral (interval[lift a,lift b]) (\y. lift(eta(drop y)))) -
                        drop(integral (interval[lift a,lift b])
                          (\y. lift(eta(drop y) * p2bx_islice (top',atlas') g' linf (R / &2) (drop y)))))) <=
         drop(integral om0 (\z. lift(p2bx_wint atlas' g' c0 (p2bx_uf linf) psi z)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `!t x. x IN topspace top' /\ a <= t /\ t <= b /\ (linf:real->B->real) t x < &2 * R
                      ==> x IN K` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN `(x:B) IN Wo` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Wo:B->bool`)) (concl th))) THEN
      EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN `open(om0:real^(3,1)finite_sum->bool) /\
                om0 SUBSET {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox (c0:(B->bool)#(B->real^3)) om0` THEN REWRITE_TAC[p2bg_cbox] THEN
    MP_TAC(ISPEC `om0:real^(3,1)finite_sum->bool` CLOSURE_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE fstcart (kp:real^(3,1)finite_sum->bool) SUBSET
                IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(kp:real^(3,1)finite_sum->bool) SUBSET om0` THEN
    UNDISCH_TAC `(om0:real^(3,1)finite_sum->bool) SUBSET
                 {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c0:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `eta:real->real`; `R:real`; `linf:real->B->real`;
                 `a:real`; `b:real`] P2BX_FCUT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fsupp")) THEN
  (* the support of Psi *)
  SUBGOAL_THEN
   `!t x. ~(p2bx_mfun (c0:(B->bool)#(B->real^3)) psi t x = &0)
          ==> x IN FST c0 /\ pastecart (SND c0 x) (lift t) IN kp`
  (LABEL_TAC "msupp") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[p2bx_mfun] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. x IN FST(c0:(B->bool)#(B->real^3)) /\ pastecart (SND c0 x) (lift t) IN kp
          ==> x IN topspace top' /\ a <= t /\ t <= b /\ (linf:real->B->real) t x <= R /\
              eta t = &1 /\ x IN Wo`
  (LABEL_TAC "kpf") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:B) IN topspace top'` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (SND(c0:(B->bool)#(B->real^3)) x) (lift t)` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `eta:real->real`)) (concl th) &&
        can (find_term ((=) `kp:real^(3,1)finite_sum->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[p2bw_cfun; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Wo:B->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* local Lipschitz readings on the partition boxes *)
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> wan_loclip ((om:num->real^(3,1)finite_sum->bool) j)
              (p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (p2bx_fcut top' eta R (linf:real->B->real))) /\
            wan_loclip (om j) (p2bw_cfun (c j) (p2bx_mfun (c0:(B->bool)#(B->real^3)) psi)) /\
            wan_loclip (om j) (p2bw_cfun (c j)
              (\t x. M * p2bx_fcut top' eta R linf t x - p2bx_mfun c0 psi t x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c:num->(B->bool)#(B->real^3)) j IN atlas' /\ p2bg_cbox (c j) (om j)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `p2bx_pdata atlas' K a b k (c:num->(B->bool)#(B->real^3)) om Ks rho` THEN
      REWRITE_TAC[p2bx_pdata] THEN DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                   `(c:num->(B->bool)#(B->real^3)) j`; `(om:num->real^(3,1)finite_sum->bool) j`;
                   `c0:(B->bool)#(B->real^3)`; `psi:real^(3,1)finite_sum->real`;
                   `kp:real^(3,1)finite_sum->bool`; `eta:real->real`; `R:real`; `M:real`]
                  P2BX_TF_LOCLIP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* nonnegativity and support of M F_R - Psi *)
  SUBGOAL_THEN `!t x. &0 <= M * p2bx_fcut top' eta R (linf:real->B->real) t x -
                            p2bx_mfun (c0:(B->bool)#(B->real^3)) psi t x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    ASM_CASES_TAC `p2bx_mfun (c0:(B->bool)#(B->real^3)) psi t x = &0` THENL
     [ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    USE_THEN "msupp" (MP_TAC o SPECL [`t:real`; `x:B`]) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "kpf" (MP_TAC o SPECL [`t:real`; `x:B`]) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(linf:real->B->real) t x / R - &1 <= &0` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ARITH `u - &1 <= &0 <=> u <= &1`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID];
      ALL_TAC] THEN
    ASM_SIMP_TAC[p2bx_fcut; p2bx_hcut; p2bx_mfun; P2BX_CHI_BOUNDS; REAL_MUL_LID; REAL_MUL_RID] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (SND(c0:(B->bool)#(B->real^3)) x) (lift t)` o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `psi:real^(3,1)finite_sum->real`)) (concl th) &&
        can (find_term ((=) `M:real`)) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!t x. ~(p2bx_fcut top' eta R (linf:real->B->real) t x = &0) ==> a <= t /\ t <= b) /\
                (!t x. ~(p2bx_mfun (c0:(B->bool)#(B->real^3)) psi t x = &0) ==> a <= t /\ t <= b) /\
                (!t x. ~(M * p2bx_fcut top' eta R linf t x - p2bx_mfun c0 psi t x = &0)
                       ==> x IN Wo /\ a <= t /\ t <= b)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [DISCH_TAC THEN USE_THEN "fsupp" (MP_TAC o SPECL [`t:real`; `x:B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN USE_THEN "msupp" (MP_TAC o SPECL [`t:real`; `x:B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "kpf" (MP_TAC o SPECL [`t:real`; `x:B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[];
      ASM_CASES_TAC `p2bx_mfun (c0:(B->bool)#(B->real^3)) psi t x = &0` THENL
       [ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN
        USE_THEN "fsupp" (MP_TAC o SPECL [`t:real`; `x:B`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `Wo:B->bool`)) (concl th) &&
          not (can (find_term ((=) `kp:real^(3,1)finite_sum->bool`)) (concl th)))) THEN
        EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN USE_THEN "msupp" (MP_TAC o SPECL [`t:real`; `x:B`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        USE_THEN "kpf" (MP_TAC o SPECL [`t:real`; `x:B`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* P1 for M F_R - Psi *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`;
                 `\t x. M * p2bx_fcut top' eta R (linf:real->B->real) t x -
                        p2bx_mfun (c0:(B->bool)#(B->real^3)) psi t x`] P2BX_GFUN_NONPOS) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* linearity *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`;
                 `p2bx_fcut top' eta R (linf:real->B->real)`;
                 `p2bx_mfun (c0:(B->bool)#(B->real^3)) psi`; `M:real`] P2BX_GFUN_LINEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  (* P3 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`;
                 `c0:(B->bool)#(B->real^3)`; `om0:real^(3,1)finite_sum->bool`;
                 `psi:real^(3,1)finite_sum->real`; `kp:real^(3,1)finite_sum->bool`]
                P2BX_GFUN_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "kpf" (MP_TAC o SPECL [`drop(sndcart(z:real^(3,1)finite_sum))`;
       `chart_inv (c0:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum))`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LIFT_DROP; PASTECART_FST_SND];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  (* the lower bound at F_R *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`;
                 `eta:real->real`; `deta:real->real`; `R:real`] P2BX_CUT_SEQ_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ (MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < M`))) THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The lower bound for every radius: compact sublevel neighbourhoods of the  *)
(* cut region, a partition for each radius, and the integrability of the     *)
(* slice terms.                                                              *)
(* ========================================================================= *)

(* Arithmetic for the sublevel neighbourhood: tau^2 l is nondecreasing.     *)

let P2BX_SUBLEVEL_ARITH = prove
 (`!a b t l0 l1 R.
     &0 < a /\ a <= t /\ t <= b /\ &0 <= l1 /\ l1 < &2 * R /\ a pow 2 * l0 <= t pow 2 * l1
     ==> l0 < &2 * R * (b / a) pow 2 + &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t pow 2 * l1 <= b pow 2 * (&2 * R)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `l0 <= &2 * R * (b / a) pow 2` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV; real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* A compact neighbourhood of the region where some time slice of linf in   *)
(* [a,b] is below 2 R.                                                       *)

let P2BX_SUBLEVEL_EXISTS = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf a b R.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\ &0 < a
     ==> ?K Wo. compact_in top' K /\ open_in top' Wo /\ Wo SUBSET K /\
                (!t x. x IN topspace top' /\ a <= t /\ t <= b /\ linf t x < &2 * R ==> x IN Wo)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`; `a:real`; `&2 * R * (b / a) pow 2 + &1`] P2BX_LINF_SUBLEVEL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`{x | x IN topspace top' /\ (linf:real->B->real) a x <= &2 * R * (b / a) pow 2 + &1}`;
    `{x | x IN topspace top' /\ (linf:real->B->real) a x < &2 * R * (b / a) pow 2 + &1}`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`; `t:real`; `x:B`] P2BX_LINF_NONNEG) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`; `x:B`; `a:real`; `t:real`] P2BX_LINF_TMONO) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC P2BX_SUBLEVEL_ARITH THEN
  MAP_EVERY EXISTS_TAC [`t:real`; `(linf:real->B->real) t x`] THEN ASM_REWRITE_TAC[]);;

(* The lower bound at one radius R, with given neighbourhoods K, Wo.        *)

let P2BX_BOX_LB_N = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V K Wo c0 om0 psi kp eta deta a b M R.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\
     compact_in top' K /\ open_in top' Wo /\ Wo SUBSET K /\
     (!t x. x IN topspace top' /\ a <= t /\ t <= b /\ linf t x < &2 * R ==> x IN Wo) /\
     &0 < a /\ a <= b /\ &0 < M /\ &0 < R /\
     c0 IN atlas' /\ p2bg_cbox c0 om0 /\
     smooth_map_on (:real^(3,1)finite_sum) (\z. lift(psi z)) /\
     (!z. &0 <= psi z /\ psi z <= M) /\
     compact kp /\ kp SUBSET om0 /\ (!z. ~(z IN kp) ==> psi z = &0) /\
     smooth_map_on (:real^1) (\s. lift(eta(drop s))) /\
     (!t. (eta has_real_derivative deta t) (atreal t)) /\ (!s. deta real_continuous atreal s) /\
     (!t. ~(eta t = &0) ==> a <= t /\ t <= b) /\ (!t. ~(deta t = &0) ==> a <= t /\ t <= b) /\
     (!t. &0 <= eta t) /\
     (!z. z IN kp ==> eta(drop(sndcart z)) = &1 /\ p2bw_cfun c0 linf z <= R /\
                      a <= drop(sndcart z) /\ drop(sndcart z) <= b)
     ==> M * (--drop(integral (interval[lift a,lift b])
                       (\y. lift(deta(drop y) * p2bx_islice (top',atlas') g' linf R (drop y)))) -
              &6 / a * (V * drop(integral (interval[lift a,lift b]) (\y. lift(eta(drop y)))) -
                        drop(integral (interval[lift a,lift b])
                          (\y. lift(eta(drop y) * p2bx_islice (top',atlas') g' linf (R / &2) (drop y)))))) <=
         drop(integral om0 (\z. lift(p2bx_wint atlas' g' c0 (p2bx_uf linf) psi z))) /\
         (\y. lift(deta(drop y) * p2bx_islice (top',atlas') g' linf R (drop y)))
           integrable_on interval[lift a,lift b] /\
         (\y. lift(eta(drop y) * p2bx_islice (top',atlas') g' linf (R / &2) (drop y)))
           integrable_on interval[lift a,lift b]`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN `!s. (eta:real->real) real_continuous atreal s` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    EXISTS_TAC `(deta:real->real) s` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t x. x IN topspace top' /\ a <= t /\ t <= b /\ (linf:real->B->real) t x < &2 * R
                      ==> x IN K` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN `(x:B) IN Wo` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Wo:B->bool`)) (concl th))) THEN
      EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`] P2BX_PDATA_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `c:num->(B->bool)#(B->real^3)`
    (X_CHOOSE_THEN `om:num->real^(3,1)finite_sum->bool` (X_CHOOSE_THEN `Ks:num->real^3->bool`
      (X_CHOOSE_THEN `rho:num->B->real` ASSUME_TAC))))) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                   `V:real`; `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`; `k:num`;
                   `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                   `Ks:num->real^3->bool`; `rho:num->B->real`;
                   `c0:(B->bool)#(B->real^3)`; `om0:real^(3,1)finite_sum->bool`;
                   `psi:real^(3,1)finite_sum->real`; `kp:real^(3,1)finite_sum->bool`;
                   `eta:real->real`; `deta:real->real`; `M:real`; `R:real`] P2BX_BOX_STEP) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                   `V:real`; `K:B->bool`; `a:real`; `b:real`; `k:num`;
                   `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                   `Ks:num->real^3->bool`; `rho:num->B->real`;
                   `deta:real->real`; `R:real`; `R:real`] P2BX_EUH_SLICE) THEN
    ASM_REWRITE_TAC[p2bx_islice; REAL_LE_REFL];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                   `V:real`; `K:B->bool`; `a:real`; `b:real`; `k:num`;
                   `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                   `Ks:num->real^3->bool`; `rho:num->B->real`;
                   `eta:real->real`; `R / &2`; `R:real`] P2BX_EUH_SLICE) THEN
    ASM_REWRITE_TAC[p2bx_islice] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* The lower bound for every radius L + n.                                   *)

let P2BX_BOX_LB_ALL = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V c0 om0 psi kp eta deta a b M L.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\
     &0 < a /\ a <= b /\ &0 < M /\ &0 < L /\
     c0 IN atlas' /\ p2bg_cbox c0 om0 /\
     smooth_map_on (:real^(3,1)finite_sum) (\z. lift(psi z)) /\
     (!z. &0 <= psi z /\ psi z <= M) /\
     compact kp /\ kp SUBSET om0 /\ (!z. ~(z IN kp) ==> psi z = &0) /\
     smooth_map_on (:real^1) (\s. lift(eta(drop s))) /\
     (!t. (eta has_real_derivative deta t) (atreal t)) /\ (!s. deta real_continuous atreal s) /\
     (!t. ~(eta t = &0) ==> a <= t /\ t <= b) /\ (!t. ~(deta t = &0) ==> a <= t /\ t <= b) /\
     (!t. &0 <= eta t) /\
     (!z. z IN kp ==> eta(drop(sndcart z)) = &1 /\ p2bw_cfun c0 linf z <= L /\
                      a <= drop(sndcart z) /\ drop(sndcart z) <= b)
     ==> !n. M * (--drop(integral (interval[lift a,lift b])
                       (\y. lift(deta(drop y) * p2bx_islice (top',atlas') g' linf (L + &n) (drop y)))) -
              &6 / a * (V * drop(integral (interval[lift a,lift b]) (\y. lift(eta(drop y)))) -
                        drop(integral (interval[lift a,lift b])
                          (\y. lift(eta(drop y) * p2bx_islice (top',atlas') g' linf ((L + &n) / &2) (drop y)))))) <=
         drop(integral om0 (\z. lift(p2bx_wint atlas' g' c0 (p2bx_uf linf) psi z))) /\
         (\y. lift(deta(drop y) * p2bx_islice (top',atlas') g' linf (L + &n) (drop y)))
           integrable_on interval[lift a,lift b] /\
         (\y. lift(eta(drop y) * p2bx_islice (top',atlas') g' linf ((L + &n) / &2) (drop y)))
           integrable_on interval[lift a,lift b]`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN `&0 < L + &n` ASSUME_TAC THENL
   [MP_TAC(SPEC `n:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN kp ==> eta(drop(sndcart z)) = &1 /\
                               p2bw_cfun (c0:(B->bool)#(B->real^3)) (linf:real->B->real) z <= L + &n /\
                               a <= drop(sndcart z) /\ drop(sndcart z) <= b`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(3,1)finite_sum` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `L:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`; `a:real`; `b:real`; `L + &n`] P2BX_SUBLEVEL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:B->bool` (X_CHOOSE_THEN `Wo:B->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `K:B->bool`; `Wo:B->bool`;
                 `c0:(B->bool)#(B->real^3)`; `om0:real^(3,1)finite_sum->bool`;
                 `psi:real^(3,1)finite_sum->real`; `kp:real^(3,1)finite_sum->bool`;
                 `eta:real->real`; `deta:real->real`; `a:real`; `b:real`; `M:real`; `L + &n`]
                P2BX_BOX_LB_N) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The weak equation for nonnegative tests: W(psi) <= 0 by the subsolution   *)
(* property, W(psi) >= M B(L + n) for every n, and B(L + n) -> 0.            *)
(* ========================================================================= *)

let P2BX_KP_TIMES = prove
 (`!kp:real^(3,1)finite_sum->bool.
     compact kp /\ ~(kp = {}) /\ (!z. z IN kp ==> &0 < drop(sndcart z))
     ==> ?t1 t2. &0 < t1 /\ t1 <= t2 /\
                 !z. z IN kp ==> t1 <= drop(sndcart z) /\ drop(sndcart z) <= t2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(IMAGE lift (IMAGE (\z:real^(3,1)finite_sum. drop(sndcart z)) kp))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (\z:real^(3,1)finite_sum. drop(sndcart z)) kp = {})` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\z:real^(3,1)finite_sum. drop(sndcart z)) kp` COMPACT_ATTAINS_INF) THEN
  MP_TAC(ISPEC `IMAGE (\z:real^(3,1)finite_sum. drop(sndcart z)) kp` COMPACT_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z2:real^(3,1)finite_sum` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:real^(3,1)finite_sum` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`drop(sndcart(z1:real^(3,1)finite_sum))`;
                        `drop(sndcart(z2:real^(3,1)finite_sum))`] THEN
  ASM_SIMP_TAC[]);;

let P2BX_CONT_UBOUND = prove
 (`!(k:real^M->bool) (f:real^M->real).
     compact k /\ (\z. lift(f z)) continuous_on k ==> ?B. &0 < B /\ !z. z IN k ==> f z <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\z. lift((f:real^M->real) z)) k` COMPACT_IMP_BOUNDED) THEN
  ANTS_TAC THENL [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2BX_BOX_WEQ_NONNEG = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V c0 om0 psi.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\
     c0 IN atlas' /\ p2bg_cbox c0 om0 /\ wan_test om0 psi /\ (!z. &0 <= psi z)
     ==> drop(integral om0 (\z. lift(p2bx_wint atlas' g' c0 (p2bx_uf linf) psi z))) = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_test")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `kp:real^(3,1)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `open(om0:real^(3,1)finite_sum->bool) /\
                om0 SUBSET {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0) /\
                                &0 < drop(sndcart z)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox (c0:(B->bool)#(B->real^3)) om0` THEN REWRITE_TAC[p2bg_cbox] THEN
    MP_TAC(ISPEC `om0:real^(3,1)finite_sum->bool` CLOSURE_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_loclip om0 (psi:real^(3,1)finite_sum->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LOCLIP_SUBSET THEN EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P2BX_SMOOTH_LOCLIP THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  (* the subsolution inequality *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `c0:(B->bool)#(B->real^3)`; `om0:real^(3,1)finite_sum->bool`;
                 `psi:real^(3,1)finite_sum->real`] P2BX_BOX_WSUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[p2bw_ltest] THEN EXISTS_TAC `kp:real^(3,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &0 /\ &0 <= x ==> x = &0`) THEN ASM_REWRITE_TAC[] THEN
  (* empty support *)
  ASM_CASES_TAC `kp:real^(3,1)finite_sum->bool = {}` THENL
   [SUBGOAL_THEN `!z. p2bx_wint atlas' (g':real->B->real^3^3) (c0:(B->bool)#(B->real^3))
                        (p2bx_uf (linf:real->B->real)) psi z = &0`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC P2BX_WINT_ZERO THEN EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ASM_MESON_TAC[NOT_IN_EMPTY];
      REWRITE_TAC[LIFT_NUM; INTEGRAL_0; DROP_VEC; REAL_LE_REFL]];
    ALL_TAC] THEN
  (* the times of the support and the time cutoff *)
  MP_TAC(ISPEC `kp:real^(3,1)finite_sum->bool` P2BX_KP_TIMES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t1 / &2`; `t2 + &1`; `t1:real`; `t2:real`] P2BX_ETA_EXISTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real->real` (X_CHOOSE_THEN `deta:real->real` STRIP_ASSUME_TAC)) THEN
  (* bounds of psi and of linf on the support *)
  MP_TAC(ISPECL [`kp:real^(3,1)finite_sum->bool`; `psi:real^(3,1)finite_sum->real`]
                P2BX_CONT_UBOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^(3,1)finite_sum)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `c0:(B->bool)#(B->real^3)`; `om0:real^(3,1)finite_sum->bool`] P2BX_BOX_CSUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`kp:real^(3,1)finite_sum->bool`;
                 `p2bw_cfun (c0:(B->bool)#(B->real^3)) (linf:real->B->real)`] P2BX_CONT_UBOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `om0:real^(3,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX];
    DISCH_THEN(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `!z. &0 <= psi z /\ (psi:real^(3,1)finite_sum->real) z <= M` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(z:real^(3,1)finite_sum) IN kp` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN kp ==> eta(drop(sndcart z)) = &1 /\
                               p2bw_cfun (c0:(B->bool)#(B->real^3)) (linf:real->B->real) z <= L /\
                               t1 / &2 <= drop(sndcart z) /\ drop(sndcart z) <= t2 + &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `t1 <= drop(sndcart(z:real^(3,1)finite_sum)) /\ drop(sndcart z) <= t2`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t1 / &2 /\ t1 / &2 <= t2 + &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= (eta:real->real) t` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* the lower bound for every n *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `c0:(B->bool)#(B->real^3)`; `om0:real^(3,1)finite_sum->bool`;
                 `psi:real^(3,1)finite_sum->real`; `kp:real^(3,1)finite_sum->bool`;
                 `eta:real->real`; `deta:real->real`; `t1 / &2`; `t2 + &1`; `M:real`; `L:real`]
                P2BX_BOX_LB_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "lbn")] THEN
  (* the limit of the bounds *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `t1 / &2`; `t2 + &1`; `eta:real->real`; `deta:real->real`; `L:real`]
                P2BX_CUT_SEQ_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `n:num` THEN
    USE_THEN "lbn" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o BETA_RULE o SPEC `M:real` o MATCH_MP REALLIM_LMUL) THEN
  REWRITE_TAC[REAL_MUL_RZERO] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] REALLIM_UBOUND)) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  USE_THEN "lbn" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The weak equation for every test in a chart box: psi = (psi + M kappa)    *)
(* - M kappa with a smooth Urysohn bump kappa = 1 on the support of psi.     *)
(* ========================================================================= *)

let P2BX_LTEST_OF_TEST = prove
 (`!(om:real^(N,1)finite_sum->bool) psi.
     open om /\ wan_test om psi /\ (!z. &0 <= psi z) ==> p2bw_ltest om psi`,
  REWRITE_TAC[wan_test; p2bw_ltest] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_LOCLIP_SUBSET THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P2BX_SMOOTH_LOCLIP THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[]]);;

let P2BX_BOX_WEQ_TEST = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V c0 om0 psi.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\
     c0 IN atlas' /\ p2bg_cbox c0 om0 /\ wan_test om0 psi
     ==> drop(integral om0 (\z. lift(p2bx_wint atlas' g' c0 (p2bx_uf linf) psi z))) = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `open(om0:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox (c0:(B->bool)#(B->real^3)) om0` THEN SIMP_TAC[p2bg_cbox]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_test")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `kp:real^(3,1)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`om0:real^(3,1)finite_sum->bool`; `kp:real^(3,1)finite_sum->bool`]
                WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:real^(3,1)finite_sum->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`kp:real^(3,1)finite_sum->bool`; `\z. --((psi:real^(3,1)finite_sum->real) z)`]
                P2BX_CONT_UBOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_NEG] THEN MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test] o check (fun th ->
    can (find_term ((=) `kap:real^(3,1)finite_sum->real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_test")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `kk:real^(3,1)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
  (* the two nonnegative tests *)
  SUBGOAL_THEN `smooth_map_on (:real^(3,1)finite_sum)
                  (\z. lift((psi:real^(3,1)finite_sum->real) z + M * kap z)) /\
                smooth_map_on (:real^(3,1)finite_sum)
                  (\z. lift(M * (kap:real^(3,1)finite_sum->real) z))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CMUL_OPEN; OPEN_UNIV];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_test om0 (\z. (psi:real^(3,1)finite_sum->real) z + M * kap z) /\
                wan_test om0 (\z. M * (kap:real^(3,1)finite_sum->real) z) /\
                (!z. &0 <= (psi:real^(3,1)finite_sum->real) z + M * kap z) /\
                (!z. &0 <= M * (kap:real^(3,1)finite_sum->real) z)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_test] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `(kp:real^(3,1)finite_sum->bool) UNION kk` THEN
      ASM_SIMP_TAC[COMPACT_UNION; UNION_SUBSET; IN_UNION; DE_MORGAN_THM] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_LID];
      EXISTS_TAC `kk:real^(3,1)finite_sum->bool` THEN ASM_SIMP_TAC[REAL_MUL_RZERO];
      X_GEN_TAC `z:real^(3,1)finite_sum` THEN
      ASM_CASES_TAC `(z:real^(3,1)finite_sum) IN kp` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(3,1)finite_sum` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `M:real`)) (concl th))) THEN
        ASM_SIMP_TAC[REAL_MUL_RID] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_ADD_LID] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  (* both have weak form zero *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `c0:(B->bool)#(B->real^3)`; `om0:real^(3,1)finite_sum->bool`;
                 `\z. (psi:real^(3,1)finite_sum->real) z + M * kap z`] P2BX_BOX_WEQ_NONNEG) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `c0:(B->bool)#(B->real^3)`; `om0:real^(3,1)finite_sum->bool`;
                 `\z. M * (kap:real^(3,1)finite_sum->real) z`] P2BX_BOX_WEQ_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  (* linearity of the integrand *)
  SUBGOAL_THEN
   `(\z. lift(p2bx_wint atlas' g' (c0:(B->bool)#(B->real^3)) (p2bx_uf (linf:real->B->real)) psi z)) =
    (\z. lift(p2bx_wint atlas' g' c0 (p2bx_uf linf) (\z. psi z + M * kap z) z) -
         lift(p2bx_wint atlas' g' c0 (p2bx_uf linf) (\z. M * kap z) z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_SUB; LIFT_EQ] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN
    MP_TAC(ISPECL [`atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                   `c0:(B->bool)#(B->real^3)`; `p2bx_uf (linf:real->B->real)`;
                   `\z. (psi:real^(3,1)finite_sum->real) z + M * kap z`;
                   `\z. M * (kap:real^(3,1)finite_sum->real) z`; `&1`;
                   `z:real^(3,1)finite_sum`] P2BX_WINT_LINEAR) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^(3,1)finite_sum)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. lift(p2bx_wint atlas' g' (c0:(B->bool)#(B->real^3)) (p2bx_uf (linf:real->B->real))
                 (\z. (psi:real^(3,1)finite_sum->real) z + M * kap z) z)`;
    `\z. lift(p2bx_wint atlas' g' (c0:(B->bool)#(B->real^3)) (p2bx_uf (linf:real->B->real))
                 (\z. M * (kap:real^(3,1)finite_sum->real) z) z)`;
    `om0:real^(3,1)finite_sum->bool`] INTEGRAL_SUB) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC P2BX_WINT_ABSINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                          `sub:num->num`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX_LTEST_OF_TEST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[DROP_SUB; REAL_SUB_REFL]);;

(* ========================================================================= *)
(* The weak equation p2bg_weq on every chart box (the integrand of p2bg_weq  *)
(* is p2bx_wint pointwise).                                                  *)
(* ========================================================================= *)

let P2BX_WEQ_OF_WINT = prove
 (`!atlas' g' (c:(B->bool)#(B->real^3)) om (linf:real->B->real).
     (!psi. wan_test om psi
            ==> drop(integral om (\z. lift(p2bx_wint atlas' g' c (p2bx_uf linf) psi z))) = &0)
     ==> p2bg_weq atlas' g' c om linf`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bg_weq] THEN
  X_GEN_TAC `psi:real^(3,1)finite_sum->real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `psi:real^(3,1)finite_sum->real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
  MATCH_MP_TAC(MESON[] `(x:real^1) = y ==> drop y = &0 ==> drop x = &0`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; LIFT_EQ] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN
  REWRITE_TAC[p2bx_wint; p2bw_bil; P2BX_UOF_UF; MATRIX_CMUL_COMPONENT; GSYM REAL_MUL_ASSOC;
              SUM_LMUL] THEN
  REAL_ARITH_TAC);;

let P2BX_BOX_WEQ = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V c om.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\
     c IN atlas' /\ p2bg_cbox c om
     ==> p2bg_weq atlas' g' c om linf`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_WEQ_OF_WINT THEN
  X_GEN_TAC `psi:real^(3,1)finite_sum->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`;
                 `psi:real^(3,1)finite_sum->real`] P2BX_BOX_WEQ_TEST) THEN
  ASM_REWRITE_TAC[]);;

