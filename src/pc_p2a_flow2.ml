(* ========================================================================= *)
(* pc_p2a_flow2: the flow level of the Part 2A L-geometry, second file, at   *)
(* N = 3: FL3 P2A_FLOW_LX_CONT (MT Prop 7.5(1), from the wan_loclip clause   *)
(* of W3) and FL4 P2A_FLOW_THM_7_10 (MT Thm 7.10, from C3 FIX, which follows *)
(* from P2A_COR_7_12_FIX_FROM_BARRIER and P2A_BARRIER_FIX).  The theorems    *)
(* here are implications from the statement constants FL2 and W3;            *)
(* pc_p2a_flfin and pc_p2a_flw3 discharge these.                             *)
(* ========================================================================= *)

needs "src/pc_p2a_flow.ml";;
needs "src/pc_p2b_w3iface.ml";;
needs "src/pc_p2a_bar.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* FL3 (MT Prop 7.5(1), Cor 7.6: lx continuous on M x (0, b - a)) from the   *)
(* first clause of W3 (P2B_REQ_P2A_WEAK_STATEMENT: lx is locally Lipschitz   *)
(* in every chart's space-time domain): a compact box around (chart point,   *)
(* tau0) and the chart homeomorphism.                                        *)
(* ------------------------------------------------------------------------- *)

(* Preimages of open sets under a chart are open.                            *)

let P2AU_CHART_PREIMAGE_OPEN = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) O.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ open O
     ==> open_in top {q | q IN FST c /\ SND c q IN O}`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `U:A->bool`; `phi:A->real^N`; `O:real^N->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (phi:A->real^N) U INTER O` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] OPEN_IN_CONTINUOUS_MAP_PREIMAGE)) THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; TOPSPACE_SUBTOPOLOGY; IN_INTER; FST; SND] THEN
  X_GEN_TAC `q:A` THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` MP_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[]);;

(* FL3 from W3.                                                              *)

let P2AU_FLOW_LX_CONT = prove
 (`!(u:A->bool) (n:3->bool).
     P2B_REQ_P2A_WEAK_STATEMENT u ==> P2A_FLOW_LX_CONT_STATEMENT u n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_REQ_P2A_WEAK_STATEMENT; P2A_FLOW_LX_CONT_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "W3") THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`; `tau0:real`; `q0:A`; `e:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `q0:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "W3" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`;
                                `chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)`]) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `p2a_cbflow (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[P2AF_CBFLOW_3] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[wan_loclip] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "INV") (K ALL_TAC)))) THEN
  ABBREV_TAC `x0 = SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)) q0` THEN
  SUBGOAL_THEN `(x0:real^3) IN IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)))
                                     (FST(chart_at atlas q0))` ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?r. &0 < r /\
        cball(x0:real^3,r) SUBSET
          IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)))
                (FST(chart_at atlas q0)) /\
        &0 < tau0 - r /\ tau0 + r < b - a`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)))
                             (FST(chart_at atlas q0)))` THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `x0:real^3`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min r1 (min (tau0 / &2) ((b - a - tau0) / &2))` THEN
    REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^3,r1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cball(x0:real^3,r) PCROSS
                               interval[lift(tau0 - r),lift(tau0 + r)]` o check (fun th ->
    is_forall(concl th) && p2au_mentions "compact" th)) THEN
  ANTS_TAC THENL
   [SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; COMPACT_INTERVAL] THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; p2bw_cdom; IN_ELIM_THM;
                FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real^1`] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  ABBREV_TAC `L' = abs L + &1` THEN
  SUBGOAL_THEN `&0 < L'` ASSUME_TAC THENL [EXPAND_TAC "L'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = min r (e / (&4 * L'))` THEN
  SUBGOAL_THEN `&0 < &4 * L'` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < L'` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d /\ d <= r /\ d <= e / (&4 * L')` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * L' * d <= e` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&4 * L') * d <= (&4 * L') * (e / (&4 * L'))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN
  EXISTS_TAC `{q | q IN FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)) /\
                   SND(chart_at atlas q0) q IN ball(x0:real^3,d)}` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2AU_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[OPEN_BALL];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`tau:real`; `q:A`] THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`pastecart (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)) (q:A)) (lift tau)`;
    `pastecart (x0:real^3) (lift tau0)`]) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; p2bw_cfun;
              FSTCART_PASTECART; SNDCART_PASTECART; CENTRE_IN_CBALL] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN
    UNDISCH_TAC `SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)) (q:A) IN
                 ball(x0,d)` THEN
    REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A))
                  (SND(chart_at atlas q0) (q:A)) = q /\
                chart_inv (chart_at atlas q0) x0 = q0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN TRY(EXPAND_TAC "x0") THEN USE_THEN "INV" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM P2A_FLOW_VIEW_3] THEN
  MATCH_MP_TAC(REAL_ARITH `!x y. y < e ==> x <= y ==> x < e`) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `L' * (&2 * d)` THEN CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `&4 * L' * d <= e` THEN
    SUBGOAL_THEN `&0 < L' * d` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; REAL_ARITH_TAC]] THEN
  SUBGOAL_THEN
   `norm(pastecart (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)) (q:A)) (lift tau) -
         pastecart (x0:real^3) (lift tau0)) <= &2 * d`
  ASSUME_TAC THENL
   [REWRITE_TAC[PASTECART_SUB] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)) (q:A) - x0) +
                norm(lift tau - lift tau0)` THEN
    REWRITE_TAC[NORM_PASTECART_LE] THEN
    UNDISCH_TAC `SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)) (q:A) IN
                 ball(x0,d)` THEN
    REWRITE_TAC[IN_BALL; GSYM LIFT_SUB; NORM_LIFT; dist] THEN
    MP_TAC(ISPECL [`x0:real^3`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A)) (q:A)`]
                  NORM_SUB) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `L' * norm(pastecart (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (q0:A))
                                    (q:A)) (lift tau) - pastecart (x0:real^3) (lift tau0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN EXPAND_TAC "L'" THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* ------------------------------------------------------------------------- *)
(* FL4 (MT Thm 7.10 with Claim 7.11) from C3 FIX                            *)
(* (P2A_COR_7_12_FIX_FROM_BARRIER, pc_p2a_c712, with P2A_BARRIER_FIX,       *)
(* pc_p2a_bar), FL0, FL2 and FL3: slices U t = M for t in [b - tau, b);     *)
(* lx is proper (P2AU_ADM_PDIST) and continuous (FL3), so its slice minima  *)
(* are attained and the slice minimum is lower semicontinuous (uniform      *)
(* continuity on compact sets).                                             *)
(* ------------------------------------------------------------------------- *)

(* Under FL2, lx is attained by a minimizer and controls the distance.      *)

let P2AU_LX_PROPER = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p.
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top
     ==> ?D0 D1. &0 <= D0 /\ &0 <= D1 /\
           !tau q. &0 < tau /\ tau < b - a /\ q IN topspace top
                   ==> (?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                        b p tau gamma /\ gamma tau = q /\
                                p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                             b gamma tau =
                                &2 * sqrt tau *
                                p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                       b p tau q) /\
                       mfd_joinable (top,atlas) p q /\
                       mfd_dist (top,atlas) (g b) p q <=
                       D0 * (&2 * sqrt tau *
                             p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                    b p tau q + D1) + &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2A_FLOW_MIN_EXISTS_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL2") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D1:real` STRIP_ASSUME_TAC) o
              MATCH_MP P2AU_ADM_PDIST) THEN
  MAP_EVERY EXISTS_TAC [`D0:real`; `D1:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`tau:real`; `q:A`] THEN STRIP_TAC THEN
  USE_THEN "FL2" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                 `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `q:A`;
                                 `tau:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                 b gamma tau =
    &2 * sqrt tau * p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau q`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2a_lx] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP P2A_MIN_LX o REWRITE_RULE[P2A_FLOW_VIEW_3]) THEN
    ASM_REWRITE_TAC[P2A_FLOW_VIEW_3] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `&0 < sqrt tau` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  CONJ_TAC THENL [EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:A`; `tau:real`; `gamma:real->A`; `tau:real`] o
    check (fun th -> can (find_term (fun t -> t = `D0:real`)) (concl th) &&
                     is_forall(concl th))) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[p2a_min; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* A positive lower bound for finitely many positive numbers.                *)

let P2AU_FINITE_POS_MIN = prove
 (`!(Fs:A->bool) (dd:A->real).
     FINITE Fs /\ (!x. x IN Fs ==> &0 < dd x) ==> ?d. &0 < d /\ !x. x IN Fs ==> d <= dd x`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN SPEC_TAC(`Fs:A->bool`,`Fs:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `Fs:A->bool`] THEN REWRITE_TAC[IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d ((dd:A->real) y)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_MESON_TAC[REAL_LE_REFL]);;

(* Uniform continuity in the first variable over a compact set.             *)

let P2AU_UNIF_CONT_COMPACT = prove
 (`!(f:real->A->real) top C tau0 e.
     compact_in top C /\ &0 < e /\
     (!q0. q0 IN C
           ==> ?d O. &0 < d /\ open_in top O /\ q0 IN O /\
                     !tau q. abs(tau - tau0) < d /\ q IN O
                             ==> abs(f tau q - f tau0 q0) < e / &2)
     ==> ?d. &0 < d /\
             !tau q. abs(tau - tau0) < d /\ q IN C ==> abs(f tau q - f tau0 q) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:A->real` (X_CHOOSE_TAC `OO:A->A->bool`)) THEN
  REWRITE_TAC[compact_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `IMAGE (OO:A->A->bool) C`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `VV:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`OO:A->A->bool`; `C:A->bool`; `VV:(A->bool)->bool`]
                FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Fs:A->bool`; `dd:A->real`] P2AU_FINITE_POS_MIN) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`tau:real`; `q:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?q0:A. q0 IN Fs /\ (q:A) IN (OO:A->A->bool) q0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(C:A->bool) SUBSET UNIONS VV` THEN
    ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q0:A) IN C` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q0:A` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `OO:A->A->bool`)) (concl th) &&
    can (find_term (fun t -> t = `dd:A->real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E")))) THEN
  SUBGOAL_THEN `d <= (dd:A->real) q0` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((f:real->A->real) tau q - f tau0 q0) < e / &2` MP_TAC THENL
   [USE_THEN "E" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((f:real->A->real) tau0 q - f tau0 q0) < e / &2` MP_TAC THENL
   [USE_THEN "E" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* FL4 assembly.                                                             *)
(* ------------------------------------------------------------------------- *)

(* Pointwise epsilon-neighbourhood continuity into the reals.                *)

let P2AU_CONT_MAP_REAL = prove
 (`!top (f:A->real).
     (!q0 e. q0 IN topspace top /\ &0 < e
             ==> ?O. open_in top O /\ q0 IN O /\ !q. q IN O ==> abs(f q - f q0) < e)
     ==> continuous_map (top,euclideanreal) f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC; CONTINUOUS_MAP_TO_METRIC;
              MBALL_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `q0:A` THEN DISCH_TAC THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`q0:A`; `r:real`]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Under FL2 and FL3 the slice minima of lx are attained.                    *)

let P2AU_LX_SLICE_MIN = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p tau.
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\ P2A_FLOW_LX_CONT_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < tau /\ tau < b - a
     ==> ?qm. qm IN topspace top /\
              !q. q IN topspace top
                  ==> p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau qm <=
                      p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "FL3") STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`] P2AU_LX_PROPER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D1:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `f = p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                    (g:real->A->real^3^3)) b p tau` THEN
  ABBREV_TAC `R = D0 * (&2 * sqrt tau * (f:A->real) p + D1) + &1` THEN
  ABBREV_TAC `Kb = mfd_cball (top,atlas) ((g:real->A->real^3^3) b) p R` THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) b) /\
                mfd_complete (top,atlas) (g b)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (Kb:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kb" THEN UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->A->real^3^3) b)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN Kb` ASSUME_TAC THENL
   [EXPAND_TAC "Kb" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`tau:real`; `p:A`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `D0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "R" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (top,euclideanreal) (f:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_CONT_MAP_REAL THEN
    MAP_EVERY X_GEN_TAC [`q0:A`; `e:real`] THEN STRIP_TAC THEN
    USE_THEN "FL3" (MP_TAC o REWRITE_RULE[P2A_FLOW_LX_CONT_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `tau:real`;
                              `q0:A`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `O:A->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `O:A->bool` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `?qm. qm IN Kb /\ !y. y IN Kb ==> (f:A->real) qm <= f y`
  (X_CHOOSE_THEN `qm:A` STRIP_ASSUME_TAC) THENL
   [MP_TAC(ISPEC `IMAGE (f:A->real) Kb` REAL_COMPACT_ATTAINS_INF) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM SET_TAC[]];
      REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Kb:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  EXISTS_TAC `qm:A` THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(q:A) IN Kb` THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:A->real) p` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((q:A) IN Kb)` THEN REWRITE_TAC[] THEN
  EXPAND_TAC "Kb" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tau:real`; `q:A`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `D0:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `D0 * (&2 * sqrt tau * (f:A->real) q + D1) + &1` THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "R" THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + &1 <= y + &1`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + D1 <= y + D1`) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The time semicontinuity of the slice minimum needed by C3 (its last      *)
(* hypothesis).  Near tau0 every value lx(tau',y') is matched up to e by a  *)
(* value at tau0: at y' itself when lx(tau',y') <= m + e (y' then lies      *)
(* in a fixed closed ball, compact, where lx is uniformly continuous in     *)
(* time by FL3), and at the slice minimizer (value m) otherwise.            *)
(* ------------------------------------------------------------------------- *)

let P2AU_LX_SEMICONT = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p tau0 e.
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\ P2A_FLOW_LX_CONT_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < tau0 /\ tau0 < b - a /\ &0 < e
     ==> ?d. &0 < d /\
             !tau' y'. &0 < tau' /\ tau' < b - a /\ abs(tau' - tau0) < d /\
                       y' IN topspace top
                       ==> ?y. y IN topspace top /\
                               p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                      b p tau0 y <=
                               p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                      b p tau' y' + e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "FL3") STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau0:real`] P2AU_LX_SLICE_MIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `qm:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`] P2AU_LX_PROPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PR"))))) THEN
  ABBREV_TAC `lxf = p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                      (g:real->A->real^3^3)) b p` THEN
  ABBREV_TAC `m = (lxf:real->A->real) tau0 qm` THEN
  ABBREV_TAC `M = abs(m + e)` THEN
  SUBGOAL_THEN `m + e <= M /\ &0 <= M` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `R' = D0 * (&2 * sqrt(b - a) * M + D1) + &1` THEN
  ABBREV_TAC `Cb = mfd_cball (top,atlas) ((g:real->A->real^3^3) b) p R'` THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) b) /\
                mfd_complete (top,atlas) (g b)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (Cb:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Cb" THEN UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->A->real^3^3) b)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Cb:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lxf:real->A->real`; `top:A topology`; `Cb:A->bool`; `tau0:real`; `e:real`]
                P2AU_UNIF_CONT_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `q0:A` THEN DISCH_TAC THEN
    USE_THEN "FL3" (MP_TAC o REWRITE_RULE[P2A_FLOW_LX_CONT_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `tau0:real`;
                              `q0:A`; `e / &2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UC"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`tau':real`; `y':A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(lxf:real->A->real) tau' y' <= m + e` THENL
   [ALL_TAC; EXISTS_TAC `qm:A` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  EXISTS_TAC `y':A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y':A) IN Cb` ASSUME_TAC THENL
   [EXPAND_TAC "Cb" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
    USE_THEN "PR" (MP_TAC o SPECL [`tau':real`; `y':A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `D0 * (&2 * sqrt tau' * (lxf:real->A->real) tau' y' + D1) + &1` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "R'" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + &1 <= y + &1`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= sqrt tau' /\ sqrt tau' <= sqrt(b - a)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LE; MATCH_MP_TAC SQRT_MONO_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt tau' * (lxf:real->A->real) tau' y' <= sqrt tau' * M` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt tau' * M <= sqrt(b - a) * M` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "UC" (MP_TAC o SPECL [`tau':real`; `y':A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* FL4 (MT Thm 7.10) from C3 FIX (P2A_COR_7_12_VIEW_FIX, MT Cor 7.12        *)
(* corrected), FL2 and FL3.  C3 is applied to the flow view with the slab U *)
(* t = M for b - tau <= t < b (empty otherwise), the ball of radius         *)
(* 1 at b and dt = tau; its hypotheses are FL0 (regions), the slice         *)
(* minima (P2AU_LX_SLICE_MIN) and P2AU_LX_SEMICONT.  The slice minimum at   *)
(* tau is then at most 3/2 = n/2.                                           *)
(* ------------------------------------------------------------------------- *)

(* The slab is a space-time open set of the flow view.                      *)

let P2AU_ST_OPEN_SLAB = prove
 (`!top atlas a b (g:real->A->real^N^N) a'.
     smooth_manifold_atlas top atlas /\ a < a' /\ a' < b
     ==> p2a_st_open (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                     (\t. if a' <= t /\ t < b then topspace top else {}) a' b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_st_open] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  ABBREV_TAC `eta = min (b - t) (t - a) / &2` THEN
  SUBGOAL_THEN `&0 < eta /\ &2 * eta <= b - t /\ &2 * eta <= t - a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`topspace top:A->bool`; `eta:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[P2A_PERSISTS_ALT; P2AU_FLOW_VIEW_PARTS; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `a <= s /\ s <= b` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* FL4 from C3, FL2 and FL3.                                                 *)

let P2AU_FLOW_THM_7_10_C3 = prove
 (`!(u:A->bool) (n:3->bool).
     P2A_COR_7_12_VIEW_FIX_STATEMENT u /\ P2A_FLOW_MIN_EXISTS_STATEMENT u n /\
     P2A_FLOW_LX_CONT_STATEMENT u n
     ==> P2A_FLOW_THM_7_10_STATEMENT u n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C3") (CONJUNCTS_THEN2 (LABEL_TAC "FL2")
    (LABEL_TAC "FL3"))) THEN
  REWRITE_TAC[P2A_FLOW_THM_7_10_STATEMENT; DIMINDEX_3] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`; `tau:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) b)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`] P2AU_LX_SLICE_MIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `qm:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `qm:A` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`u:A->bool`; `n:3->bool`] P2AW_FLOW_VIEW_3) THEN
  REWRITE_TAC[P2A_FLOW_VIEW_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `a:real`; `b:real`; `g:real->A->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "REG") (K ALL_TAC))) THEN
  ABBREV_TAC `U = \t. if b - tau <= t /\ t < b then topspace top else {}:A->bool` THEN
  (* the hypotheses of C3 *)
  SUBGOAL_THEN `p2a_atlas_lc (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3))` ASSUME_TAC THENL
   [REWRITE_TAC[P2A_ATLAS_LC_FLOW_VIEW]; ALL_TAC] THEN
  SUBGOAL_THEN `b - tau < b /\ &0 < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace(rfs_vtop (p2a_flow_view (top,atlas) (real_interval[a,b])
                                             (g:real->A->real^3^3)) b)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM P2A_VIEW_PROJ_3] THEN
    ASM_SIMP_TAC[P2AU_FLOW_VTOP; REAL_LT_IMP_LE; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball (p2a_flow_view (top,atlas) (real_interval[a,b])
                            (g:real->A->real^3^3)) b p (&1) =
                mfd_ball (top,atlas) (g b) p (&1)` (LABEL_TAC "BALL") THENL
   [REWRITE_TAC[P2A_VBALL_ALT; P2AU_FLOW_VIEW_PARTS; IN_REAL_INTERVAL; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3))
                (rfs_vball (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (&1))
                (b - tau) b` ASSUME_TAC THENL
   [USE_THEN "BALL" SUBST1_TAC THEN USE_THEN "REG" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MFD_BALL_OPEN] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_st_open (p2a_flow_view (top,atlas) (real_interval[a,b])
                               (g:real->A->real^3^3)) U (b - tau) b` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC P2AU_ST_OPEN_SLAB THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. y IN U t
          ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b])
                                 (g:real->A->real^3^3)) b p (b - t) gamma /\
                      gamma (b - t) = y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN EXPAND_TAC "U" THEN
    COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY] THEN DISCH_TAC THEN
    USE_THEN "FL2" (MP_TAC o REWRITE_RULE[P2A_FLOW_MIN_EXISTS_STATEMENT]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. b - tau < s /\ s < b /\ b - tau <= s ==> (p:A) IN U s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "U" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. b - tau <= t /\ t < b
        ==> ~(p2a_Lmin_set (p2a_flow_view (top,atlas) (real_interval[a,b])
                                          (g:real->A->real^3^3)) b p U t = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `p:A`; `b - t`] P2AU_LX_SLICE_MIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MIN"))) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; p2a_Lmin_set; IN_ELIM_THM] THEN
    EXISTS_TAC `y:A` THEN EXPAND_TAC "U" THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "MIN" (MP_TAC o SPEC `z:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[p2a_lx] THEN
    SUBGOAL_THEN `&0 < &2 * sqrt(b - t)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t e. b - tau <= t /\ t < b /\ &0 < e
          ==> ?d. &0 < d /\
                  !t' y'. b - tau <= t' /\ t' < b /\ abs(t' - t) < d /\ y' IN U t'
                          ==> ?y. y IN U t /\
                                  p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                                            (g:real->A->real^3^3)) b p (b - t) y <=
                                  p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                         b p (b - t') y' + e`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `e:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `p:A`; `b - t`; `e:real`] P2AU_LX_SEMICONT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SC"))) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t':real`; `y':A`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y':A) IN (U:real->A->bool) t'` THEN EXPAND_TAC "U" THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN USE_THEN "SC" (MP_TAC o SPECL [`b - t'`; `y':A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  (* apply C3 *)
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  USE_THEN "C3" (MP_TAC o SPECL
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `p:A`; `b:real`; `b - tau`; `U:real->A->bool`; `&1`; `tau:real`] o
    REWRITE_RULE[P2A_COR_7_12_VIEW_FIX_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `b - tau`) THEN
  REWRITE_TAC[REAL_LE_REFL; REAL_ARITH `b - (b - tau) = tau`] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p2a_lx (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) b p tau y` THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(y:A) IN (U:real->A->bool)(b - tau)` THEN EXPAND_TAC "U" THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* FL4: FL2 and W3 imply FL4.  C3 FIX from the barrier L13 FIX               *)
(* (P2A_COR_7_12_FIX_FROM_BARRIER, pc_p2a_c712; P2A_BARRIER_FIX,             *)
(* pc_p2a_bar), FL3 from W3 (P2AU_FLOW_LX_CONT).                             *)
(* ------------------------------------------------------------------------- *)

let P2AU_FLOW_THM_7_10 = prove
 (`!(u:A->bool) (n:3->bool).
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\ P2B_REQ_P2A_WEAK_STATEMENT u
     ==> P2A_FLOW_THM_7_10_STATEMENT u n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2AU_FLOW_THM_7_10_C3 THEN
  ASM_SIMP_TAC[P2AU_FLOW_LX_CONT] THEN
  MATCH_MP_TAC P2A_COR_7_12_FIX_FROM_BARRIER THEN REWRITE_TAC[P2A_BARRIER_FIX]);;

