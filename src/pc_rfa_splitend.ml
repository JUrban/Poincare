(* ========================================================================= *)
(* Unit pc_rfa_splitend: the endpoint t1 = b of the statement                *)
(* P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT of pc_p2b_splitreq for a flow on (a,b] *)
(* (rfs_flow_upto), and the full statement RFA_P2B_REQ_SMP_SPLIT_PT.  Near   *)
(* (b,y) in a chart the flow agrees up to time b with a smooth family of     *)
(* metrics on a box (RFA_UPTO_BOX); the strong maximum principles reach b    *)
(* through a bump comparison whose barriers are only needed before b         *)
(* (RFA_SPREAD_B_END); the parallel field at time b is the limit of those    *)
(* before b.                                                                 *)
(* ========================================================================= *)

needs "src/pc_rfa_split.ml";;

prioritize_real();;
type_invention_error := true;;



(* ========================================================================= *)
(* Boxes through the endpoint, restriction of boxes, and the                 *)
(* spreading of positivity up to the endpoint (RFA_SPREAD_B_END).          *)
(* ========================================================================= *)

(* Restriction of smooth metric families to smaller boxes (the text of     *)
(* RFU_LSMOOTH_SUB of pc_rf_unique, which is not in this load closure).    *)

let RFA_LSMOOTH_SUB = prove
 (`!U V ta tb ta' tb' (G:real->real^N->real^N^N).
     lrg_lsmooth U ta tb G /\ open V /\ V SUBSET U /\ ta <= ta' /\ ta' < tb' /\ tb' <= tb
     ==> lrg_lsmooth V ta' tb' G`,
  REWRITE_TAC[lrg_lsmooth] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift ta,lift tb) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM SET_TAC[]]]);;

(* Near (b,y) in a chart, a flow on (a,b] with a smooth extension past b   *)
(* (rfs_flow_upto) agrees up to time b with a smooth family of metrics on  *)
(* a box around (b,y).                                                      *)

let RFA_UPTO_BOX = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) c y.
     rfs_flow_upto (top,atlas) a b g /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
     ==> ?d (Gb:real->real^3->real^3^3).
           &0 < d /\ a <= b - d /\ ball(y,d) SUBSET IMAGE (SND c) (FST c) /\
           lrg_lsmooth (ball(y,d)) (b - d) (b + d) Gb /\
           (!t. t <= b ==> Gb t = metric_local atlas c (g t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `c:(A->bool)#(A->real^3)`))) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                a < b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t <= b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t:real = b` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `V = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
  SUBGOAL_THEN `open(V:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t <= b
                    ==> metric_field V (metric_local atlas (c:(A->bool)#(A->real^3))
                                          ((g:real->A->real^3^3) t))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "V" THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `O = interval(lift a,lift(b + e)) PCROSS (V:real^3->bool)` THEN
  SUBGOAL_THEN `open(O:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  ABBREV_TAC
   `Fs = (\m. (vectorize:real^3^3->real^(3,3)finite_prod)
                (inv(&2) %% (matrify m + transp(matrify m)))) o
         (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)` THEN
  SUBGOAL_THEN
   `smooth_map_on O (Fs:real^(1,3)finite_sum->real^(3,3)finite_prod) /\
    (!w. transp(matrify(Fs w)) = matrify(Fs w):real^3^3) /\
    (!t w. a < t /\ t <= b /\ w IN V
           ==> Fs(pastecart (lift t) w) =
               vectorize(metric_local atlas (c:(A->bool)#(A->real^3))
                           ((g:real->A->real^3^3) t) w))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Fs" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL;
                  GSYM VECTORIZE_ADD; GSYM VECTORIZE_CMUL] THEN
      CONJ_TAC THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
      GEN_TAC THEN REWRITE_TAC[o_THM; MATRIFY_VECTORIZE; TRANSP_MATRIX_CMUL;
                               TRANSP_MATRIX_ADD; TRANSP_TRANSP] THEN
      AP_TERM_TAC THEN MATCH_ACCEPT_TAC MATRIX_ADD_SYM;
      MAP_EVERY X_GEN_TAC [`t:real`; `w:real^3`] THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(Fx:real^(1,3)finite_sum->real^(3,3)finite_prod) (pastecart (lift t) w) =
                    vectorize(metric_local atlas (c:(A->bool)#(A->real^3))
                                ((g:real->A->real^3^3) t) w)`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[o_THM; MATRIFY_VECTORIZE] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `transp(metric_local atlas (c:(A->bool)#(A->real^3))
                             ((g:real->A->real^3^3) t) w) =
                    metric_local atlas c (g t) w`
      SUBST1_TAC THENL
       [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
      REWRITE_TAC[CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,3)finite_sum->bool`;
                 `Fs:real^(1,3)finite_sum->real^(3,3)finite_prod`;
                 `pastecart (lift b) (y:real^3)`] RFA_LOCAL_LSMOOTH) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "O" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Fs:real^(1,3)finite_sum->real^(3,3)finite_prod) (pastecart (lift b) y) =
                  vectorize(metric_local atlas (c:(A->bool)#(A->real^3))
                              ((g:real->A->real^3^3) b) y)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[MATRIFY_VECTORIZE] THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `V:real^3->bool` THEN ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = min d0 (b - a)` THEN
  SUBGOAL_THEN `&0 < d /\ d <= d0 /\ a <= b - d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(y:real^3,d) SUBSET ball(y,d0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ball(y:real^3,d) SUBSET V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `interval(lift(b - d0),lift(b + d0)) PCROSS ball(y:real^3,d0) SUBSET O` THEN
    EXPAND_TAC "O" THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (lift b) (w:real^3)` o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ANTS_TAC THENL [ASM SET_TAC[REAL_ARITH `&0 < d0 ==> b - d0 < b /\ b < b + d0`]; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`d:real`;
    `\t w. if t <= b then metric_local atlas (c:(A->bool)#(A->real^3))
                             ((g:real->A->real^3^3) t) w
           else matrify((Fs:real^(1,3)finite_sum->real^(3,3)finite_prod)
                          (pastecart (lift t) w)):real^3^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; X_GEN_TAC `t:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[ETA_AX]] THEN
  REWRITE_TAC[lrg_lsmooth; OPEN_BALL] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t <= b` THEN
    ASM_REWRITE_TAC[ETA_AX] THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `V:real^3->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `ball(y:real^3,d0)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[lrg_lsmooth] o
      check (fun th -> can (term_match [] `lrg_lsmooth U ta tb (G:real->real^3->real^3^3)`)
                            (concl th))) THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `Fs:real^(1,3)finite_sum->real^(3,3)finite_prod` THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `w:real^3`] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[VECTORIZE_MATRIFY] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O:real^(1,3)finite_sum->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `interval(lift(b - d0),lift(b + d0)) PCROSS ball(y:real^3,d0)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC);;

(* A function continuous on K, nonnegative along (t,z) for t1 <= t < b,    *)
(* is nonnegative at (b,z).                                                 *)

let RFA_LEFT_LIMIT_NONNEG = prove
 (`!(h:real^(1,N)finite_sum->real) K t1 b (z:real^N).
     (lift o h) continuous_on K /\ t1 < b /\
     (!t. t1 <= t /\ t <= b ==> pastecart (lift t) z IN K) /\
     (!t. t1 <= t /\ t < b ==> &0 <= h(pastecart (lift t) z))
     ==> &0 <= h(pastecart (lift b) z)`,
  REPEAT GEN_TAC THEN INTRO_TAC "hc t1b inK nn" THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  USE_THEN "hc" (MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift b) (z:real^N)`) THEN
  ANTS_TAC THENL [USE_THEN "inK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[continuous_within; o_THM; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `--((h:real^(1,N)finite_sum->real) (pastecart (lift b) z))`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift(max t1 (b - d / &2))) (z:real^N)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "inK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DIST_PASTECART_CANCEL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "nn" (MP_TAC o SPEC `max t1 (b - d / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Spreading of positivity up to the endpoint b of the barrier hypotheses  *)
(* (barriers only before b, continuity and the box family through b): the  *)
(* comparison with the bump of RFA_SPREAD_CORE_B holds on [t1,b) with      *)
(* constants fixed by the cylinder [t1,b] x cball(y,R), hence at b.        *)

let RFA_SPREAD_B_END = prove
 (`!Om a b' (G:real->real^N->real^N^N) (v:real->real^N->real) B y rho R t1 b dl.
     lrg_lsmooth Om a b' G /\
     (\w. lift(v (drop(fstcart w)) (sndcart w))) continuous_on
       (interval[lift t1,lift b] PCROSS cball(y,R)) /\
     a < t1 /\ t1 < b /\ b < b' /\ &0 < rho /\ rho < R /\ cball(y,R) SUBSET Om /\
     &0 < dl /\
     (!t z. t1 <= t /\ t <= b /\ z IN cball(y,R) ==> &0 <= v t z) /\
     (!t z. t1 < t /\ t < b /\ z IN cball(y,R)
            ==> ?d W (q:real->real^N->real) D.
                  &0 < d /\ open W /\ z IN W /\
                  (!z'. z' IN W ==> v t z' <= q t z') /\ q t z = v t z /\
                  (!s. t - d < s /\ s <= t ==> v s z <= q s z) /\
                  smooth_map_on W (\z'. lift(q t z')) /\
                  ((\s. q s z) has_real_derivative D)
                    (atreal t within {s | t - d <= s /\ s <= t}) /\
                  llap (G t) (q t) z - B * v t z <= D) /\
     (!z. z IN ball(y,rho) ==> dl <= v t1 z)
     ==> !z. z IN ball(y,R) ==> &0 < v b z`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "lsm vsm at1 t1b bb rhop rhoR cb dlp vpos sup init" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  ABBREV_TAC `B1 = max B (&1)` THEN
  SUBGOAL_THEN `&0 < B1 /\ B <= B1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. t1 < t /\ t < b /\ z IN cball(y,R)
          ==> ?d W (q:real->real^N->real) D.
                &0 < d /\ open W /\ z IN W /\
                (!z'. z' IN W ==> (v:real->real^N->real) t z' <= q t z') /\
                q t z = v t z /\
                (!s. t - d < s /\ s <= t ==> v s z <= q s z) /\
                smooth_map_on W (\z'. lift(q t z')) /\
                ((\s. q s z) has_real_derivative D)
                  (atreal t within {s | t - d <= s /\ s <= t}) /\
                llap ((G:real->real^N->real^N^N) t) (q t) z - B1 * v t z <= D`
  (LABEL_TAC "sup1") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sup" (MP_TAC o SPECL [`t:real`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `W:real^N->bool`
      (X_CHOOSE_THEN `q:real->real^N->real` (X_CHOOSE_THEN `D:real`
        STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `W:real^N->bool`; `q:real->real^N->real`; `D:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `B * (v:real->real^N->real) t z <= B1 * v t z` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "vpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `K = interval[lift t1,lift b] PCROSS cball(y:real^N,R)` THEN
  SUBGOAL_THEN
   `compact(K:real^(1,N)finite_sum->bool) /\
    K SUBSET interval(lift a,lift b') PCROSS Om /\
    (!t z. pastecart (lift t) z IN K <=> (t1 <= t /\ t <= b) /\ z IN cball(y,R))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; COMPACT_CBALL] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Om:real^N->bool`; `a:real`; `b':real`; `G:real->real^N->real^N^N`;
                 `K:real^(1,N)finite_sum->bool`] RFA_LSMOOTH_QFORM_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Om:real^N->bool`; `a:real`; `b':real`; `G:real->real^N->real^N^N`;
                 `\w:real^N. norm(w - y) pow 2`;
                 `K:real^(1,N)finite_sum->bool`] RFA_LSMOOTH_LLAP_BOUND) THEN
  ASM_SIMP_TAC[RFA_SQDIST_SMOOTH] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= C1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(llap ((G:real->real^N->real^N^N) t1) (\w:real^N. norm(w - y) pow 2) y)` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_CBALL; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `V = (R pow 2 - rho pow 2) / (b - t1)` THEN
  SUBGOAL_THEN `&0 <= V /\ rho pow 2 + V * (b - t1) = R pow 2 /\ &0 < rho pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(b - t1 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_CHOOSE_TAC `n:num`
    (SPEC `((V + C1) / rho pow 2) * L0 * R pow 2 / &4` REAL_ARCH_SIMPLE) THEN
  ABBREV_TAC `k = n + 2` THEN
  SUBGOAL_THEN `2 <= k /\ ((V + C1) / rho pow 2) * L0 * R pow 2 <= &4 * (&k - &1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `lam = B1 + &2 * &k * ((V + C1) / rho pow 2)` THEN
  (* the bump lies below v at the initial time *)
  SUBGOAL_THEN
   `!z. z IN cball(y,R)
        ==> rfa_sbump dl lam t1 (rho pow 2) V k (y:real^N) t1 z <= (v:real->real^N->real) t1 z`
  (LABEL_TAC "init2") THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(z:real^N) IN ball(y,rho)` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dl:real` THEN
      ASM_SIMP_TAC[RFA_SBUMP_INIT; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`dl:real`; `lam:real`; `t1:real`; `rho pow 2`; `V:real`; `k:num`;
                   `y:real^N`; `t1:real`; `z:real^N`] RFA_SBUMP_ZERO) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~((z:real^N) IN ball(y,rho))` THEN
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN USE_THEN "vpos" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* comparison on [t1,b) *)
  SUBGOAL_THEN
   `!t z. t1 <= t /\ t < b /\ z IN cball(y,R)
          ==> rfa_sbump dl lam t1 (rho pow 2) V k (y:real^N) t z <= (v:real->real^N->real) t z`
  (LABEL_TAC "cmp") THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `t:real = t1` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN USE_THEN "init2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `t1 < t:real /\ t < b'` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `Rt = sqrt(rho pow 2 + V * (t - t1))` THEN
    SUBGOAL_THEN `&0 < rho pow 2 + V * (t - t1) /\ rho pow 2 + V * (t - t1) <= R pow 2 /\
                  rho pow 2 + V * (t - t1) = Rt pow 2 /\ &0 < Rt /\ Rt <= R`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= V * (t - t1) /\ V * (t - t1) <= V * (b - t1)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < rho pow 2 + V * (t - t1) /\ rho pow 2 + V * (t - t1) <= R pow 2`
      STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Rt" THEN
      SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_POS_LT;
               ASSUME `&0 < rho pow 2 + V * (t - t1)`] THEN
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `(z:real^N) IN cball(y,Rt)` THENL
     [ALL_TAC;
      MP_TAC(ISPECL [`dl:real`; `lam:real`; `t1:real`; `rho pow 2`; `V:real`; `k:num`;
                     `y:real^N`; `t:real`; `z:real^N`] RFA_SBUMP_ZERO) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Rt pow 2` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `~((z:real^N) IN cball(y,Rt))` THEN
        REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN USE_THEN "vpos" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]] THEN
    SUBGOAL_THEN `cball(y:real^N,Rt) SUBSET cball(y,R)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `cball(y:real^N,Rt) SUBSET Om` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\w. lift((v:real->real^N->real) (drop(fstcart w)) (sndcart w))) continuous_on
      (interval[lift t1,lift t] PCROSS cball(y,Rt))`
    ASSUME_TAC THENL
     [USE_THEN "vsm" (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
      EXPAND_TAC "K" THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `((V + C1) / rho pow 2) * L0 * Rt pow 2 <= &4 * (&k - &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `((V + C1) / rho pow 2) * L0 * R pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Om:real^N->bool`; `a:real`; `b':real`; `G:real->real^N->real^N^N`;
                   `v:real->real^N->real`; `B1:real`; `y:real^N`; `Rt:real`; `t1:real`;
                   `t:real`; `dl:real`; `lam:real`; `rho pow 2`; `V:real`; `k:num`;
                   `L0:real`; `C1:real`] RFA_SPREAD_CORE_B) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM SET_TAC[];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM SET_TAC[];
        REPEAT STRIP_TAC THEN USE_THEN "vpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM SET_TAC[];
        REPEAT STRIP_TAC THEN USE_THEN "sup1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM SET_TAC[];
        REPEAT STRIP_TAC THEN USE_THEN "init2" MATCH_MP_TAC THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `z:real^N`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the limit t -> b *)
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN cball(y,R)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\w:real^(1,N)finite_sum. (v:real->real^N->real) (drop(fstcart w)) (sndcart w) -
                              rfa_sbump dl lam t1 (rho pow 2) V k (y:real^N)
                                (drop(fstcart w)) (sndcart w)`;
    `K:real^(1,N)finite_sum->bool`; `t1:real`; `b:real`; `z:real^N`]
   RFA_LEFT_LIMIT_NONNEG)) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; REAL_SUB_LE] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [USE_THEN "vsm" ACCEPT_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`dl:real`; `lam:real`; `t1:real`; `rho pow 2`; `V:real`; `k:num`;
                     `y:real^N`] RFA_SBUMP_CONT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
      EXPAND_TAC "K" THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; IN_ELIM_THM;
                  FSTCART_PASTECART; LIFT_DROP] THEN
      SIMP_TAC[];
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "cmp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x <= y ==> &0 < y`) THEN
  MATCH_MP_TAC RFA_SBUMP_POS THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[NORM_POS_LE; ARITH_EQ] THEN
  UNDISCH_TAC `(z:real^N) IN ball(y,R)` THEN
  REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist]);;



(* ========================================================================= *)
(* The strong maximum principles for lambda and R up to the                  *)
(* endpoint b: lambda = 0 or R = 0 at (b,p) forces it on (a,b] x M.       *)
(* ========================================================================= *)

(* lambda in chart coordinates is continuous on [b - d/2,b] x ball in the  *)
(* box of RFA_UPTO_BOX.                                                     *)

let RFA_SECMIN_BOX_CONT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) c d
    (Gb:real->real^3->real^3^3) y1.
     rfs_flow_upto (top,atlas) a b g /\ c IN atlas /\ &0 < d /\ a <= b - d /\
     ball(y1,d) SUBSET IMAGE (SND c) (FST c) /\
     lrg_lsmooth (ball(y1,d)) (b - d) (b + d) Gb /\
     (!t. t <= b ==> Gb t = metric_local atlas c (g t))
     ==> (\w. lift(mfd_sec_min atlas (g (drop(fstcart w))) (chart_inv c (sndcart w))))
         continuous_on (interval[lift(b - d / &2),lift b] PCROSS ball(y1,d))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                (!t. a < t /\ t <= b ==> riemannian_metric atlas ((g:real->A->real^3^3) t))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t:real = b` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  MP_TAC(BETA_RULE(ISPECL
    [`ball(y1:real^3,d)`; `b - d / &2`; `b + d / &2`; `d / &2`; `Gb:real->real^3->real^3^3`;
     `\z:real^(1,3)finite_sum. (vectorize:real^3^3->real^(3,3)finite_prod)
                                 ((Gb:real->real^3->real^3^3) (drop(fstcart z)) (sndcart z))`]
    RFA_LAM_CHART_CONTINUOUS)) THEN
  REWRITE_TAC[OPEN_BALL; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(b - d),lift(b + d)) PCROSS ball(y1:real^3,d)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_NEG) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
  DISCH_THEN(MP_TAC o SPEC `interval[lift(b - d / &2),lift b] PCROSS ball(y1:real^3,d)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; IN_ELIM_THM;
                FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; FSTCART_PASTECART;
              SNDCART_PASTECART; LIFT_DROP; FORALL_LIFT] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM LIFT_NEG; LIFT_EQ] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `c:(A->bool)#(A->real^3)`;
                 `chart_inv (c:(A->bool)#(A->real^3)) y`] RFA_SECMIN_SUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]);;

(* Spreading of positivity of lambda up to the endpoint b in the box of     *)
(* RFA_UPTO_BOX: lambda(t1,z0) > 0 with b - d/2 <= t1 < b gives lambda > 0  *)
(* at time b on the chart ball of radius R around z0.                       *)

let RFA_SECMIN_SPREAD_END = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) c d
    (Gb:real->real^3->real^3^3) y1 z0 R t1.
     rfs_flow_upto (top,atlas) a b g /\
     (!t x. a < t /\ t <= b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     c IN atlas /\ &0 < d /\ a <= b - d /\ ball(y1,d) SUBSET IMAGE (SND c) (FST c) /\
     lrg_lsmooth (ball(y1,d)) (b - d) (b + d) Gb /\
     (!t. t <= b ==> Gb t = metric_local atlas c (g t)) /\
     z0 IN FST c /\ &0 < R /\ cball(SND c z0,R) SUBSET ball(y1,d) /\
     b - d / &2 <= t1 /\ t1 < b /\ &0 < mfd_sec_min atlas (g t1) z0
     ==> !x. x IN FST c /\ SND c x IN ball(SND c z0,R)
             ==> &0 < mfd_sec_min atlas (g b) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ci1") (LABEL_TAC "ci2")))) THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^3)) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `y0 = SND(c:(A->bool)#(A->real^3)) z0` THEN
  SUBGOAL_THEN `(y0:real^3) IN ball(y1,d)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `d:real`;
                 `Gb:real->real^3->real^3^3`; `y1:real^3`] RFA_SECMIN_BOX_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "vc") THEN
  ABBREV_TAC `l0 = mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                               ((g:real->A->real^3^3) t1) z0` THEN
  SUBGOAL_THEN
   `?rho. &0 < rho /\ rho < R /\
          !w. w IN ball(y0,rho)
              ==> l0 / &2 <= mfd_sec_min atlas ((g:real->A->real^3^3) t1)
                                         (chart_inv (c:(A->bool)#(A->real^3)) w)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. lift(mfd_sec_min atlas ((g:real->A->real^3^3) t1)
                  (chart_inv (c:(A->bool)#(A->real^3)) w))) continuous_on ball(y1,d)`
    MP_TAC THENL
     [SUBGOAL_THEN
       `(\w. lift(mfd_sec_min atlas ((g:real->A->real^3^3) t1)
                    (chart_inv (c:(A->bool)#(A->real^3)) w))) =
        (\w. lift(mfd_sec_min atlas (g (drop(fstcart w))) (chart_inv c (sndcart w)))) o
        (\w. pastecart (lift t1) w)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
        ALL_TAC] THEN
      USE_THEN "vc" (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[OPEN_BALL; CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
    DISCH_THEN(MP_TAC o SPEC `y0:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[continuous_at; DIST_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC `l0 / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e (R / &2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) y0 = z0` SUBST1_TAC THENL
     [EXPAND_TAC "y0" THEN USE_THEN "ci1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(y1:real^3,d)`; `b - d`; `b + d`; `Gb:real->real^3->real^3^3`;
                 `\t w. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                          ((g:real->A->real^3^3) t) (chart_inv (c:(A->bool)#(A->real^3)) w)`;
                 `&1`; `y0:real^3`; `rho:real`; `R:real`; `t1:real`; `b:real`;
                 `l0 / &2`] RFA_SPREAD_B_END) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_HALF] THEN REPEAT CONJ_TAC THENL
     [(* continuity on the cylinder *)
      USE_THEN "vc" (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
      MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      (* nonnegativity *)
      MAP_EVERY X_GEN_TAC [`t:real`; `w:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(w:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP (ASSUME
        `!y. y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)
             ==> chart_inv c y IN FST c /\ SND c (chart_inv c y) = y`)) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    (* barriers before b *)
    MAP_EVERY X_GEN_TAC [`t:real`; `w:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^3)) w` THEN
    SUBGOAL_THEN `(x:A) IN FST(c:(A->bool)#(A->real^3)) /\ SND c x = w` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN USE_THEN "ci2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `FST(c:(A->bool)#(A->real^3))`;
                   `c:(A->bool)#(A->real^3)`; `t:real`; `x:A`] RFA_SECMIN_BARRIER_C) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INTER_IDEMPOT] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `dd:real` (X_CHOOSE_THEN `W:real^3->bool`
      (X_CHOOSE_THEN `q:real->real^3->real` (X_CHOOSE_THEN `D:real`
       (X_CHOOSE_THEN `p2:real` (X_CHOOSE_THEN `p3:real` STRIP_ASSUME_TAC)))))) THEN
    MAP_EVERY EXISTS_TAC [`dd:real`; `W:real^3->bool`; `q:real->real^3->real`; `D:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Gb:real->real^3->real^3^3) t =
                  metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= mfd_sec_min atlas ((g:real->A->real^3^3) t) x` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= p2 * p3 /\
                  &0 <= mfd_sec_min atlas ((g:real->A->real^3^3) t) x pow 2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_LE_POW_2]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SND(c:(A->bool)#(A->real^3)) x`) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ci1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN FST(c:(A->bool)#(A->real^3))`)]));;

(* Every point has a neighbourhood N such that positivity of lambda at any  *)
(* (t1,z), z in N, t1 < b, gives positivity at (b,z') for all z' in N.     *)

let RFA_SECMIN_LOCAL_END = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) x.
     rfs_flow_upto (top,atlas) a b g /\
     (!t x. a < t /\ t <= b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     x IN topspace top
     ==> ?N. open_in top N /\ x IN N /\ N SUBSET topspace top /\
             !z z' t1. z IN N /\ z' IN N /\ a < t1 /\ t1 < b /\
                       &0 < mfd_sec_min atlas (g t1) z
                       ==> &0 < mfd_sec_min atlas (g b) z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^3))->bool) x` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `(U:A->bool,phi:A->real^3)`; `(phi:A->real^3) x`]
         RFA_UPTO_BOX) THEN
  ASM_REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `{z | z IN U /\ (phi:A->real^3) z IN ball(phi x,d / &6)}` THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `{z | z IN U /\ (phi:A->real^3) z IN ball(phi x,d / &6)} =
      {z | z IN topspace(subtopology top U) /\
           phi z IN IMAGE phi U INTER ball(phi x,d / &6)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `z:A` THEN
      UNDISCH_TAC `(U:A->bool) SUBSET topspace top` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
      MP_TAC(ISPECL [`phi:A->real^3`; `U:A->bool`; `z:A`] FUN_IN_IMAGE) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^3) U)` THEN
    SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
    MATCH_MP_TAC HOMEOMORPHIC_IMP_CONTINUOUS_MAP THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_BALL] THEN
  MAP_EVERY X_GEN_TAC [`z:A`; `z':A`; `t1:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `t2 = (max t1 (b - d / &2) + b) / &2` THEN
  SUBGOAL_THEN `t1 < t2 /\ b - d / &2 <= t2 /\ t2 < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                 ((g:real->A->real^3^3) t2) z`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `z:A`] RFA_SECMIN_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Nz:A->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`z:A`; `t1:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `(U:A->bool,phi:A->real^3)`; `d:real`;
                 `Gb:real->real^3->real^3^3`; `(phi:A->real^3) x`; `z:A`; `d / &3`; `t2:real`]
         RFA_SECMIN_SPREAD_END) THEN
  ASM_REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN X_GEN_TAC `w:real^3` THEN
    MP_TAC(ISPECL [`(phi:A->real^3) x`; `(phi:A->real^3) z`; `w:real^3`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL] THEN
  MP_TAC(ISPECL [`(phi:A->real^3) z`; `(phi:A->real^3) x`; `(phi:A->real^3) z'`]
         DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`(phi:A->real^3) z`; `(phi:A->real^3) x`] DIST_SYM) THEN
  ASM_REAL_ARITH_TAC);;

(* Spreading of positivity of R up to the endpoint b in the box of          *)
(* RFA_UPTO_BOX (R is its own barrier: dR/dt = Lap R + 2|Ric|^2 before b).  *)

let RFA_SCALAR_SPREAD_END = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) c d
    (Gb:real->real^3->real^3^3) y1 z0 R t1.
     rfs_flow_upto (top,atlas) a b g /\
     (!t x. a < t /\ t <= b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     c IN atlas /\ &0 < d /\ a <= b - d /\ ball(y1,d) SUBSET IMAGE (SND c) (FST c) /\
     lrg_lsmooth (ball(y1,d)) (b - d) (b + d) Gb /\
     (!t. t <= b ==> Gb t = metric_local atlas c (g t)) /\
     z0 IN FST c /\ &0 < R /\ cball(SND c z0,R) SUBSET ball(y1,d) /\
     b - d < t1 /\ t1 < b /\ &0 < mfd_scalar atlas (g t1) z0
     ==> !x. x IN FST c /\ SND c x IN ball(SND c z0,R)
             ==> &0 < mfd_scalar atlas (g b) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t <= b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t:real = b` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ci1") (LABEL_TAC "ci2")))) THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^3)) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  (* R in the chart *)
  SUBGOAL_THEN
   `!t w. a < t /\ t <= b /\ w IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)
          ==> mfd_scalar atlas ((g:real->A->real^3^3) t) (chart_inv c w) =
              lscalar (metric_local atlas c (g t)) w`
  (LABEL_TAC "sc") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_scalar] THEN
    USE_THEN "ci2" (MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `c:(A->bool)#(A->real^3)`;
                   `chart_inv (c:(A->bool)#(A->real^3)) w`] RFA_MFD_SCALAR_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(y1:real^3,d)`; `b - d`; `b + d`; `Gb:real->real^3->real^3^3`]
         LRG_LSMOOTH_LSCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `y0 = SND(c:(A->bool)#(A->real^3)) z0` THEN
  SUBGOAL_THEN `(y0:real^3) IN ball(y1,d)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->A->real^3^3) t1) z0 =
                lscalar ((Gb:real->real^3->real^3^3) t1) y0`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(Gb:real->real^3->real^3^3) t1 =
                  metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t1)`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) y0 = z0` (SUBST1_TAC o SYM) THENL
     [EXPAND_TAC "y0" THEN USE_THEN "ci1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "sc" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `l0 = lscalar ((Gb:real->real^3->real^3^3) t1) y0` THEN
  SUBGOAL_THEN
   `?rho. &0 < rho /\ rho < R /\
          !w. w IN ball(y0,rho) ==> l0 / &2 <= lscalar ((Gb:real->real^3->real^3^3) t1) w`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `metric_field (ball(y1:real^3,d)) ((Gb:real->real^3->real^3^3) t1)`
    MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LRG_LSCALAR_SMOOTH) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    SIMP_TAC[OPEN_BALL; CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
    DISCH_THEN(MP_TAC o SPEC `y0:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[continuous_at; DIST_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC `l0 / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e (R / &2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(y1:real^3,d)`; `b - d`; `b + d`; `Gb:real->real^3->real^3^3`;
                 `\t w. lscalar ((Gb:real->real^3->real^3^3) t) w`;
                 `&0`; `y0:real^3`; `rho:real`; `R:real`; `t1:real`; `b:real`;
                 `l0 / &2`] RFA_SPREAD_B_END) THEN
  REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(b - d),lift(b + d)) PCROSS ball(y1:real^3,d)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      (* nonnegativity *)
      MAP_EVERY X_GEN_TAC [`t:real`; `w:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(w:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(Gb:real->real^3->real^3^3) t =
                    metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "sc" (MP_TAC o SPECL [`t:real`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "ci2" (MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&6 * mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                  ((g:real->A->real^3^3) t)
                                  (chart_inv (c:(A->bool)#(A->real^3)) (w:real^3))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
        MATCH_MP_TAC RFA_SCALAR_GE_6SECMIN THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]]];
      ALL_TAC] THEN
    (* R is its own barrier before b *)
    MAP_EVERY X_GEN_TAC [`t:real`; `w:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c) /\
                  (w:real^3) IN ball(y1,d)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`b - t`; `ball(y1:real^3,d)`; `\s w. lscalar ((Gb:real->real^3->real^3^3) s) w`;
      `llap (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t))
            (lscalar (metric_local atlas c (g t))) w +
       &2 * ltnorm2 2 (metric_local atlas c (g t)) (lric2 (metric_local atlas c (g t))) w`] THEN
    REWRITE_TAC[ETA_AX; OPEN_BALL; REAL_LE_REFL; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
      EXISTS_TAC `\s. lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                 ((g:real->A->real^3^3) s)) w` THEN
      EXISTS_TAC `b - t` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_THM_TAC THEN
        AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`; `a:real`; `b:real`;
                     `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
                     `t:real`; `w:real^3`] LSCALAR_EVOLUTION) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LRG_RICCI_FLOW_ON_CHART THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(Gb:real->real^3->real^3^3) t =
                    metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC LTNORM2_POS THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
      SUBGOAL_THEN `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                      (metric_local atlas c ((g:real->A->real^3^3) t))` ASSUME_TAC THENL
       [SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[LRG_LRIC2_FIELD]];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SND(c:(A->bool)#(A->real^3)) x`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Gb:real->real^3->real^3^3) b =
                metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) b)`
  SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  USE_THEN "sc" (MP_TAC o SPECL [`b:real`; `SND(c:(A->bool)#(A->real^3)) x`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  USE_THEN "ci1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN FST(c:(A->bool)#(A->real^3))`)]));;

(* A function continuous on K and positive at (b,z) is positive at some     *)
(* (s,z) with t0 <= s < b.                                                  *)

let RFA_POS_LEFT_OF = prove
 (`!(h:real^(1,N)finite_sum->real) K t0 b (z:real^N).
     (lift o h) continuous_on K /\ t0 < b /\
     (!t. t0 <= t /\ t <= b ==> pastecart (lift t) z IN K) /\
     &0 < h(pastecart (lift b) z)
     ==> ?s. t0 <= s /\ s < b /\ &0 < h(pastecart (lift s) z)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  MP_TAC(BETA_RULE(ISPECL [`\w:real^(1,N)finite_sum. --((h:real^(1,N)finite_sum->real) w)`;
                           `K:real^(1,N)finite_sum->bool`; `t0:real`; `b:real`; `z:real^N`]
         RFA_LEFT_LIMIT_NONNEG)) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_NEG] THEN MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
    UNDISCH_TAC `(lift o (h:real^(1,N)finite_sum->real)) continuous_on K` THEN
    REWRITE_TAC[o_DEF];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* lambda = 0 at (b,p) forces lambda = 0 on (a,b] x M (flow on (a,b],      *)
(* lambda >= 0 on (a,b], M connected).                                      *)

let RFA_SECMIN_ZERO_UPTO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) p.
     rfs_flow_upto (top,atlas) a b g /\ connected_space top /\
     (!t x. a < t /\ t <= b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     p IN topspace top /\ mfd_sec_min atlas (g b) p = &0
     ==> !t x. a < t /\ t <= b /\ x IN topspace top ==> mfd_sec_min atlas (g t) x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\ a < b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  (* before b *)
  SUBGOAL_THEN
   `!t x. a < t /\ t < b /\ x IN topspace top
          ==> mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t) x = &0`
  (LABEL_TAC "before") THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `t:real`; `x:A`] RFA_SECMIN_STRONG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `p:A`] RFA_SECMIN_LOCAL_END) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Nl"))))) THEN
    SUBGOAL_THEN `&0 < mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                   ((g:real->A->real^3^3) b) p` MP_TAC THENL
     [USE_THEN "Nl" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`p:A`; `(t + b) / &2`] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_LT_REFL]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:real = b` THENL
   [ALL_TAC; USE_THEN "before" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
  (* positivity at (b,x) persists slightly before b *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`;
                 `SND(c:(A->bool)#(A->real^3)) x`] RFA_UPTO_BOX) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `d:real`;
                 `Gb:real->real^3->real^3^3`; `SND(c:(A->bool)#(A->real^3)) x`]
         RFA_SECMIN_BOX_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) (SND c x) = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?s. b - d / &2 <= s /\ s < b /\
        &0 < mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) s) x`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
     [`\w:real^(1,3)finite_sum.
         mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
           ((g:real->A->real^3^3) (drop(fstcart w)))
           (chart_inv (c:(A->bool)#(A->real^3)) (sndcart w))`;
      `interval[lift(b - d / &2),lift b] PCROSS ball(SND(c:(A->bool)#(A->real^3)) x,d)`;
      `b - d / &2`; `b:real`; `SND(c:(A->bool)#(A->real^3)) x`] RFA_POS_LEFT_OF)) THEN
    REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) s) x =
                &0`
  MP_TAC THENL
   [USE_THEN "before" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* R = 0 at (b,p) forces R = 0 on (a,b] x M (flow on (a,b], sec >= 0,     *)
(* M Hausdorff and connected).                                              *)

let RFA_SCALAR_ZERO_UPTO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) p.
     hausdorff_space top /\ connected_space top /\ rfs_flow_upto (top,atlas) a b g /\
     (!t x. a < t /\ t <= b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     p IN topspace top /\ mfd_scalar atlas (g b) p = &0
     ==> !t x. a < t /\ t <= b /\ x IN topspace top ==> mfd_scalar atlas (g t) x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\ a < b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t <= b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t:real = b` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. a < t /\ t <= b /\ x IN topspace top
          ==> &0 <= mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t) x`
  (LABEL_TAC "Rpos") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&6 * mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) t) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC RFA_SCALAR_GE_6SECMIN THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* R in a chart *)
  SUBGOAL_THEN
   `!c t x. c IN atlas /\ a < t /\ t <= b /\ x IN FST c
            ==> mfd_scalar atlas ((g:real->A->real^3^3) t) x =
                lscalar (metric_local atlas (c:(A->bool)#(A->real^3)) (g t)) (SND c x)`
  (LABEL_TAC "sc") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_scalar] THEN
    MATCH_MP_TAC RFA_MFD_SCALAR_CHART THEN EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the box at a point *)
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> ?c d (Gb:real->real^3->real^3^3).
              c IN atlas /\ x IN FST c /\ &0 < d /\ a <= b - d /\
              ball(SND c x,d) SUBSET IMAGE (SND c) (FST c) /\
              lrg_lsmooth (ball(SND c x,d)) (b - d) (b + d) Gb /\
              (!t. t <= b ==> Gb t = metric_local atlas c ((g:real->A->real^3^3) t))`
  (LABEL_TAC "box") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
           CHART_AT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) x`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) x) x`] RFA_UPTO_BOX) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`chart_at (atlas:((A->bool)#(A->real^3))->bool) x`; `d:real`;
                          `Gb:real->real^3->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* before b *)
  SUBGOAL_THEN
   `!t x. a < t /\ t < b /\ x IN topspace top
          ==> mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t) x = &0`
  (LABEL_TAC "before") THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN CONJ_TAC THENL
     [USE_THEN "Rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `t:real`; `x:A`] RFA_SCALAR_STRONG_SEC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    USE_THEN "box" (MP_TAC o SPEC `p:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(A->bool)#(A->real^3)` (X_CHOOSE_THEN `d:real`
      (X_CHOOSE_THEN `Gb:real->real^3->real^3^3` STRIP_ASSUME_TAC))) THEN
    ABBREV_TAC `t1 = (max t (b - d) + b) / &2` THEN
    SUBGOAL_THEN `t < t1 /\ b - d < t1 /\ t1 < b` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `d:real`;
                   `Gb:real->real^3->real^3^3`; `SND(c:(A->bool)#(A->real^3)) p`; `p:A`;
                   `d / &2`; `t1:real`] RFA_SCALAR_SPREAD_END) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `p:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:real = b` THENL
   [ALL_TAC; USE_THEN "before" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN CONJ_TAC THENL
   [USE_THEN "Rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
  USE_THEN "box" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(A->bool)#(A->real^3)` (X_CHOOSE_THEN `d:real`
    (X_CHOOSE_THEN `Gb:real->real^3->real^3^3` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  SUBGOAL_THEN
   `!s. a < s /\ s <= b
        ==> lscalar ((Gb:real->real^3->real^3^3) s) (SND(c:(A->bool)#(A->real^3)) x) =
            mfd_scalar atlas ((g:real->A->real^3^3) s) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(Gb:real->real^3->real^3^3) s =
                  metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) s)`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN USE_THEN "sc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?s. b - d / &2 <= s /\ s < b /\
        &0 < lscalar ((Gb:real->real^3->real^3^3) s) (SND(c:(A->bool)#(A->real^3)) x)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
     [`\w:real^(1,3)finite_sum. lscalar ((Gb:real->real^3->real^3^3) (drop(fstcart w))) (sndcart w)`;
      `interval[lift(b - d / &2),lift b] PCROSS ball(SND(c:(A->bool)#(A->real^3)) x,d)`;
      `b - d / &2`; `b:real`; `SND(c:(A->bool)#(A->real^3)) x`] RFA_POS_LEFT_OF)) THEN
    REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(b - d),lift(b + d)) PCROSS ball(SND(c:(A->bool)#(A->real^3)) x,d)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC LRG_LSMOOTH_LSCALAR THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `lscalar ((Gb:real->real^3->real^3^3) b) (SND(c:(A->bool)#(A->real^3)) x) =
                    mfd_scalar atlas ((g:real->A->real^3^3) b) x` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) s) x =
                &0`
  MP_TAC THENL
   [USE_THEN "before" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lscalar ((Gb:real->real^3->real^3^3) s) (SND(c:(A->bool)#(A->real^3)) x) =
                mfd_scalar atlas ((g:real->A->real^3^3) s) x` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;




(* ========================================================================= *)
(* The parallel field at the endpoint as a limit, the split                  *)
(* and the per-time dichotomy at b, and the split statement for t1 = b.     *)
(* ========================================================================= *)

(* Joint smoothness of P = (R/2) g - Ric along a smooth family of metrics.  *)

let RFA_LSMOOTH_LPCURV = prove
 (`!U ta tb (G:real->real^N->real^N^N) u.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(lpcurv (G (drop(fstcart z))) (sndcart z) u))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[lpcurv; lmetric2; lric2; LIFT_SUB] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC LRG_LSMOOTH_LRICCI THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`; `inv(&2)`;
                   `\z:real^(1,N)finite_sum. lift(lscalar ((G:real->real^N->real^N^N)
                                                 (drop(fstcart z))) (sndcart z))`]
           SMOOTH_MAP_ON_LIFT_CMUL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_LSMOOTH_LSCALAR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
                 `\z:real^(1,N)finite_sum. (u:num->real^N) 1`;
                 `\z:real^(1,N)finite_sum. (G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) **
                                           (u:num->real^N) 2`] SMOOTH_MAP_ON_DOT_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
                 `\z:real^(1,N)finite_sum. (G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)`;
                 `\z:real^(1,N)finite_sum. (u:num->real^N) 2`] LRG_SMOOTH_MATVEC) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; o_DEF]);;

(* Normalisation of a smooth field in a smooth family of metrics, jointly.  *)

let RFA_SMOOTH_GNORMALIZE_GEN = prove
 (`!s (A:real^M->real^N^N) (Y:real^M->real^N).
     open s /\ smooth_map_on s ((vectorize:real^N^N->real^(N,N)finite_prod) o A) /\
     smooth_map_on s Y /\ (!w. w IN s ==> &0 < Y w dot (A w ** Y w))
     ==> smooth_map_on s (\w. inv(sqrt(Y w dot (A w ** Y w))) % Y w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`;
    `\w. lift(inv(sqrt((Y:real^M->real^N) w dot ((A:real^M->real^N^N) w ** Y w))))`;
    `Y:real^M->real^N`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^M->bool`;
    `\w. lift(sqrt((Y:real^M->real^N) w dot ((A:real^M->real^N^N) w ** Y w)))`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^M->bool`;
      `\w. lift((Y:real^M->real^N) w dot ((A:real^M->real^N^N) w ** Y w))`]
      SMOOTH_MAP_ON_LIFT_SQRT) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_SIMP_TAC[]]);;

(* Joint smoothness of the field Y = G^-1 P(b,.) along a smooth family.     *)

let RFA_LSMOOTH_PFIELD = prove
 (`!U ta tb (G:real->real^N->real^N^N) b.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. matrix_inv(G (drop(fstcart z)) (sndcart z)) **
                ((lambda k. lpcurv (G (drop(fstcart z))) (sndcart z)
                              (\m. if m = 1 then b else basis k)):real^N))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
                 `\z:real^(1,N)finite_sum. matrix_inv((G:real->real^N->real^N^N)
                                             (drop(fstcart z)) (sndcart z))`;
                 `\z:real^(1,N)finite_sum. ((lambda k. lpcurv ((G:real->real^N->real^N^N)
                     (drop(fstcart z))) (sndcart z) (\m. if m = 1 then b else basis k)):real^N)`]
         LRG_SMOOTH_MATVEC) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LRG_LSMOOTH_GINV) THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
                 `\k z. lift(lpcurv ((G:real->real^N->real^N^N) (drop(fstcart z))) (sndcart z)
                               (\m. if m = 1 then b else basis k))`]
         (INST_TYPE [`:N`,`:N`; `:(1,N)finite_sum`,`:M`] SMOOTH_MAP_ON_LAMBDA)) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LSMOOTH_LPCURV THEN ASM_REWRITE_TAC[]);;

(* A vector function continuous on K, zero along (t,z) for t1 <= t < b, is  *)
(* zero at (b,z).                                                           *)

let RFA_ZERO_LEFT_LIMIT = prove
 (`!(H:real^(1,N)finite_sum->real^P) K t1 b (z:real^N).
     H continuous_on K /\ t1 < b /\
     (!t. t1 <= t /\ t <= b ==> pastecart (lift t) z IN K) /\
     (!t. t1 <= t /\ t < b ==> H(pastecart (lift t) z) = vec 0)
     ==> H(pastecart (lift b) z) = vec 0`,
  REPEAT GEN_TAC THEN INTRO_TAC "hc t1b inK zero" THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\w:real^(1,N)finite_sum. --(norm((H:real^(1,N)finite_sum->real^P) w))`;
     `K:real^(1,N)finite_sum->bool`; `t1:real`; `b:real`; `z:real^N`]
    RFA_LEFT_LIMIT_NONNEG)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_NEG] THEN MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN USE_THEN "hc" ACCEPT_TAC;
      USE_THEN "t1b" ACCEPT_TAC;
      USE_THEN "inK" ACCEPT_TAC;
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      USE_THEN "zero" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC];
    REWRITE_TAC[REAL_ARITH `&0 <= --x <=> x <= &0`; NORM_LE_0]]);;

(* Closedness of the parallel condition under t -> b: for a field V jointly *)
(* smooth on a box through b, parallel at y for the metrics G(t), t1 <= t  *)
(* < b, it is parallel at y for G(b).                                       *)

let RFA_LCOVD_LIMIT = prove
 (`!U ta tb (G:real->real^N->real^N^N) (V:real^(1,N)finite_sum->real^N) y z t1 b.
     lrg_lsmooth U ta tb G /\ smooth_map_on (interval(lift ta,lift tb) PCROSS U) V /\
     ta < t1 /\ t1 < b /\ b < tb /\ y IN U /\
     (!t. t1 <= t /\ t < b ==> lcovd (G t) (\w. z) (\w. V(pastecart (lift t) w)) y = vec 0)
     ==> lcovd (G b) (\w. z) (\w. V(pastecart (lift b) w)) y = vec 0`,
  REPEAT GEN_TAC THEN INTRO_TAC "lsm vsm ta1 t1b btb yU zero" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  SUBGOAL_THEN
   `!t. ta < t /\ t < tb
        ==> lcovd ((G:real->real^N->real^N^N) t) (\w. z)
                  (\w. (V:real^(1,N)finite_sum->real^N) (pastecart (lift t) w)) y =
            (\w. frechet_derivative V (at w) (pastecart (vec 0) z) +
                 christoffel (G (drop(fstcart w))) (sndcart w) z (V w))
            (pastecart (lift t) y)`
  (LABEL_TAC "sl") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[lcovd; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN BETA_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LRG_SLICE_DERIV THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift ta,lift tb) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\w:real^(1,N)finite_sum.
       frechet_derivative (V:real^(1,N)finite_sum->real^N) (at w) (pastecart (vec 0) z) +
       christoffel ((G:real->real^N->real^N^N) (drop(fstcart w))) (sndcart w) z (V w)`;
    `interval(lift ta,lift tb) PCROSS (U:real^N->bool)`; `t1:real`; `b:real`; `y:real^N`]
   RFA_ZERO_LEFT_LIMIT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `G:real->real^N->real^N^N`;
                       `z:real^N`; `V:real^(1,N)finite_sum->real^N`]
               LRG_LSMOOTH_CHRISTOFFEL_ARG) THEN
        ASM_SIMP_TAC[]];
      USE_THEN "t1b" ACCEPT_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "sl" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN USE_THEN "zero" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "sl" (MP_TAC o SPEC `b:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* The unit field of RFA_PARALLEL_CHART at the endpoint b: parallel at time *)
(* b as the limit of the parallel fields before b (RFA_LCOVD_LIMIT in the  *)
(* box of RFA_UPTO_BOX, where P(b0,b0) > 0 persists).                       *)

let RFA_PARALLEL_CHART_END = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) c N b0 y z.
     rfs_flow_upto (top,atlas) a b g /\ c IN atlas /\
     (!t x. a < t /\ t <= b /\ x IN topspace top ==> mfd_sec_min atlas (g t) x = &0) /\
     open N /\ N SUBSET IMAGE (SND c) (FST c) /\
     (!y. y IN N ==> &0 < lpcurv (metric_local atlas c (g b)) y (\m. b0)) /\
     y IN N
     ==> lcovd (metric_local atlas c (g b)) (\w. z)
           (\w. inv(sqrt((matrix_inv(metric_local atlas c (g b) w) **
                          ((lambda k. lpcurv (metric_local atlas c (g b)) w
                                        (\m. if m = 1 then b0 else basis k)):real^3)) dot
                         (metric_local atlas c (g b) w **
                          (matrix_inv(metric_local atlas c (g b) w) **
                           ((lambda k. lpcurv (metric_local atlas c (g b)) w
                                         (\m. if m = 1 then b0 else basis k)):real^3))))) %
                (matrix_inv(metric_local atlas c (g b) w) **
                 ((lambda k. lpcurv (metric_local atlas c (g b)) w
                               (\m. if m = 1 then b0 else basis k)):real^3)))
           y = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `y:real^3`] RFA_UPTO_BOX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  (* P(b0,b0) > 0 near (b,y) *)
  SUBGOAL_THEN
   `?e. &0 < e /\
        !t w. abs(t - b) < e /\ dist(w,y) < e
              ==> &0 < lpcurv ((Gb:real->real^3->real^3^3) t) w (\m. b0)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(y:real^3,d1)`; `b - d1`; `b + d1`; `Gb:real->real^3->real^3^3`;
                   `(\m:num. (b0:real^3))`] RFA_LSMOOTH_LPCURV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL; CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (lift b) (y:real^3)`) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[continuous_at; DIST_LIFT; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    SUBGOAL_THEN `&0 < lpcurv ((Gb:real->real^3->real^3^3) b) y (\m. b0)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(Gb:real->real^3->real^3^3) b =
                    metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) b)`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `lpcurv ((Gb:real->real^3->real^3^3) b) y (\m. b0)`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `w:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift t) (w:real^3)`) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`pastecart (lift b) (y:real^3)`; `t:real`; `w:real^3`; `e / &2`]
             RFA_PCROSS_BOX_DIST) THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(y:real^3,r) SUBSET N` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  ABBREV_TAC `d = min d1 (min e r)` THEN
  SUBGOAL_THEN `&0 < d /\ d <= d1 /\ d <= e /\ d <= r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(y:real^3,d) SUBSET ball(y,d1) /\ ball(y:real^3,d) SUBSET N`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y:real^3,r)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lrg_lsmooth (ball(y:real^3,d)) (b - d) (b + d) (Gb:real->real^3->real^3^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LSMOOTH_SUB THEN
    MAP_EVERY EXISTS_TAC [`ball(y:real^3,d1)`; `b - d1`; `b + d1`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  SUBGOAL_THEN
   `!t w. b - d < t /\ t < b + d /\ w IN ball(y,d)
          ==> &0 < lpcurv ((Gb:real->real^3->real^3^3) t) w (\m. b0)`
  (LABEL_TAC "Ppos") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(w:real^3) IN ball(y,d)` THEN REWRITE_TAC[IN_BALL] THEN
    MP_TAC(ISPECL [`y:real^3`; `w:real^3`] DIST_SYM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the field Y and its normalisation are smooth on the box *)
  SUBGOAL_THEN
   `!w. w IN interval(lift(b - d),lift(b + d)) PCROSS ball(y:real^3,d)
        ==> &0 < (matrix_inv((Gb:real->real^3->real^3^3) (drop(fstcart w)) (sndcart w)) **
                  ((lambda k. lpcurv (Gb (drop(fstcart w))) (sndcart w)
                                (\m. if m = 1 then b0 else basis k)):real^3)) dot
                 (Gb (drop(fstcart w)) (sndcart w) **
                  (matrix_inv(Gb (drop(fstcart w)) (sndcart w)) **
                   ((lambda k. lpcurv (Gb (drop(fstcart w))) (sndcart w)
                                 (\m. if m = 1 then b0 else basis k)):real^3)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; FSTCART_PASTECART;
                SNDCART_PASTECART; FORALL_LIFT; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `w:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field (ball(y:real^3,d)) ((Gb:real->real^3->real^3^3) t)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `ball(y:real^3,d)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(y:real^3,d)`; `(Gb:real->real^3->real^3^3) t`; `w:real^3`; `b0:real^3`;
                   `b0:real^3`] RFA_PFIELD_DOT) THEN
    ASM_REWRITE_TAC[DOT_LZERO; COND_ID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&0 = x)`) THEN
    USE_THEN "Ppos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`ball(y:real^3,d)`; `b - d`; `b + d`; `Gb:real->real^3->real^3^3`;
    `\w:real^(1,3)finite_sum.
       inv(sqrt((matrix_inv((Gb:real->real^3->real^3^3) (drop(fstcart w)) (sndcart w)) **
                 ((lambda k. lpcurv (Gb (drop(fstcart w))) (sndcart w)
                               (\m. if m = 1 then b0 else basis k)):real^3)) dot
                (Gb (drop(fstcart w)) (sndcart w) **
                 (matrix_inv(Gb (drop(fstcart w)) (sndcart w)) **
                  ((lambda k. lpcurv (Gb (drop(fstcart w))) (sndcart w)
                                (\m. if m = 1 then b0 else basis k)):real^3))))) %
       (matrix_inv(Gb (drop(fstcart w)) (sndcart w)) **
        ((lambda k. lpcurv (Gb (drop(fstcart w))) (sndcart w)
                      (\m. if m = 1 then b0 else basis k)):real^3))`;
    `y:real^3`; `z:real^3`; `b - d / &2`; `b:real`] RFA_LCOVD_LIMIT) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  SUBGOAL_THEN `(Gb:real->real^3->real^3^3) b =
                metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) b)`
  (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN REPEAT CONJ_TAC THENL
   [(* smoothness of the normalised field *)
    MP_TAC(ISPECL
     [`interval(lift(b - d),lift(b + d)) PCROSS ball(y:real^3,d)`;
      `\w:real^(1,3)finite_sum. (Gb:real->real^3->real^3^3) (drop(fstcart w)) (sndcart w)`;
      `\w:real^(1,3)finite_sum.
         matrix_inv((Gb:real->real^3->real^3^3) (drop(fstcart w)) (sndcart w)) **
         ((lambda k. lpcurv (Gb (drop(fstcart w))) (sndcart w)
                       (\m. if m = 1 then b0 else basis k)):real^3)`]
     RFA_SMOOTH_GNORMALIZE_GEN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC RFA_LSMOOTH_PFIELD THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* parallel before b *)
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Gb:real->real^3->real^3^3) t =
                metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`
  SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `t:real`;
                 `ball(y:real^3,d)`; `b0:real^3`; `y:real^3`; `z:real^3`] RFA_PARALLEL_CHART) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ASM SET_TAC[];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t) =
                  (Gb:real->real^3->real^3^3) t` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "Ppos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Locally split at the endpoint b where lambda = 0 on (a,b] and R > 0     *)
(* everywhere at time b (RFA_SPLIT_AT_TIME with RFA_PARALLEL_CHART_END).   *)

let RFA_SPLIT_AT_END = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3).
     rfs_flow_upto (top,atlas) a b g /\
     (!t x. a < t /\ t <= b /\ x IN topspace top ==> mfd_sec_min atlas (g t) x = &0) /\
     (!x. x IN topspace top ==> &0 < mfd_scalar atlas (g b) x)
     ==> p2b_locally_split (top,atlas) (g b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2b_locally_split] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric atlas ((g:real->A->real^3^3) b) /\ a < b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top
                    ==> mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                    ((g:real->A->real^3^3) b) x = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) b`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`;
                 `x:A`] RFA_SECMIN_CHART_3D) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->A->real^3^3) b) x` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_scalar] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  ABBREV_TAC `G = metric_local atlas (c0:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) b)` THEN
  ABBREV_TAC `y1 = SND (c0:(A->bool)#(A->real^3)) x` THEN
  ABBREV_TAC `V = IMAGE (SND (c0:(A->bool)#(A->real^3))) (FST c0)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `metric_field V (G:real^3->real^3^3) /\ (y1:real^3) IN V` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["V"; "G"; "y1"] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) b)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b0:real^3. &0 < lpcurv (G:real^3->real^3^3) y1 (\m. b0)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y1:real^3`; `S:real^3^3`]
           RFA_P3_FRAME_SCALARS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `&0 < lpcurv (G:real^3->real^3^3) y1 (\m. transp(S:real^3^3) ** basis 1)` THENL
     [EXISTS_TAC `transp(S:real^3^3) ** basis 1` THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `&0 < lpcurv (G:real^3->real^3^3) y1 (\m. transp(S:real^3^3) ** basis 2)` THENL
     [EXISTS_TAC `transp(S:real^3^3) ** basis 2` THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    EXISTS_TAC `transp(S:real^3^3) ** basis 3` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `N0 = {y:real^3 | y IN V /\ &0 < lpcurv (G:real^3->real^3^3) y (\m. b0)}` THEN
  SUBGOAL_THEN `open (N0:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N0" THEN
    SUBGOAL_THEN
     `{y:real^3 | y IN V /\ &0 < lpcurv (G:real^3->real^3^3) y (\m. b0)} =
      {y | y IN V /\ (\y. lift(lpcurv G y (\m. b0))) y IN {x:real^1 | x$1 > &0}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP; real_gt]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`] RFA_LPCURV_FIELD) THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[metric_field]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N0:real^3->bool) SUBSET V /\ (y1:real^3) IN N0 /\
                (!y. y IN N0 ==> &0 < lpcurv (G:real^3->real^3^3) y (\m. b0))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N0" THEN REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field N0 (G:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `Yf = \w. matrix_inv((G:real^3->real^3^3) w) **
             ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3)` THEN
  SUBGOAL_THEN `smooth_map_on N0 (Yf:real^3->real^3) /\
                (!w. w IN N0 ==> ~((Yf:real^3->real^3) w = vec 0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `V:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Yf" THEN MATCH_MP_TAC RFA_PFIELD_SMOOTH THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `w:real^3`; `b0:real^3`;
                     `b0:real^3`] RFA_PFIELD_DOT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      UNDISCH_TAC `(Yf:real^3->real^3) w = vec 0` THEN EXPAND_TAC "Yf" THEN
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_LZERO; COND_ID] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&0 = x)`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `V0 = \w. inv(sqrt((Yf:real^3->real^3) w dot ((G:real^3->real^3^3) w ** Yf w))) %
                       Yf w` THEN
  SUBGOAL_THEN
   `smooth_map_on N0 (V0:real^3->real^3) /\
    (!y. y IN N0 ==> (V0:real^3->real^3) y dot ((G:real^3->real^3^3) y ** V0 y) = &1) /\
    (!y z. y IN N0
           ==> frechet_derivative (V0:real^3->real^3) (at y) z +
               christoffel (G:real^3->real^3^3) y z (V0 y) = vec 0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "V0" THEN MATCH_MP_TAC RFA_GNORMALIZE_SMOOTH THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXPAND_TAC "V0" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_GNORM_UNIT THEN EXISTS_TAC `N0:real^3->bool` THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                     `b:real`; `g:real->A->real^3^3`; `c0:(A->bool)#(A->real^3)`;
                     `N0:real^3->bool`; `b0:real^3`; `y:real^3`; `z:real^3`]
             RFA_PARALLEL_CHART_END) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(N0:real^3->bool) SUBSET V` THEN EXPAND_TAC "V" THEN SIMP_TAC[];
          ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[lcovd] THEN
      SUBGOAL_THEN
       `(\w. inv(sqrt((matrix_inv((G:real^3->real^3^3) w) **
                      ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3)) dot
                     (G w ** (matrix_inv(G w) **
                      ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3))))) %
             (matrix_inv(G w) **
              ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3))) =
        (V0:real^3->real^3)`
      (fun th -> REWRITE_TAC[th]) THEN
      MAP_EVERY EXPAND_TAC ["V0"; "Yf"] THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) b`; `c0:(A->bool)#(A->real^3)`; `N0:real^3->bool`;
                 `V0:real^3->real^3`] RFA_PARALLEL_ON_FROM_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(N0:real^3->bool) SUBSET V` THEN EXPAND_TAC "V" THEN SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`{x:A | x IN FST c0 /\ SND (c0:(A->bool)#(A->real^3)) x IN N0}`;
    `\x. chart_jac (c0:(A->bool)#(A->real^3)) (chart_at atlas x) x
                   ((V0:real^3->real^3) (SND c0 x))`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]);;

(* The per-time dichotomy at the endpoint b: lambda = 0 on (a,b] gives g(b) *)
(* flat or locally split.                                                   *)

let RFA_DICHOTOMY_AT_END = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3).
     hausdorff_space top /\ connected_space top /\ rfs_flow_upto (top,atlas) a b g /\
     (!t x. a < t /\ t <= b /\ x IN topspace top ==> mfd_sec_min atlas (g t) x = &0)
     ==> (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> mfd_sectional atlas (g b) x u v = &0) \/
         p2b_locally_split (top,atlas) (g b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric atlas ((g:real->A->real^3^3) b) /\ a < b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t x. a < t /\ t <= b /\ x IN topspace top
                      ==> &0 <= mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                            ((g:real->A->real^3^3) t) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `!x. x IN topspace top
                     ==> &0 < mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                         ((g:real->A->real^3^3) b) x` THENL
   [DISJ2_TAC THEN MATCH_MP_TAC RFA_SPLIT_AT_END THEN
    EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_THEN(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) b) x0 =
                &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&6 * mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) b) x0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC RFA_SCALAR_GE_6SECMIN THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `x0:A`] RFA_SCALAR_ZERO_UPTO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_FLAT_POINT THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]]);;

(* The split statement at the endpoint t1 = b of a flow on (a,b].           *)

let RFA_SPLIT_PT_END = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) p.
     hausdorff_space top /\ connected_space top /\ rfs_flow_upto (top,atlas) a b g /\
     (!t x u v. a < t /\ t <= b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas (g t) x u v) /\
     p IN topspace top
     ==> (!u1 v1. ~collinear {vec 0,u1,v1} /\ mfd_sectional atlas (g b) p u1 v1 = &0
                  ==> !t. a < t /\ t <= b
                          ==> (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                                       ==> mfd_sectional atlas (g t) x u v = &0) \/
                              p2b_locally_split (top,atlas) (g t)) /\
         (mfd_scalar atlas (g b) p = &0
          ==> !t x u v. a < t /\ t <= b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                        ==> mfd_sectional atlas (g t) x u v = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                a < b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t <= b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t:real = b` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t x. a < t /\ t <= b /\ x IN topspace top
                      ==> &0 <= mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                            ((g:real->A->real^3^3) t) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_SECMIN_NONNEG THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u1:real^3`; `v1:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                              ((g:real->A->real^3^3) b) p = &0`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
          `mfd_sectional (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) b)
                         p u1 v1 = &0`) (concl th))) THEN
        MATCH_MP_TAC RFA_SEC_GE_SECMIN THEN EXISTS_TAC `top:A topology` THEN
        ASM_SIMP_TAC[REAL_LE_REFL]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `p:A`] RFA_SECMIN_ZERO_UPTO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t:real = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC RFA_DICHOTOMY_AT_END THEN
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_DICHOTOMY_AT_TIME THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `p:A`] RFA_SCALAR_ZERO_UPTO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_FLAT_POINT THEN
  EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[]);;




(* ========================================================================= *)
(* The main theorem RFA_P2B_REQ_SMP_SPLIT_PT                                 *)
(* (P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT of pc_p2b_splitreq): interior times   *)
(* t1 < b by RFA_SPLIT_PT_INTERIOR, the endpoint t1 = b by RFA_SPLIT_PT_END. *)
(* ========================================================================= *)

let RFA_P2B_REQ_SMP_SPLIT_PT = prove
 (`!w:A->bool. P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
    `a:real`; `b:real`; `p:A`; `t1:real`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `t1:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC RFA_SPLIT_PT_END THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `t1:real`] RFA_SPLIT_PT_INTERIOR) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

