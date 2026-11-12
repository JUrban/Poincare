(* ========================================================================= *)
(* Unit pc_p2c_c1116a (Part 2C): MT Claim 11.12 and its ingredients for one  *)
(* Ricci flow on (-Tm,0] with complete slices of sec >= 0 and abs Rm bounded *)
(* on every [a,0]: the Harnack bound (s + Tm) R(x,s) <= (t + Tm) R(x,t)      *)
(* (s <= t < 0) and R <= Q Tm / (s + Tm), distances non-increasing in time,  *)
(* continuity of the distances at 0, and the additive distance distortion    *)
(* d_s <= d_0 + c Tm sqrt Q.                                                 *)
(* ========================================================================= *)

needs "src/pc_p2c_c1116req.ml";;
needs "src/pc_p2b_l925.ml";;
needs "src/pc_lim_back.ml";;
needs "src/pc_p2b_rmhalf.ml";;
needs "src/pc_p2b_flatfwd.ml";;
needs "src/pc_rf_unique_a14.ml";;
needs "src/pc_rfa_scalar.ml";;
needs "src/pc_apx_scal.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The Harnack bound (MT p. 273: dR/dt >= -R/(t+T)).                         *)
(* ------------------------------------------------------------------------- *)

(* A linear inequality in a passes to the limit a -> -Tm. *)

let P2FL_LIMIT_IN_A = prove
 (`!s t Tm Rs Rt.
     --Tm < s /\ (!a. --Tm < a /\ a < s ==> (s - a) * Rs <= (t - a) * Rt)
     ==> (s + Tm) * Rs <= (t + Tm) * Rt`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `dl = (s + Tm) * Rs - (t + Tm) * Rt` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL [EXPAND_TAC "dl" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c = abs(Rs - Rt)` THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL [EXPAND_TAC "c" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = min ((s + Tm) / &2) (dl / (c + &1))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta < s + Tm /\ eta * (c + &1) <= dl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `x <= y / &2 /\ &0 < y ==> x < y`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 < c + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dl / (c + &1) * (c + &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `eta * (Rs - Rt) <= eta * c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    EXPAND_TAC "c" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--Tm + eta` o check (fun th -> is_forall(concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(s + Tm) * Rs - (t + Tm) * Rt = dl` THEN
  UNDISCH_TAC `eta * (c + &1) <= dl` THEN UNDISCH_TAC `eta * (Rs - Rt) <= eta * c` THEN
  UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC);;

(* The Harnack monotonicity: (s + Tm) R(x,s) is non-decreasing on (-Tm,0). *)

let P2FL_HARNACK_MONO = prove
 (`!(w:B->bool) top atlas (g:real->B->real^3^3) Tm x.
     P2C_REQ_HARNACK_STATEMENT w /\
     hausdorff_space top /\ &0 < Tm /\
     (!a b. --Tm < a /\ a < b /\ b <= &0 ==> ricci_flow_on (top,atlas) a b g) /\
     (!s. --Tm < s /\ s <= &0
          ==> mfd_complete (top,atlas) (g s) /\
              (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                       ==> &0 <= mfd_sectional atlas (g s) y u v)) /\
     (!a. --Tm < a ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                 ==> mfd_rm_norm atlas (g s) y <= K) /\
     x IN topspace top
     ==> !s t. --Tm < s /\ s <= t /\ t < &0
               ==> (s + Tm) * mfd_scalar atlas (g s) x <= (t + Tm) * mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "harn") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
      (CONJUNCTS_THEN2 (LABEL_TAC "kb") ASSUME_TAC)))))) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2FL_LIMIT_IN_A THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "kb" (MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "K")) THEN
  (* the derivative of R(x,.) on (a,0) *)
  SUBGOAL_THEN `?Df. !u. a < u /\ u < &0
                         ==> ((\r. mfd_scalar atlas ((g:real->B->real^3^3) r) x)
                              has_real_derivative Df u) (atreal u)`
  (X_CHOOSE_THEN `Df:real->real` (LABEL_TAC "der")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC `u:real` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `a:real`; `&0`;
                   `g:real->B->real^3^3`; `u:real`; `x:B`] RFA_MFD_SCALAR_EVOLUTION) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the slice facts on (a,0) *)
  SUBGOAL_THEN `(!r. a < r /\ r < &0 ==> mfd_complete (top,atlas) ((g:real->B->real^3^3) r)) /\
                (!r y p q. a < r /\ r < &0 /\ y IN topspace top /\ ~collinear {vec 0,p,q}
                           ==> &0 <= mfd_sectional atlas ((g:real->B->real^3^3) r) y p q) /\
                (!r y. a < r /\ r < &0 /\ y IN topspace top
                       ==> mfd_rm_norm atlas ((g:real->B->real^3^3) r) y <= K)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      USE_THEN "sl" (MP_TAC o SPEC `r:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`r:real`; `y:B`; `p:real^3`; `q:real^3`] THEN STRIP_TAC THEN
      USE_THEN "sl" (MP_TAC o SPEC `r:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`r:real`; `y:B`] THEN STRIP_TAC THEN
      USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* Harnack: -R/(u - a) <= Df u *)
  SUBGOAL_THEN `!u. a < u /\ u < &0
                    ==> --(mfd_scalar atlas ((g:real->B->real^3^3) u) x / (u - a)) <= Df u`
  (LABEL_TAC "hb") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    USE_THEN "harn" (MP_TAC o GEN_REWRITE_RULE I [P2C_REQ_HARNACK_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                               `a:real`; `&0`; `g:real->B->real^3^3`; `K:real`; `x:B`; `u:real`;
                               `(Df:real->real) u`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* f(u) = (u - a) R(x,u) is non-decreasing on (a,0) *)
  MP_TAC(ISPECL [`\u. (u - a) * mfd_scalar atlas ((g:real->B->real^3^3) u) x`;
                 `\u. mfd_scalar atlas ((g:real->B->real^3^3) u) x + (u - a) * Df u`;
                 `real_interval(a,&0)`; `s:real`; `t:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) u) x + (u - a) * Df u =
                    (u - a) * Df u + &1 * mfd_scalar atlas (g u) x` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN CONJ_TAC THENL
       [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
        USE_THEN "der" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < u - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "hb" (MP_TAC o C MP (CONJ (ASSUME `a < u`) (ASSUME `u < &0`)) o SPEC `u:real`) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(u - a) * --(mfd_scalar atlas ((g:real->B->real^3^3) u) x / (u - a)) <=
                    (u - a) * Df u` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `(u - a) * --(mfd_scalar atlas ((g:real->B->real^3^3) u) x / (u - a)) =
                    --(mfd_scalar atlas (g u) x)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < u - a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* R >= 0 and the global bound (s + Tm) R(x,s) <= Q on (-Tm,0] (Q from abs   *)
(* Rm on [-Tm/2,0] and the Harnack monotonicity).                            *)
(* ------------------------------------------------------------------------- *)

let P2FL_SCALAR_BOUND = prove
 (`!(w:B->bool) top atlas (g:real->B->real^3^3) Tm.
     P2C_REQ_HARNACK_STATEMENT w /\
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < Tm /\
     (!a b. --Tm < a /\ a < b /\ b <= &0 ==> ricci_flow_on (top,atlas) a b g) /\
     (!s. --Tm < s /\ s <= &0
          ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
              (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                       ==> &0 <= mfd_sectional atlas (g s) y u v)) /\
     (!a. --Tm < a ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                 ==> mfd_rm_norm atlas (g s) y <= K)
     ==> ?Q. &0 < Q /\
             !s x. --Tm < s /\ s <= &0 /\ x IN topspace top
                   ==> &0 <= mfd_scalar atlas (g s) x /\
                       (s + Tm) * mfd_scalar atlas (g s) x <= Q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "harn") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rf")
      (CONJUNCTS_THEN2 (LABEL_TAC "sl") (LABEL_TAC "kb"))))))) THEN
  USE_THEN "kb" (MP_TAC o SPEC `--Tm / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "K")) THEN
  (* R >= 0 and R <= 6 K on [-Tm/2,0] *)
  SUBGOAL_THEN `!s x. --Tm < s /\ s <= &0 /\ x IN topspace top
                      ==> &0 <= mfd_scalar atlas ((g:real->B->real^3^3) s) x`
  (LABEL_TAC "nn") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "sl" (MP_TAC o C MP (CONJ (ASSUME `--Tm < s`) (ASSUME `s <= &0`)) o
                   SPEC `s:real`) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `x:B`;
                   `mfd_rm_norm atlas ((g:real->B->real^3^3) s) x`] P2BFF_MFD_SCALAR_BOUNDS) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s x. --Tm / &2 <= s /\ s <= &0 /\ x IN topspace top
                      ==> mfd_scalar atlas ((g:real->B->real^3^3) s) x <= &6 * max K (&0)`
  (LABEL_TAC "r6") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "sl" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `mfd_rm_norm atlas ((g:real->B->real^3^3) s) x <= max K (&0)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= K ==> x <= max K (&0)`) THEN
      USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `x:B`; `max K (&0)`] P2BFF_MFD_SCALAR_BOUNDS) THEN
    ASM_SIMP_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `Tm * &6 * max K (&0) + &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `x:B`] THEN STRIP_TAC THEN
  CONJ_TAC THENL [USE_THEN "nn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + &1`) THEN
  ASM_CASES_TAC `--Tm / &2 <= s` THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      USE_THEN "nn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "r6" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(--Tm / &2 + Tm) * mfd_scalar atlas ((g:real->B->real^3^3) (--Tm / &2)) x` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`w:B->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `Tm:real`; `x:B`] P2FL_HARNACK_MONO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      USE_THEN "sl" (MP_TAC o C MP (ASSUME `--Tm < r /\ r <= &0`) o SPEC `r:real`) THEN
      SIMP_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      USE_THEN "nn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "r6" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Comparison of the metrics and distances up to the end time of a flow that *)
(* is smooth up to b (rfs_flow_upto): with abs Rm <= K, g(s) <= exp(4 K (b - *)
(* s)) g(b) (Gronwall, as LIM_METRIC_BACK); hence d_s <= exp(2 K (b - s))    *)
(* d_b, and with sec >= 0, d_b <= d_s.                                       *)
(* ------------------------------------------------------------------------- *)

let P2FL_QF_NEAR_END = prove
 (`!top atlas (g:real->B->real^3^3) a b K s x (v:real^3).
     rfs_flow_upto (top,atlas) a b g /\ &0 <= K /\
     (!t y. a < t /\ t < b /\ y IN topspace top ==> mfd_rm_norm atlas (g t) y <= K) /\
     a < s /\ s <= b /\ x IN topspace top
     ==> v dot (g s x ** v) <= exp(&4 * K * (b - s)) * (v dot (g b x ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = b:real` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < b:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                !t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->B->real^3^3) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. exp(&4 * K * t) * ((v:real^3) dot ((g:real->B->real^3^3) t x ** v))`;
                 `\t. exp(&4 * K * t) *
                      ((v:real^3) dot ((--(&2) %% mfd_ricci_matrix atlas ((g:real->B->real^3^3) t) x)
                                       ** v)) +
                      (&4 * K * exp(&4 * K * t)) * ((v:real^3) dot (g t x ** v))`;
                 `s:real`; `b:real`] REAL_MVT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN X_GEN_TAC `r:real` THEN
        DISCH_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
        EXISTS_TAC `&4 * K * exp(&4 * K * r)` THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
        MATCH_MP_TAC LIM_UPTO_QF_CONT THEN
        MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `a:real`] THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN CONJ_TAC THENL
       [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
        MATCH_MP_TAC P4_RF_PREFERRED_DERIV THEN
        MAP_EVERY EXISTS_TAC [`top:B topology`; `a:real`; `b:real`] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "mvt"))) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v dot ((--(&2) %% mfd_ricci_matrix atlas ((g:real->B->real^3^3) t) x) ** v) =
                --(&2) * mfd_ricci atlas (g t) x v v` ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) t`; `x:B`; `v:real^3`; `v:real^3`] P3S_MFD_RICCI_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (v:real^3) dot ((g:real->B->real^3^3) t x ** v)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_QF_NONNEG THEN
        MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
        ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ricci atlas ((g:real->B->real^3^3) t) x v v <=
                &2 * K * ((v:real^3) dot (g t x ** v))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) t`; `x:B`; `v:real^3`] P2BFF_MFD_RICCI_ABS) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `mfd_rm_norm atlas ((g:real->B->real^3^3) t) x * ((v:real^3) dot (g t x ** v)) <=
                  K * (v dot (g t x ** v))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&4 * K * s) * ((v:real^3) dot ((g:real->B->real^3^3) s x ** v)) <=
                exp(&4 * K * b) * (v dot (g b x ** v))` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!d x y:real. &0 <= d /\ y - x = d ==> x <= y`) THEN
    EXISTS_TAC `(exp(&4 * K * t) *
                 ((v:real^3) dot ((--(&2) %% mfd_ricci_matrix atlas ((g:real->B->real^3^3) t) x)
                                  ** v)) +
                 (&4 * K * exp(&4 * K * t)) * ((v:real^3) dot (g t x ** v))) * (b - s)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&0 < exp(&4 * K * t)` MP_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    SPEC_TAC(`exp(&4 * K * t)`,`ex:real`) THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= ex * (&4 * K * ((v:real^3) dot ((g:real->B->real^3^3) t x ** v)) -
                              &2 * mfd_ricci atlas (g t) x v v)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(&4 * K * s)) * exp(&4 * K * s) = &1 /\
                exp(--(&4 * K * s)) * exp(&4 * K * b) = exp(&4 * K * (b - s))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_NEG_MUL2];
      REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(&4 * K * s)) *
                (exp(&4 * K * s) * ((v:real^3) dot ((g:real->B->real^3^3) s x ** v))) <=
                exp(--(&4 * K * s)) * (exp(&4 * K * b) * (v dot (g b x ** v)))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`exp(--(&4 * K * s))`; `exp(&4 * K * s)`;
                 `(v:real^3) dot ((g:real->B->real^3^3) s x ** v)`] REAL_MUL_ASSOC) THEN
  MP_TAC(ISPECL [`exp(--(&4 * K * s))`; `exp(&4 * K * b)`;
                 `(v:real^3) dot ((g:real->B->real^3^3) b x ** v)`] REAL_MUL_ASSOC) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN REAL_ARITH_TAC);;

(* The distances. *)

let P2FL_DIST_NEAR_END = prove
 (`!top atlas (g:real->B->real^3^3) a b K s x y.
     rfs_flow_upto (top,atlas) a b g /\ &0 <= K /\
     (!t z. a < t /\ t < b /\ z IN topspace top ==> mfd_rm_norm atlas (g t) z <= K) /\
     a < s /\ s <= b /\ mfd_joinable (top,atlas) x y
     ==> mfd_dist (top,atlas) (g s) x y <= exp(&2 * K * (b - s)) * mfd_dist (top,atlas) (g b) x y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
    ASM_CASES_TAC `s = b:real` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * K * (b - s)) = sqrt(exp(&4 * K * (b - s)))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    REWRITE_TAC[REAL_EXP_POS_LE; REAL_POW_2; GSYM REAL_EXP_ADD] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2BX_DIST_COMPARE THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2FL_QF_NEAR_END THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `a:real`] THEN
  ASM_REWRITE_TAC[]);;

let P2FL_DIST_MONO = prove
 (`!top atlas (g:real->B->real^3^3) a b s x y.
     rfs_flow_upto (top,atlas) a b g /\
     (!t z u w. a < t /\ t <= b /\ z IN topspace top /\ ~collinear {vec 0,u,w}
                ==> &0 <= mfd_sectional atlas (g t) z u w) /\
     a < s /\ s <= b /\ mfd_joinable (top,atlas) x y
     ==> mfd_dist (top,atlas) (g b) x y <= mfd_dist (top,atlas) (g s) x y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
    ASM_CASES_TAC `s = b:real` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `(g:real->B->real^3^3) b`; `&1`; `x:B`; `y:B`]
                P2BX_DIST_COMPARE) THEN
  REWRITE_TAC[SQRT_1; REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_POS] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIM_METRIC_BACK THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `a:real`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MT Claim 11.12, the distance distortion d_s <= d_0 + c on (-Tm,0]         *)
(* (P2C_REQ_DIST_DISTORTION with k(r) = Q / (2 (r + Tm)), the integral by    *)
(* the fundamental theorem of calculus, and the limit to the end time 0 by   *)
(* P2FL_DIST_NEAR_END).                                                      *)
(* ------------------------------------------------------------------------- *)

(* A bound that holds for all t in [t1,0) with the factor exp(2 K (-t))      *)
(* holds without it.                                                          *)

let P2FL_EXP_LIMIT0 = prove
 (`!d D c K t1.
     &0 <= K /\ &0 <= D /\ t1 < &0 /\
     (!t. t1 <= t /\ t < &0 ==> d <= exp(&2 * K * --t) * D + c)
     ==> d <= D + c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `dl = d - (D + c)` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL [EXPAND_TAC "dl" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * (K + &1) /\ &0 < &4 * (K + &1) * (D + &1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = min (--t1) (min (inv(&4 * (K + &1))) (dl / (&4 * (K + &1) * (D + &1)))) / &2` THEN
  SUBGOAL_THEN `&0 < u /\ u < --t1 /\ u <= inv(&4 * (K + &1)) /\
                u <= dl / (&4 * (K + &1) * (D + &1))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    SUBGOAL_THEN `&0 < inv(&4 * (K + &1)) /\ &0 < dl / (&4 * (K + &1) * (D + &1))`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV; REAL_LT_DIV]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--u` o check (fun th -> is_forall(concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_NEG_NEG]] THEN
  (* exp(2 K u) <= 1 + 4 K u *)
  SUBGOAL_THEN `exp(&2 * K * u) <= &1 + &2 * (&2 * K * u)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `K * u <= (K + &1) * inv(&4 * (K + &1))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(K + &1) * inv(&4 * (K + &1)) = inv(&4)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &4 * (K + &1)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* 4 K u D < dl *)
  SUBGOAL_THEN `&4 * K * u * D < dl` ASSUME_TAC THENL
   [SUBGOAL_THEN `u * (&4 * (K + &1) * (D + &1)) <= dl` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `dl / (&4 * (K + &1) * (D + &1)) * (&4 * (K + &1) * (D + &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 * K * u * D < u * (&4 * (K + &1) * (D + &1))` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < y - x ==> x < y`) THEN
      SUBGOAL_THEN `u * (&4 * (K + &1) * (D + &1)) - &4 * K * u * D = u * (&4 * (K + D + &1))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * K * u) * D <= (&1 + &2 * (&2 * K * u)) * D` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `d - (D + c) = dl` THEN UNDISCH_TAC `&4 * K * u * D < dl` THEN
  REAL_ARITH_TAC);;

(* The integral of the distortion rate. *)

let P2FL_RATE_INTEGRAL = prove
 (`!Q Tm t1 t2.
     &0 < Q /\ &0 < Tm /\ --Tm < t1 /\ t1 <= t2 /\ t2 <= &0
     ==> real_integral (real_interval[t1,t2])
           (\s. &8 * sqrt(&2 * (Q / (&2 * (s + Tm))) / &3)) <= &16 * sqrt(Q * Tm)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. &16 * sqrt(Q / &3) * sqrt(s + Tm)`;
                 `\s. &8 * sqrt(&2 * (Q / (&2 * (s + Tm))) / &3)`; `t1:real`; `t2:real`]
                REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    SUBGOAL_THEN `&0 < r + Tm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 * (Q / (&2 * (r + Tm))) / &3 = (Q / &3) / (r + Tm)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < r + Tm` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_DIV; REAL_LT_IMP_LE; REAL_LE_DIV; REAL_POS] THEN
    SUBGOAL_THEN `&0 < sqrt(r + Tm)` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  SUBGOAL_THEN `&0 <= sqrt(t1 + Tm) /\ sqrt(t2 + Tm) <= sqrt Tm /\ &0 <= sqrt(Q / &3)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(Q / &3) * sqrt Tm <= sqrt(Q * Tm)` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(Q / &3) * sqrt Tm = sqrt(Q / &3 * Tm)` SUBST1_TAC THENL
     [REWRITE_TAC[SQRT_MUL]; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN
    SUBGOAL_THEN `&0 <= Q * Tm` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(Q / &3) * sqrt(t2 + Tm) <= sqrt(Q / &3) * sqrt Tm /\
                &0 <= sqrt(Q / &3) * sqrt(t1 + Tm)` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `sqrt(Q / &3) * sqrt Tm <= sqrt(Q * Tm)` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* MT Lemma 11.11 in direct, pointwise form.  Bounded curvature at bounded   *)
(* distance from base points with R >= 2 bounds R(z,s) for every z joined at *)
(* time s to a point y with R(y,s) <= C' by a connected set W of             *)
(* g(s)-diameter <= L (the base point: a point of W with R = 2 by the        *)
(* intermediate value theorem on W, or y itself).  MT applies it to X = W    *)
(* compact connected; here W may depend on z and s.                          *)
(* ------------------------------------------------------------------------- *)

let P2FL_LEMMA_11_11 = prove
 (`!top atlas (g:real->B->real^3^3) Tm Cp L.
     smooth_manifold_atlas top atlas /\
     (!s. --Tm < s /\ s <= &0 ==> riemannian_metric atlas (g s)) /\
     (!A. ?D. !s y z. --Tm < s /\ s <= &0 /\ y IN topspace top /\ z IN topspace top /\
                      &2 <= mfd_scalar atlas (g s) y /\
                      mfd_dist (top,atlas) (g s) y z <= A * inv(sqrt(mfd_scalar atlas (g s) y))
                      ==> mfd_scalar atlas (g s) z <= D * mfd_scalar atlas (g s) y)
     ==> ?Kx. !s W y z.
                --Tm < s /\ s <= &0 /\ connected_in top W /\ W SUBSET topspace top /\
                y IN W /\ z IN W /\ mfd_scalar atlas (g s) y <= Cp /\
                (!p q. p IN W /\ q IN W ==> mfd_dist (top,atlas) (g s) p q <= L)
                ==> mfd_scalar atlas (g s) z <= Kx`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rm") (LABEL_TAC "bc"))) THEN
  ABBREV_TAC `C2 = max Cp (&2)` THEN
  SUBGOAL_THEN `&2 <= C2 /\ Cp <= C2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C2" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "bc" (MP_TAC o SPEC `max L (&0) * sqrt C2`) THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` (LABEL_TAC "D")) THEN
  EXISTS_TAC `max (&2) (max D (&0) * C2)` THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `W:B->bool`; `y:B`; `z:B`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "diam")))))))) THEN
  ASM_CASES_TAC `mfd_scalar atlas ((g:real->B->real^3^3) s) z <= &2` THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s)` ASSUME_TAC THENL
   [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?w. w IN W /\ &2 <= mfd_scalar atlas ((g:real->B->real^3^3) s) w /\
                    mfd_scalar atlas (g s) w <= C2`
  (X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) THENL
   [ASM_CASES_TAC `&2 <= mfd_scalar atlas ((g:real->B->real^3^3) s) y` THENL
     [EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `is_realinterval (IMAGE (mfd_scalar atlas ((g:real->B->real^3^3) s)) W)`
    MP_TAC THENL
     [REWRITE_TAC[GSYM CONNECTED_IN_EUCLIDEANREAL] THEN
      MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN(MP_TAC o SPECL [`mfd_scalar atlas ((g:real->B->real^3^3) s) y`;
                               `mfd_scalar atlas ((g:real->B->real^3^3) s) z`; `&2`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:B` THEN
    STRIP_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&2 = mfd_scalar atlas ((g:real->B->real^3^3) s) w` THEN
    UNDISCH_TAC `&2 <= C2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:B) IN topspace top /\ (z:B) IN topspace top` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) ((g:real->B->real^3^3) s) w z <=
                (max L (&0) * sqrt C2) * inv(sqrt(mfd_scalar atlas (g s) w))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `max L (&0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= L ==> x <= max L (&0)`) THEN
      USE_THEN "diam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt(mfd_scalar atlas ((g:real->B->real^3^3) s) w) /\
                  sqrt(mfd_scalar atlas (g s) w) <= sqrt C2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM real_div] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  USE_THEN "D" (MP_TAC o SPECL [`s:real`; `w:B`; `z:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `D * mfd_scalar atlas ((g:real->B->real^3^3) s) w <= max D (&0) * C2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `max D (&0) * mfd_scalar atlas ((g:real->B->real^3^3) s) w` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* MT Claim 11.12 (p. 273): with (s + Tm) R <= Q on (-Tm,0], d_0 <= d_s <=   *)
(* d_0 + 16 sqrt(Q Tm).                                                      *)
(* ------------------------------------------------------------------------- *)

let P2FL_CLAIM_11_12 = prove
 (`!(w:B->bool) top atlas (g:real->B->real^3^3) Tm Q.
     P2C_REQ_DIST_DISTORTION_STATEMENT w /\
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ connected_space top /\
     &0 < Tm /\ &0 < Q /\
     (!a b. --Tm < a /\ a < b /\ b <= &0 ==> ricci_flow_on (top,atlas) a b g) /\
     (!a. --Tm < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
     (!s. --Tm < s /\ s <= &0
          ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
              (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                       ==> &0 <= mfd_sectional atlas (g s) y u v)) /\
     (!a. --Tm < a ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                 ==> mfd_rm_norm atlas (g s) y <= K) /\
     (!s x. --Tm < s /\ s <= &0 /\ x IN topspace top
            ==> &0 <= mfd_scalar atlas (g s) x /\ (s + Tm) * mfd_scalar atlas (g s) x <= Q)
     ==> !s x y. --Tm < s /\ s <= &0 /\ x IN topspace top /\ y IN topspace top
                 ==> mfd_dist (top,atlas) (g (&0)) x y <= mfd_dist (top,atlas) (g s) x y /\
                     mfd_dist (top,atlas) (g s) x y <=
                     mfd_dist (top,atlas) (g (&0)) x y + &16 * sqrt(Q * Tm)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dd") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rf")
    (CONJUNCTS_THEN2 (LABEL_TAC "up") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (CONJUNCTS_THEN2 (LABEL_TAC "kb") (LABEL_TAC "qb"))))))))))) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `x:B`; `y:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (x:B) y` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `a0 = (s + --Tm) / &2` THEN
  SUBGOAL_THEN `--Tm < a0 /\ a0 < s /\ a0 < &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_flow_upto (top,atlas) a0 (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "up" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t z u v. a0 < t /\ t <= &0 /\ z IN topspace top /\ ~collinear {vec 0,u,v}
                          ==> &0 <= mfd_sectional atlas ((g:real->B->real^3^3) t) z u v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "sl" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2FL_DIST_MONO THEN EXISTS_TAC `a0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) x y` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sl" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &16 * sqrt(Q * Tm)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "kb" (MP_TAC o SPEC `a0:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0")) THEN
  MATCH_MP_TAC P2FL_EXP_LIMIT0 THEN
  MAP_EVERY EXISTS_TAC [`max K0 (&0)`; `s:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  (* d_t <= exp(2 K (0 - t)) d_0 *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `a0:real`; `&0`; `max K0 (&0)`; `t:real`; `x:B`; `y:B`]
                P2FL_DIST_NEAR_END) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= K ==> x <= max K (&0)`) THEN
      USE_THEN "K0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REAL_SUB_LZERO] THEN DISCH_TAC] THEN
  (* d_s <= d_t + 16 sqrt(Q Tm) *)
  SUBGOAL_THEN `mfd_dist (top,atlas) ((g:real->B->real^3^3) s) x y <=
                mfd_dist (top,atlas) (g t) x y + &16 * sqrt(Q * Tm)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) ((g:real->B->real^3^3) t) x y +
                real_integral (real_interval[s,t])
                  (\r. &8 * sqrt(&2 * (Q / (&2 * (r + Tm))) / &3))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REAL_ARITH `y <= z ==> x + y <= x + z`) THEN
      MATCH_MP_TAC P2FL_RATE_INTEGRAL THEN ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `ricci_flow_on (top,atlas) a0 (&0) (g:real->B->real^3^3) /\
                  (!r. a0 < r /\ r < &0 ==> mfd_complete (top,atlas) ((g:real->B->real^3^3) r)) /\
                  (\r. Q / (&2 * (r + Tm))) real_continuous_on real_interval[s,t] /\
                  (!r. s <= r /\ r <= t ==> &0 < Q / (&2 * (r + Tm)))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        USE_THEN "sl" (MP_TAC o SPEC `r:real`) THEN ANTS_TAC THENL
         [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MATCH_MP_TAC REAL_CONTINUOUS_ON_DIV THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; IN_REAL_INTERVAL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
          REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
          X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC];
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `!r z (v:real^3). s <= r /\ r <= t /\ z IN topspace top
                   ==> mfd_ricci atlas ((g:real->B->real^3^3) r) z v v <=
                       &2 * (Q / (&2 * (r + Tm))) * (v dot (g r z ** v))`
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [`r:real`; `z:B`; `v:real^3`] THEN STRIP_TAC THEN
      USE_THEN "sl" (MP_TAC o SPEC `r:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&0 < r + Tm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (v:real^3) dot ((g:real->B->real^3^3) r z ** v)` ASSUME_TAC THENL
       [MATCH_MP_TAC P2BX_QF_NONNEG THEN
        MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) r`; `z:B`; `v:real^3`] P2BFF_MFD_RICCI_ABS) THEN
      ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) r`; `z:B`] P2BX0_RM_NORM_LE_HALF_SCALAR) THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      USE_THEN "qb" (MP_TAC o SPECL [`r:real`; `z:B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) r) z <= Q / (r + Tm)`
      ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&2 * mfd_rm_norm atlas ((g:real->B->real^3^3) r) z *
                    ((v:real^3) dot (g r z ** v)) <=
                    (Q / (r + Tm)) * (v dot (g r z ** v))` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&2 * (Q / (&2 * (r + Tm))) * ((v:real^3) dot ((g:real->B->real^3^3) r z ** v)) =
                    (Q / (r + Tm)) * (v dot (g r z ** v))` ASSUME_TAC THENL
       [UNDISCH_TAC `&0 < r + Tm` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "dd" (MP_TAC o GEN_REWRITE_RULE I [P2C_REQ_DIST_DISTORTION_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                               `a0:real`; `&0`; `g:real->B->real^3^3`;
                               `\r. Q / (&2 * (r + Tm))`; `s:real`; `t:real`; `x:B`; `y:B`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) ((g:real->B->real^3^3) t) x y <=
               exp(&2 * max K0 (&0) * --t) * mfd_dist (top,atlas) (g (&0)) x y` THEN
  REAL_ARITH_TAC);;

