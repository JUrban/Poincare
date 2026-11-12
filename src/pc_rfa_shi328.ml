(* ========================================================================= *)
(* Unit pc_rfa_shi328: MT Thm 3.28 (Shi's local derivative estimates) on     *)
(* manifolds, P2_THM_3_28_STATEMENT.  For each order m, on shrinking regions *)
(* (b - tau / 2^m, b] x B_b(x, r_m), the bound comes from RFA_SLOC_STEP in   *)
(* the normal coordinates of g(t - tau / 2^(m+1)) at each centre             *)
(* (RFA_MFD_EXPSETUP, RFA_EXPFLOW_LRICCI, RFA_EXPFLOW_RMD), and at t = b by  *)
(* continuity of the chart extensions past b.                                *)
(* ========================================================================= *)

needs "src/pc_rfa_slmfd.ml";;
needs "src/pc_p3_iface.ml";;

prioritize_real();;
type_invention_error := true;;

(* Every chart representative of g(t), t in (a,b], extends smoothly to      *)
(* (a,b + e): the third conjunct of rfs_flow_upto, for any dimension.        *)

let rfa_ext = new_definition
 `rfa_ext (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (a:real) (b:real)
          (g:real->A->real^N^N) <=>
    !c. c IN atlas
        ==> ?e Fx. &0 < e /\
                   smooth_map_on
                     (interval(lift a,lift(b + e)) PCROSS IMAGE (SND c) (FST c)) Fx /\
                   !t y. a < t /\ t <= b /\ y IN IMAGE (SND c) (FST c)
                         ==> Fx(pastecart (lift t) y) =
                             (vectorize:real^N^N->real^(N,N)finite_prod)
                             (metric_local atlas c (g t) y)`;;

let RFA_RFS_FLOW_UPTO = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) a b g.
     rfs_flow_upto (top,atlas) a b g <=>
     ricci_flow_on (top,atlas) a b g /\ riemannian_metric atlas (g b) /\
     rfa_ext (top,atlas) a b g`,
  REWRITE_TAC[rfs_flow_upto; rfa_ext]);;

(* ========================================================================= *)
(* Bounds on |nabla^j Rm|^2 at times t < b pass to t = b when                *)
(* the chart representatives extend smoothly past b.                         *)
(* ========================================================================= *)

(* RFA_SYMM_EXT of pc_rfa_mfd with the time set given by a predicate. *)

let RFA_SYMM_EXT_P = prove
 (`!O V (P:real->bool) (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
     open O /\ smooth_map_on O FF /\
     (!t y. P t /\ y IN V ==> transp(Gc t y) = Gc t y) /\
     (!t y. P t /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y))
     ==> ?Fs. smooth_map_on O Fs /\
              (!w. transp(matrify(Fs w)) = matrify(Fs w):real^N^N) /\
              (!t y. P t /\ y IN V ==> Fs(pastecart (lift t) y) = vectorize(Gc t y))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(\m. vectorize(inv(&2) %% (matrify m + transp(matrify m)):real^N^N)) o
              (FF:real^(1,N)finite_sum->real^(N,N)finite_prod)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL;
                GSYM VECTORIZE_ADD; GSYM VECTORIZE_CMUL] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[o_THM; MATRIFY_VECTORIZE; TRANSP_MATRIX_CMUL;
                             TRANSP_MATRIX_ADD; TRANSP_TRANSP] THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC MATRIX_ADD_SYM;
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[o_THM; MATRIFY_VECTORIZE] THEN AP_TERM_TAC THEN
    REWRITE_TAC[CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC]);;

let RFA_UPTO_RMD_LIMIT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) y j C d.
     ricci_flow_on (top,atlas) a b g /\ riemannian_metric atlas (g b) /\
     rfa_ext (top,atlas) a b g /\ y IN topspace top /\ &0 < d /\
     (!t. b - d < t /\ t < b ==> rfa_rmd2 j atlas (g t) y <= C)
     ==> rfa_rmd2 j atlas (g b) y <= C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "ext") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_rmd2] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)` THEN
  ABBREV_TAC `V = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ABBREV_TAC `y0 = SND(c:(A->bool)#(A->real^N)) y` THEN
  SUBGOAL_THEN `(y0:real^N) IN V` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["y0"; "V"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ext" (fun th -> MP_TAC(MATCH_MP (REWRITE_RULE[rfa_ext] th)
    (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `O = interval(lift a,lift(b + e)) PCROSS (V:real^N->bool)` THEN
  SUBGOAL_THEN `open(O:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a < t /\ t <= b
        ==> metric_field V (metric_local atlas (c:(A->bool)#(A->real^N))
                                         ((g:real->A->real^N^N) t))`
  (LABEL_TAC "mf") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) t)` MP_TAC THENL
     [ASM_CASES_TAC `t:real = b` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `V:real^N->bool`;
                 `\t. a < t /\ t <= b`;
                 `\t. metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t)`;
                 `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`] RFA_SYMM_EXT_P) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `metric_field V (metric_local atlas (c:(A->bool)#(A->real^N))
                                     ((g:real->A->real^N^N) t))` MP_TAC THENL
       [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[metric_field] THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:real^(1,N)finite_sum->real^(N,N)finite_prod`
    (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  SUBGOAL_THEN `pastecart (lift b) (y0:real^N) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod)
              (pastecart (lift b) y0)):real^N^N =
    metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) b) y0`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(Fs:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift b) y0) =
      vectorize(metric_local atlas (c:(A->bool)#(A->real^N))
                             ((g:real->A->real^N^N) b) y0)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[MATRIFY_VECTORIZE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`;
                 `Fs:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `pastecart (lift b) (y0:real^N)`] RFA_LOCAL_LSMOOTH) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `metric_field V (metric_local atlas (c:(A->bool)#(A->real^N))
                                   ((g:real->A->real^N^N) b))` MP_TAC THENL
     [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[metric_field] THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Gx = \t (z:real^N). matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                            (pastecart (lift t) z)):real^N^N` THEN
  SUBGOAL_THEN `ball(y0:real^N,d1) SUBSET V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `interval(lift(b - d1),lift(b + d1)) PCROSS ball(y0:real^N,d1) SUBSET O` THEN
    EXPAND_TAC "O" THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    DISCH_THEN(MP_TAC o SPECL [`lift b`; `z:real^N`]) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a < t /\ t <= b /\ b - d1 < t
        ==> lrm_deriv_norm2 j (metric_local atlas (c:(A->bool)#(A->real^N))
                                 ((g:real->A->real^N^N) t)) y0 =
            lrm_deriv_norm2 j ((Gx:real->real^N->real^N^N) t) y0`
  (LABEL_TAC "same") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN EXISTS_TAC `ball(y0:real^N,d1)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "Gx" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(Fs:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) z) =
      vectorize(metric_local atlas (c:(A->bool)#(A->real^N))
                             ((g:real->A->real^N^N) t) z)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[MATRIFY_VECTORIZE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t. lrm_deriv_norm2 j ((Gx:real->real^N->real^N^N) t) y0) real_continuous atreal b`
  MP_TAC THENL
   [MP_TAC(ISPECL [`interval(lift(b - d1),lift(b + d1)) PCROSS ball(y0:real^N,d1)`;
                   `\z. lift(lrm_deriv_norm2 j ((Gx:real->real^N->real^N^N)
                                                  (drop(fstcart z))) (sndcart z))`;
                   `\x:real^1. x`; `y0:real^N`; `b:real`] RFA_TSLICE_CONTINUOUS) THEN
    REWRITE_TAC[LINEAR_ID; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
             LIFT_DROP; CENTRE_IN_BALL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC RFA_LSMOOTH_LRM_NORM2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
  USE_THEN "same" (MP_TAC o SPEC `b:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `(p ==> q) <=> (~q ==> ~p)`] THEN
  REWRITE_TAC[REAL_NOT_LE; NOT_FORALL_THM; NOT_IMP] THEN DISCH_TAC THEN
  EXISTS_TAC `lrm_deriv_norm2 j ((Gx:real->real^N->real^N^N) b) y0 - C` THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
  X_GEN_TAC `del:real` THEN
  ASM_CASES_TAC `&0 < del` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `b - min (min del d) (min d1 (b - a)) / &2` THEN
  SUBGOAL_THEN `&0 < min (min del d) (min d1 (b - a))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = b - min (min del d) (min d1 (b - a)) / &2` THEN
  USE_THEN "bd" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfa_rmd2] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "same" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* One order up on a manifold.  Bounds for j <= m on                         *)
(* (b - Tm, b] x B_b(x,r1) and |sec| <= K there give a bound for order m + 1  *)
(* on (b - Tm/2, b) x B_b(x,r2), r2 < r1: at t1, normal coordinates of        *)
(* g(t1 - Tm/2) at the centre and RFA_SLOC_STEP.                              *)
(* ========================================================================= *)

let RFA_MFD_SHI_STEP = prove
 (`!m K r1 r2 Tm C.
     &0 < K /\ &0 < r2 /\ r2 < r1 /\ &0 < Tm /\ &0 <= C
     ==> ?C'. !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
               (g:real->A->real^N^N) x Kc.
           hausdorff_space top /\ ricci_flow_on (top,atlas) a b g /\
           riemannian_metric atlas (g b) /\ rfa_ext (top,atlas) a b g /\
           Tm <= b - a /\ x IN topspace top /\ compact_in top Kc /\
           mfd_ball (top,atlas) (g b) x r1 SUBSET Kc /\
           (!t y. b - Tm < t /\ t <= b /\ y IN mfd_ball (top,atlas) (g b) x r1
                  ==> mfd_rm_norm atlas (g t) y <= K) /\
           (!j t y. j <= m /\ b - Tm < t /\ t <= b /\
                    y IN mfd_ball (top,atlas) (g b) x r1
                    ==> rfa_rmd2 j atlas (g t) y <= C)
           ==> !t y. b - Tm / &2 < t /\ t < b /\ y IN mfd_ball (top,atlas) (g b) x r2
                     ==> rfa_rmd2 (m + 1) atlas (g t) y <= C'`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Kr = &(dimindex(:N)) * sqrt C` THEN
  SUBGOAL_THEN `&0 <= Kr` ASSUME_TAC THENL
   [EXPAND_TAC "Kr" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `lam = exp(Kr * Tm)` THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `rho = min (inv(sqrt K)) ((r1 - r2) / lam)` THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= (r1 - r2) / lam /\ K * rho pow 2 <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(sqrt K) /\ &0 < (r1 - r2) / lam` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT; REAL_LT_DIV; REAL_SUB_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < rho /\ rho <= inv(sqrt K) /\ rho <= (r1 - r2) / lam`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `rho pow 2 <= inv K` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(sqrt K) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * inv K` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`(m:num) + 1`; `\i:num. (C:real)`; `K:real`; `rho:real`; `Tm / &2`]
         (INST_TYPE [`:N`,`:N`] RFA_SLOC_STEP)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C':real` (LABEL_TAC "loc")) THEN
  EXISTS_TAC `C':real` THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "sec") (LABEL_TAC "bds")))))))))) THEN
  MAP_EVERY X_GEN_TAC [`t1:real`; `y:A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  ABBREV_TAC `sg = t1 - Tm / &2` THEN
  SUBGOAL_THEN `a < sg /\ sg < b /\ b - Tm < sg /\ sg + Tm / &2 = t1 /\ sg <= b`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "sg" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) sg)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `R = mfd_ball (top,atlas) ((g:real->A->real^N^N) b) x r1` THEN
  SUBGOAL_THEN `open_in top (R:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:A. z IN R ==> z IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN
    UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) ((g:real->A->real^N^N) b) x r2` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. mfd_joinable (top,atlas) (y:A) z /\
        mfd_dist (top,atlas) ((g:real->A->real^N^N) b) y z < r1 - r2 ==> z IN R`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN STRIP_TAC THEN EXPAND_TAC "R" THEN
    UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) ((g:real->A->real^N^N) b) x r2` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) b`; `x:A`; `y:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z v. z IN R
          ==> v dot ((g:real->A->real^N^N) b z ** v) <=
              lam pow 2 * (v dot (g sg z ** v))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:A`; `v:real^N`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^N^N`; `z:A`; `sg:real`; `Kr:real`;
                   `v:real^N`] RFA_UPTO_QFORM_EQUIV) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GSYM rfa_ext] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      EXPAND_TAC "Kr" THEN MATCH_MP_TAC RFA_R1_RIC_BOUND THEN
      EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "bds" MATCH_MP_TAC THEN EXPAND_TAC "R" THEN
        ASM_REWRITE_TAC[LE_0] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [EXPAND_TAC "lam" THEN REWRITE_TAC[GSYM REAL_EXP_N] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      SUBGOAL_THEN `Kr * (b - sg) <= Kr * Tm` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(g:real->A->real^N^N) sg`; `z:A`] GEOD_TNORM_BASIC) THEN
      ASM_SIMP_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `v dot ((g:real->A->real^N^N) sg z ** v) =
                    mfd_tnorm (g sg) z v pow 2` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_LE_POW_2]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN R ==> mfd_rm_norm atlas ((g:real->A->real^N^N) sg) z <= K`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
    EXPAND_TAC "R" THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) sg`; `y:A`] RFA_FRAME_EXISTS) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) sg`; `(g:real->A->real^N^N) b`; `R:A->bool`;
                 `Kc:A->bool`; `y:A`; `r1 - r2:real`; `lam:real`; `K:real`; `rho:real`;
                 `E:real^N^N`] RFA_MFD_EXPSETUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXPAND_TAC "R" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:real->A->real^N^N`; `a:real`; `b:real`; `sg:real`; `y:A`;
                 `E:real^N^N`; `rho:real`] RFA_EXPFLOW_LRICCI) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  USE_THEN "loc" (MP_TAC o SPECL
   [`a:real`; `b:real`; `rfa_expflow (top,atlas) (g:real->A->real^N^N) sg y E`;
    `sg:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RFA_EXPFLOW_SG] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `s:real`; `w:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:real->A->real^N^N`; `a:real`; `b:real`; `sg:real`; `y:A`;
                   `E:real^N^N`; `rho:real`; `i:num`; `s:real`; `w:real^N`]
           RFA_EXPFLOW_RMD) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "bds" MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) y ((E:real^N^N) ** w) IN R`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "R" THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:real->A->real^N^N`; `a:real`; `b:real`; `sg:real`; `y:A`;
                 `E:real^N^N`; `rho:real`; `(m:num) + 1`; `t1:real`; `vec 0:real^N`]
         RFA_EXPFLOW_RMD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) sg`; `y:A`] MFD_EXP_DOM) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* All orders by induction, on the regions                                   *)
(* (b - tau / 2^m, b] x B_b(x, r/2 + r/2^(m+1)).                           *)
(* ========================================================================= *)

let RFA_MFD_BALL_MONO = prove
 (`!top atlas (g:A->real^N^N) x r s.
     r <= s ==> mfd_ball (top,atlas) g x r SUBSET mfd_ball (top,atlas) g x s`,
  REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RFA_DIV_LE_SELF = prove
 (`!x p. &0 <= x /\ &1 <= p ==> x / p <= x`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= p ==> &0 < p`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let RFA_MFD_SHI_ALL = prove
 (`!K r tau. &0 < K /\ &0 < r /\ &0 < tau
     ==> !m. ?C. &0 <= C /\
           !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
            (g:real->A->real^N^N) x Kc.
             hausdorff_space top /\ ricci_flow_on (top,atlas) a b g /\
             riemannian_metric atlas (g b) /\ rfa_ext (top,atlas) a b g /\
             tau <= b - a /\ x IN topspace top /\ compact_in top Kc /\
             mfd_ball (top,atlas) (g b) x r SUBSET Kc /\
             (!t y. a < t /\ t <= b /\ y IN mfd_ball (top,atlas) (g b) x r
                    ==> mfd_rm_norm atlas (g t) y <= K)
             ==> !j t y. j <= m /\ b - tau / &2 pow m < t /\ t <= b /\
                         y IN mfd_ball (top,atlas) (g b) x (r / &2 + r / &2 pow (m + 1))
                         ==> rfa_rmd2 j atlas (g t) y <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0"))
      (INST_TYPE [`:A`,`:A`; `:N`,`:N`] RFA_R1_RMD0) THEN
    EXISTS_TAC `C0 * K pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[LE; real_pow; REAL_DIV_1; ADD_CLAUSES; REAL_POW_1] THEN
    SUBGOAL_THEN `r / &2 + r / &2 = r` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `t:real`; `y:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "c0" MATCH_MP_TAC THEN
    EXISTS_TAC `top:A topology` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_CASES_TAC `t:real = b` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) ((g:real->A->real^N^N) b) x r` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `Cm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih"))) THEN
  SUBGOAL_THEN `&1 <= &2 pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_ADD; REAL_POW_1]) THEN
  REWRITE_TAC[real_pow; REAL_POW_ADD; REAL_POW_1] THEN
  ABBREV_TAC `p = &2 pow m` THEN
  SUBGOAL_THEN
   `r / ((&2 * p) * &2) = inv(&2) * (r / (p * &2)) /\
    tau / (&2 * p) = inv(&2) * (tau / p) /\
    &0 < r / (p * &2) /\ &0 < tau / p /\ r / (p * &2) <= r / &2 /\ tau / p <= tau`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `r / (p * &2) = (r / &2) / p` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC RFA_DIV_LE_SELF THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFA_DIV_LE_SELF THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `K:real`; `r / &2 + r / (p * &2)`;
                `r / &2 + r / ((&2 * p) * &2)`; `tau / p`; `Cm:real`]
         RFA_MFD_SHI_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C':real` (LABEL_TAC "step")) THEN
  EXISTS_TAC `max Cm (max C' (&0))` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `a:real`; `b:real`; `g:real->A->real^N^N`; `x:A`; `Kc:A->bool`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`j:num`; `t:real`; `y:A`] THEN STRIP_TAC THEN
  USE_THEN "ih" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `a:real`; `b:real`; `g:real->A->real^N^N`; `x:A`; `Kc:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "ihf")] THEN
  SUBGOAL_THEN
   `mfd_ball (top,atlas) ((g:real->A->real^N^N) b) x (r / &2 + r / ((&2 * p) * &2))
    SUBSET mfd_ball (top,atlas) (g b) x (r / &2 + r / (p * &2)) /\
    mfd_ball (top,atlas) (g b) x (r / &2 + r / (p * &2)) SUBSET
    mfd_ball (top,atlas) (g b) x r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_MFD_BALL_MONO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(j:num) <= m` THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= Cm ==> x <= max Cm (max C' (&0))`) THEN
    USE_THEN "ihf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:num) = m + 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= C' ==> x <= max Cm (max C' (&0))`) THEN
  SUBGOAL_THEN `tau / p <= b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) ((g:real->A->real^N^N) b) x (r / &2 + r / (p * &2))
                SUBSET Kc` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. b - tau / p < t /\ t <= b /\
          y IN mfd_ball (top,atlas) ((g:real->A->real^N^N) b) x (r / &2 + r / (p * &2))
          ==> mfd_rm_norm atlas (g t) y <= K`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "step" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `a:real`; `b:real`; `g:real->A->real^N^N`; `x:A`; `Kc:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "stepf")] THEN
  ASM_CASES_TAC `t:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC RFA_UPTO_RMD_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `(tau / p) / &2`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) ((g:real->A->real^N^N) b) x
                     (r / &2 + r / ((&2 * p) * &2))` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "stepf" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    USE_THEN "stepf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* P2_THM_3_28 (MT Thm 3.28, ball at the final time): the                    *)
(* dimension-3 instance of RFA_MFD_SHI_ALL at t = b on B_b(x, r/2), with    *)
(* the compact closure of B_b(x,r) as the compact set.                       *)
(* ========================================================================= *)

let RFA_P2_THM_3_28 = prove
 (`!u:A->bool. P2_THM_3_28_STATEMENT u`,
  REWRITE_TAC[P2_THM_3_28_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real`; `r:real`; `tau:real`]
    (INST_TYPE [`:A`,`:A`; `:3`,`:N`] RFA_MFD_SHI_ALL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `l:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "all"))) THEN
  EXISTS_TAC `C:real` THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `a:real`; `b:real`; `g:real->A->real^3^3`; `x:A`] THEN
  STRIP_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [RFA_RFS_FLOW_UPTO]) THEN
  USE_THEN "all" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `x:A`;
    `top closure_of mfd_ball (top,atlas) ((g:real->A->real^3^3) b) x r`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num`; `b:real`; `y:A`]) THEN
  REWRITE_TAC[rfa_rmd2] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[LE_REFL; REAL_LE_REFL] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `b - x < b <=> &0 < x`] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) ((g:real->A->real^3^3) b) x (r / &2)` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `r / &2` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LE_DIV THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE; REAL_POS]);;

