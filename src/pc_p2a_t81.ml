(* ========================================================================= *)
(* pc_p2a_t81: the route obligation O4 against the FIX forms                 *)
(* (P2A_ROUTE_8_1_FIX), MT Thm 8.1 through Prop 8.2 and Lemmas 8.3, 8.9, and *)
(* Thm 8.1 from the leaves (P2A_THM_8_1_FROM_LEAVES).  S is the set of       *)
(* initial vectors of minimizers ending in B; its reduced volume integral at *)
(* tau0 bounds V0 from above (area inequality), and at tau1 = eps r^2 it     *)
(* splits into a small part (injectivity, SMALLZ, slice volume comparison)   *)
(* and a Gaussian tail.                                                      *)
(*                                                                           *)
(* First: admissibility of L-geodesics, congruence of the L-length,          *)
(* minimizers give initial vectors in Smin, continuity of Lexp.              *)
(* ========================================================================= *)

needs "src/pc_p2a_defs3.ml";;
needs "src/pc_p2a_lgeo3.ml";;
needs "src/pc_p2a_reg.ml";;
needs "src/pc_p2a_minr.ml";;
needs "src/pc_p2a_inj.ml";;
needs "src/pc_p2a_usc.ml";;
needs "src/pc_grg_vol.ml";;
needs "src/pc_p2b_cap.ml";;
needs "src/pc_p2a_c712.ml";;

prioritize_real();;
type_invention_error := true;;

let P2A_T81_LGEOD_ADM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A).
     p2a_Lgeod V tt gamma b /\ gamma(&0) = x /\
     p2a_L_integrand V tt gamma b real_integrable_on real_interval[&0,b]
     ==> p2a_adm V tt x b gamma`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2a_adm] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2a_Lgeod]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `sqrt tau0`; `O:A->bool`] P2A_LGEOD_CONT) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e pow 2` THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sqrt tau`) THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(abs(tau - tau0))` THEN
    ASM_SIMP_TAC[REAL_ABS_LE_SQRT_POS] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(e pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    EXISTS_TAC `{}:real->bool` THEN MATCH_MP_TAC P2A_LGEOD_PC1 THEN ASM_REWRITE_TAC[]]);;

let P2A_T81_LGEO_ADM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b
     ==> p2a_adm V tt x b (p2a_Lgeo V tt x Z b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_T81_LGEOD_ADM THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LGEO_PROP) THEN REWRITE_TAC[p2a_Lgeod_from] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\(Z:real^N) s. p2a_lsint (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt
                     (p2a_Lgeo V tt x Z b) b s`; `&0`; `sqrt b`; `{Z:real^N}`]
                P2A_PARAM_REAL_INTEGRAL_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE; COMPACT_SING; LIFT_NUM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[vec 0,lift(sqrt b)] PCROSS
                p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) tt x b` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`] P2A_LSINT_JOINT) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; GEOL_IN_PCROSS; IN_SING] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Z:real^N` o CONJUNCT1) THEN
  REWRITE_TAC[IN_SING; ETA_AX] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`;
                 `p2a_Lgeo (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt x Z b`; `b:real`] P2A_L_LENGTH_SFORM) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[real_integrable_on]);;

let P2A_T81_LENGTH_CONG = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) gamma' b.
     (!tau. &0 <= tau /\ tau <= b ==> gamma tau = gamma' tau)
     ==> p2a_L_length V tt gamma b = p2a_L_length V tt gamma' b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_L_length] THEN
  MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{&0,b}` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_INSERT; REAL_NEGLIGIBLE_SING] THEN
  X_GEN_TAC `tau:real` THEN
  REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Every minimizer ending at q is represented by an initial vector in Smin.  *)

let P2A_T81_SMIN_OF_MIN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A).
     p2a_svs V /\ p2a_atlas_lc V /\ x IN topspace(p2a_vtop V tt) /\
     p2a_bsmooth V x tt /\ p2a_min V tt x b gamma
     ==> ?Z. Z IN p2a_Smin V tt x b /\ p2a_Lexp V tt x b Z = gamma b /\
             p2a_Ltil V tt x b Z = p2a_L_length V tt gamma b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`]
                P2A_MIN_LGEOD_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `Z:real^N` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min; p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt (p2a_Lgeo V tt x Z b) b =
    p2a_L_length V tt gamma b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_T81_LENGTH_CONG THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b Z = gamma b` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_Lexp] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2a_Smin; IN_ELIM_THM; p2a_Ltil] THEN
  REWRITE_TAC[p2a_min] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2A_T81_LGEO_ADM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `g':real->A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) tt x b gamma` THEN
  REWRITE_TAC[p2a_min] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(g':real->A) b = p2a_Lgeo (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x Z b b` THEN
  ASM_REWRITE_TAC[GSYM p2a_Lexp]);;

(* Continuity of the L-exponential map into the slice tt - b.               *)

let P2A_T81_LEXP_CONT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z0 O.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b /\ open_in (p2a_vtop V (tt - b)) O /\
     p2a_Lexp V tt x b Z0 IN O
     ==> ?e. &0 < e /\
             !Z. dist(Z,Z0) < e ==> Z IN p2a_Ldom V tt x b /\ p2a_Lexp V tt x b Z IN O`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`]
                P2A_LEXP_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum`
      STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`;
                 `tt - b`; `O:A->bool`] P2A_REGION_OPEN_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`;
                 `b':real`] P2A_REGION_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER W INTER O))` ASSUME_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) b'`;
      `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) b'`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN
    SUBGOAL_THEN `U INTER W INTER O = U INTER ((W:A->bool) INTER O)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN `(fstcart o (Phi:real^N->real^(N,N)finite_sum)) continuous at Z0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`fstcart o (Phi:real^N->real^(N,N)finite_sum)`; `N:real^N->bool`]
                  CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS; SMOOTH_MAP_ON_FSTCART_OPEN];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b Z0 IN U INTER W /\
                (phi:A->real^N) (p2a_Lexp V tt x b Z0) =
                fstcart((Phi:real^N->real^(N,N)finite_sum) Z0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(fstcart o (Phi:real^N->real^(N,N)finite_sum)) Z0 IN
                IMAGE (phi:A->real^N) (U INTER W INTER O)` ASSUME_TAC THENL
   [REWRITE_TAC[o_THM; IN_IMAGE] THEN
    EXISTS_TAC `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b Z0` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `open(IMAGE (phi:A->real^N) (U INTER W INTER O))` THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(fstcart o (Phi:real^N->real^(N,N)finite_sum)) Z0`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bl"))) THEN
  UNDISCH_TAC `(fstcart o (Phi:real^N->real^(N,N)finite_sum)) continuous at Z0` THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e1:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ct"))) THEN
  UNDISCH_TAC `open(N:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `Z0:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bn"))) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `Z:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Z:real^N) IN N` ASSUME_TAC THENL
   [USE_THEN "bn" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(fstcart o (Phi:real^N->real^(N,N)finite_sum)) Z IN
                IMAGE (phi:A->real^N) (U INTER W INTER O)` MP_TAC THENL
   [USE_THEN "bl" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    USE_THEN "ct" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; o_THM; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b Z IN U INTER W /\
                (phi:A->real^N) (p2a_Lexp V tt x b Z) =
                fstcart((Phi:real^N->real^(N,N)finite_sum) Z)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b'`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b'`; `U:A->bool`; `phi:A->real^N`]
                CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `y:A` th) THEN
    MP_TAC(SPEC `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b Z` th)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Smin is relatively closed in the open set Ldom (upper semicontinuity of   *)
(* Lx with continuity of Ltil and Lexp), so the set S of initial vectors of  *)
(* minimizers ending in an open B is Lebesgue measurable.                    *)
(* ------------------------------------------------------------------------- *)

let P2A_T81_LE_EPS = prove
 (`!a b. (!e. &0 < e ==> a <= b + e) ==> a <= b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a - b) / &2`) THEN ASM_REAL_ARITH_TAC);;

let P2A_T81_SMIN_CLOSED = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z0.
     p2a_svs V /\ p2a_atlas_lc V /\ x IN topspace(p2a_vtop V tt) /\
     p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b /\ Z0 IN closure(p2a_Smin V tt x b)
     ==> Z0 IN p2a_Smin V tt x b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [UNDISCH_TAC `(Z0:real^N) IN p2a_Ldom (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b` THEN
    REWRITE_TAC[p2a_Ldom; IN_ELIM_THM; p2a_Lgeod_from; p2a_Lgeod] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_Smin; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p2a_min] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2A_T81_LGEO_ADM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `g':real->A` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2A_T81_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `g':real->A`;
                 `e / &2`] P2A_LX_USC_GEN) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "usc")))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`;
                 `O:A->bool`] P2A_T81_LEXP_CONT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[p2a_Lexp] THEN
    UNDISCH_TAC `(g':real->A) b IN O` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lx"))) THEN
  SUBGOAL_THEN `&0 < &2 * sqrt b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`] P2A_LTIL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `Z0:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &2 / (&2 * sqrt b)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lt"))) THEN
  UNDISCH_TAC `(Z0:real^N) IN closure(p2a_Smin (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b)` THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `min d1 d2`) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z:real^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "lx" (MP_TAC o SPEC `Z:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "usc" (MP_TAC o SPEC `p2a_Lexp (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b Z`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g'':real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt (p2a_Lgeo V tt x Z b) b <=
    p2a_L_length V tt g'' b` ASSUME_TAC THENL
   [UNDISCH_TAC `(Z:real^N) IN p2a_Smin (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b` THEN
    REWRITE_TAC[p2a_Smin; IN_ELIM_THM; p2a_min] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    UNDISCH_TAC `p2a_adm1 (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                   (real->A->real^N^N)) tt x b g''` THEN
    SIMP_TAC[p2a_adm1] THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM p2a_Lexp];
    ALL_TAC] THEN
  USE_THEN "lt" (MP_TAC o SPEC `Z:real^N`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[p2a_Smin; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[DIST_LIFT; p2a_ltil; p2a_Ltil] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < c ==> a / c - d / c = (a - d) / c`; REAL_ABS_DIV;
               REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_DIV2_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let P2A_T81_S_MEASURABLE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b B.
     p2a_svs V /\ p2a_atlas_lc V /\ x IN topspace(p2a_vtop V tt) /\
     p2a_bsmooth V x tt /\ open_in (p2a_vtop V (tt - b)) B
     ==> lebesgue_measurable {Z | Z IN p2a_Smin V tt x b /\ p2a_Lexp V tt x b Z IN B}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{Z | Z IN p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) tt x b /\ p2a_Lexp V tt x b Z IN B} =
    {Z | Z IN p2a_Ldom V tt x b /\ p2a_Lexp V tt x b Z IN B} INTER
    closure(p2a_Smin V tt x b)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `Z:real^N` THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[p2a_Smin; IN_ELIM_THM];
        MP_TAC(ISPEC `p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) tt x b` CLOSURE_SUBSET) THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC P2A_T81_SMIN_CLOSED THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN
  SIMP_TAC[LEBESGUE_MEASURABLE_CLOSED; CLOSED_CLOSURE] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL; IN_ELIM_THM] THEN
  X_GEN_TAC `Z0:real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`;
                 `B:A->bool`] P2A_T81_LEXP_CONT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Gaussian 8 exp(-|Z|^2) on real^3, its linear changes of variables Z   *)
(* -> A Z (for the metric G = A^T A at x), and the density at x.             *)
(* ------------------------------------------------------------------------- *)

let P2A_T81_GAUSS_CONT = prove
 (`!(G:real^3^3) s. (\Z:real^3. lift(&8 * exp(--(Z dot (G ** Z))))) continuous_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `Z0:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_CMUL THEN
  SUBGOAL_THEN `(\Z:real^3. lift(exp(--(Z dot (G ** Z))))) =
                (lift o exp o drop) o (\Z. --(lift(Z dot (G ** Z))))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_NEG; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_NEG THEN MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN
    SIMP_TAC[CONTINUOUS_AT_ID; LINEAR_CONTINUOUS_AT; MATRIX_VECTOR_MUL_LINEAR];
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL; REAL_CONTINUOUS_AT_EXP]]);;

let P2A_T81_GAUSS_UNIV = prove
 (`P2A_GAUSS_TAIL_STATEMENT
   ==> (\Z:real^3. lift(&8 * exp(--(Z dot Z)))) absolutely_integrable_on (:real^3)`,
  REWRITE_TAC[P2A_GAUSS_TAIL_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `eps0:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(:real^3) = {Z | &1 <= &64 * eps0 * (Z dot Z)} UNION
                            {Z | &64 * eps0 * (Z dot Z) <= &1}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV; IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_UNION THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bounded {Z:real^3 | &64 * eps0 * (Z dot Z) <= &1}` MP_TAC THENL
   [REWRITE_TAC[bounded; IN_ELIM_THM] THEN EXISTS_TAC `&1 + inv(&64 * eps0)` THEN
    X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Z:real^3) dot Z <= inv(&64 * eps0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `inv x = &1 / x`; REAL_LE_RDIV_EQ; REAL_LT_MUL;
                   REAL_OF_NUM_LT; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `Z:real^3` NORM_POW_2) THEN MP_TAC(ISPEC `Z:real^3` NORM_POS_LE) THEN
    SPEC_TAC(`norm(Z:real^3)`,`n:real`) THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `n <= &1` THENL
     [MP_TAC(SPEC `&64 * eps0` REAL_LE_INV) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `n <= n pow 2` MP_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` ASSUME_TAC)) THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `interval[a:real^3,b]` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
    MP_TAC(ISPECL [`mat 1:real^3^3`; `interval[a:real^3,b]`] P2A_T81_GAUSS_CONT) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LID];
    MATCH_MP_TAC LEBESGUE_MEASURABLE_CLOSED THEN
    SUBGOAL_THEN `{Z:real^3 | &64 * eps0 * (Z dot Z) <= &1} =
                  {Z | (\Z. lift(&64 * eps0 * (Z dot Z))) Z IN {y | drop y <= &1}}`
    SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
    REWRITE_TAC[drop; CLOSED_HALFSPACE_COMPONENT_LE] THEN
    GEN_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_CMUL) THEN
    MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN REWRITE_TAC[CONTINUOUS_AT_ID]]);;

let P2A_T81_DOT_COV = prove
 (`!(A:real^N^N) Z. (A ** Z) dot (A ** Z) = Z dot ((transp A ** A) ** Z)`,
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

let P2A_T81_GAUSS_LINEAR = prove
 (`!(A:real^3^3) s.
     invertible A /\
     (\Z:real^3. lift(&8 * exp(--(Z dot Z)))) absolutely_integrable_on
       IMAGE (\Z. A ** Z) s
     ==> (\Z. lift(&8 * exp(--(Z dot ((transp A ** A) ** Z)))))
           absolutely_integrable_on s /\
         integral (IMAGE (\Z. A ** Z) s) (\Z:real^3. lift(&8 * exp(--(Z dot Z)))) =
         abs(det A) % integral s (\Z. lift(&8 * exp(--(Z dot ((transp A ** A) ** Z)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\Z:real^3. lift(&8 * exp(--(Z dot Z)))) o (\Z. (A:real^3^3) ** Z) =
                (\Z. lift(&8 * exp(--(Z dot ((transp A ** A) ** Z)))))` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; P2A_T81_DOT_COV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\Z:real^3. lift(&8 * exp(--(Z dot Z)))`; `\Z. (A:real^3^3) ** Z`;
                 `s:real^3->bool`] ABSOLUTELY_INTEGRABLE_ON_LINEAR_IMAGE) THEN
  MP_TAC(ISPECL [`\Z:real^3. lift(&8 * exp(--(Z dot Z)))`; `\Z. (A:real^3^3) ** Z`;
                 `s:real^3->bool`] INTEGRAL_CHANGE_OF_VARIABLES_LINEAR) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [INVERTIBLE_DET_NZ]) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let P2A_T81_IMAGE_COV = prove
 (`!(A:real^3^3) P.
     invertible A
     ==> IMAGE (\Z. A ** Z) {Z | P(Z dot ((transp A ** A) ** Z))} = {W | P(W dot W)}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `W:real^3` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `Z:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[P2A_T81_DOT_COV];
    DISCH_TAC THEN EXISTS_TAC `matrix_inv(A:real^3^3) ** W` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID;
                    GSYM P2A_T81_DOT_COV]]);;

(* The metric at x is A^T A for an invertible A, and the density at x is   *)
(* abs(det A) > 0.                                                          *)

let P2A_T81_DENS_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt)
     ==> ?A:real^N^N. invertible A /\ p2a_vmetric V tt x = transp A ** A /\
                      p2a_zdens V tt x = abs(det A) /\ &0 < abs(det A)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt)
                  (p2a_vatlas V tt) /\
                riemannian_metric (p2a_vatlas V tt) (p2a_vmetric V tt)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                   (real->A->real^N^N))` THEN
    REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o SPEC `tt:real`) THEN
    MATCH_MP_TAC(TAUT `p ==> (q /\ (p ==> r) ==> r)`) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) tt`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) tt`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`; `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`; `x:A`]
                METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `positive_definite(p2a_vmetric (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x)`
  MP_TAC THENL
   [UNDISCH_TAC `riemannian_metric (p2a_vatlas (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt)
                   (p2a_vmetric V tt)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `chart_at (p2a_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) x`) THEN
    ASM_REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `SND(chart_at (p2a_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) x) x` o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    REWRITE_TAC[positive_definite; symmetric_matrix] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[POSITIVE_DEFINITE_COVARIANCE_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  EXISTS_TAC `A:real^N^N` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [INVERTIBLE_DET_NZ]) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < abs x <=> ~(x = &0)`] THEN
  REWRITE_TAC[p2a_zdens; mfd_density] THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[DET_MUL; DET_TRANSP; GSYM REAL_POW_2; POW_2_SQRT_ABS]);;

(* ------------------------------------------------------------------------- *)
(* Rvi below the Gaussian on Smin (RVI_MONO and RVI_ASYMP), J in terms of    *)
(* rvi, and the area formula (P2A_REQ_AREA_STATEMENT) for Lexp.              *)
(* ------------------------------------------------------------------------- *)

let P2A_T81_RVI_GAUSS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x b Z b1.
     P2A_RVI_MONO_STATEMENT (u:A->bool) /\ P2A_RVI_ASYMP_STATEMENT u /\
     p2a_svs V /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Smin V tt x b /\ &0 < b1 /\ b1 <= b
     ==> p2a_rvi V tt x b1 Z <= &8 * exp(--(p2a_znorm2 V tt x Z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2A_RVI_MONO_STATEMENT; P2A_RVI_ASYMP_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mono") (CONJUNCTS_THEN2 (LABEL_TAC "asy")
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  USE_THEN "asy" (MP_TAC o SPECL
    [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `tt:real`; `x:A`; `Z:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC
    `(p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
               (real->A->real^3^3)) tt x b1 Z - &8 * exp(--(p2a_znorm2 V tt x Z))) / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min d b1 / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "mono" (MP_TAC o SPECL
    [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `tt:real`; `x:A`; `b:real`; `Z:real^3`; `min d b1 / &2`; `b1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2A_T81_J_RVI = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z.
     &0 < b
     ==> p2a_J V tt x b Z =
         exp(p2a_ltil V tt x b Z) * sqrt b pow dimindex(:N) * p2a_rvi V tt x b Z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_rvi] THEN
  SUBGOAL_THEN `&0 < sqrt b pow dimindex(:N)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; SQRT_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `p2a_ltil (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                 (real->A->real^N^N)) tt x b Z` REAL_EXP_NEG_MUL) THEN
  SPEC_TAC(`sqrt b pow dimindex(:N)`,`q:real`) THEN
  SPEC_TAC(`exp(p2a_ltil (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                 (real->A->real^N^N)) tt x b Z)`,`e1:real`) THEN
  SPEC_TAC(`exp(--p2a_ltil (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                 (real->A->real^N^N)) tt x b Z)`,`e2:real`) THEN
  CONV_TAC REAL_FIELD);;

(* The area formula for Lexp at time tt - b on a measurable S in Ldom.      *)

let P2A_T81_AREA_APPLY = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x b S.
     P2A_REQ_AREA_STATEMENT (u:A->bool) /\
     p2a_svs V /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt /\
     lebesgue_measurable S /\ S SUBSET p2a_Ldom V tt x b /\ ~(S = {}) /\
     (\Z. lift(p2a_J V tt x b Z)) integrable_on S
     ==> ?v. mfd_has_volume (rfs_vtop V (tt - b),rfs_vatlas V (tt - b))
                            (rfs_vmetric V (tt - b)) (IMAGE (p2a_Lexp V tt x b) S) v /\
             v <= p2a_zdens V tt x * drop(integral S (\Z. lift(p2a_J V tt x b Z))) /\
             ((!Z Z'. Z IN S /\ Z' IN S /\ p2a_Lexp V tt x b Z = p2a_Lexp V tt x b Z'
                      ==> Z = Z')
              ==> v = p2a_zdens V tt x * drop(integral S (\Z. lift(p2a_J V tt x b Z))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM P2A_VIEW_PROJ_3] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?Z0:real^3. Z0 IN S` STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^3. Z IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b
                  ==> &0 < b /\ p2a_Lexp V tt x b Z IN topspace(p2a_vtop V (tt - b))`
  ASSUME_TAC THENL
   [X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LGEO_PROP) THEN
    REWRITE_TAC[p2a_Lgeod_from; p2a_Lgeod; p2a_Lexp] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - b)) (p2a_vatlas V (tt - b)) /\
                riemannian_metric (p2a_vatlas V (tt - b)) (p2a_vmetric V (tt - b))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN REWRITE_TAC[p2a_svs] THEN
    DISCH_THEN(MP_TAC o SPEC `tt - b`) THEN
    MATCH_MP_TAC(TAUT `p ==> (q /\ (p ==> r) ==> r)`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b Z0` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2A_T81_DENS_X) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(\Z:real^3. lift(abs(det(matrix(frechet_derivative
        (\W. SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - b)) (p2a_Lexp V tt x b Z))
                (p2a_Lexp V tt x b W)) (at Z)))) *
        mfd_density (p2a_vatlas V (tt - b))
          (chart_at (p2a_vatlas V (tt - b)) (p2a_Lexp V tt x b Z))
          (p2a_vmetric V (tt - b))
          (SND(chart_at (p2a_vatlas V (tt - b)) (p2a_Lexp V tt x b Z))
              (p2a_Lexp V tt x b Z)))) =
    (\Z. p2a_zdens V tt x % lift(p2a_J V tt x b Z))` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; LIFT_EQ] THEN X_GEN_TAC `Z:real^3` THEN
    REWRITE_TAC[p2a_J; GSYM p2a_zdens] THEN
    UNDISCH_TAC `&0 < abs(det(A0:real^3^3))` THEN
    UNDISCH_TAC `p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x = abs(det(A0:real^3^3))` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  UNDISCH_TAC `P2A_REQ_AREA_STATEMENT (u:A->bool)` THEN
  REWRITE_TAC[P2A_REQ_AREA_STATEMENT] THEN
  DISCH_THEN(MP_TAC o ISPECL
   [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - b)`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - b)`; `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - b)`;
    `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b`;
    `\Z:real^3. frechet_derivative
        (\W. SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - b)) (p2a_Lexp V tt x b Z))
                (p2a_Lexp V tt x b W)) (at Z)`;
    `S:real^3->bool`]) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
      REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `O:A->bool` THEN DISCH_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
      EXISTS_TAC `{Z | Z IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b /\ p2a_Lexp V tt x b Z IN O}` THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      REWRITE_TAC[OPEN_CONTAINS_BALL; IN_ELIM_THM] THEN
      X_GEN_TAC `Z1:real^3` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `tt:real`; `x:A`; `b:real`; `Z1:real^3`;
                     `O:A->bool`] P2A_T81_LEXP_CONT) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[];
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC P2A_LEXP_DIFFERENTIABLE THEN ASM SET_TAC[];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* Comparison of slice volumes inside a region from a comparison of the      *)
(* region metrics (P2BC_VOLUME_PB_COMPARE of pc_p2b_cap, with the identity   *)
(* diffeomorphism of the region).                                            *)
(* ------------------------------------------------------------------------- *)

let P2A_T81_RESTRICT_METRIC_FORM = prove
 (`!top atlas (W:A->bool) y.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     open_in top W /\ y IN W
     ==> ?J:real^N^N. invertible J /\
                      !h:A->real^N^N. restrict_metric atlas W h y = transp J ** h y ** J`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `y:A`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (W:A->bool)`)) THEN ASM SET_TAC[];
    STRIP_TAC] THEN
  EXISTS_TAC `matrix(chart_jac (U:A->bool,phi:A->real^N) (chart_at atlas y) y)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U:A->bool,phi:A->real^N)`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) y`;
                   `y:A`] GRGE_CHART_JAC_INVERTIBLE) THEN
    ASM_REWRITE_TAC[FST] THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `h:A->real^N^N` THEN
  ASM_REWRITE_TAC[restrict_metric; metric_local; SND] THEN
  SUBGOAL_THEN `chart_inv (U INTER W:A->bool,phi:A->real^N) (phi y) = y` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`; `W:A->bool`] MFDR_CHART_INV_RESTRICT) THEN
    DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `W:A->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) y`; `y:A`]
                MFDR_CHART_JAC_RESTRICT_L) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let P2A_T81_QF_TRANSFER = prove
 (`!(J:real^N^N) (A:real^N^N) B lam.
     invertible J /\
     (!w. w dot ((transp J ** A ** J) ** w) <= lam * (w dot ((transp J ** B ** J) ** w)))
     ==> !v. v dot (A ** v) <= lam * (v dot (B ** v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BC_QF_CONG] THEN STRIP_TAC THEN
  X_GEN_TAC `v:real^N` THEN FIRST_X_ASSUM(MP_TAC o SPEC `matrix_inv(J:real^N^N) ** v`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  SUBGOAL_THEN `(J:real^N^N) ** (matrix_inv J ** v) = v` (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]);;

let P2A_T81_SLICE_VOLCMP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s S v v' lam.
     p2a_svs V /\ p2a_region V W a b /\ a < s /\ s < b /\ S SUBSET W /\ ~(S = {}) /\
     &0 <= lam /\
     mfd_has_volume (p2a_vtop V b,p2a_vatlas V b) (p2a_vmetric V b) S v /\
     mfd_has_volume (p2a_vtop V s,p2a_vatlas V s) (p2a_vmetric V s) S v' /\
     (!y w. y IN S
            ==> w dot (p2a_rmetric V W b s y ** w) <=
                lam * (w dot (p2a_rmetric V W b b y ** w)))
     ==> v' <= lam * sqrt lam * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `s:real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `?y0:A. y0 IN S` STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) = {}) /\ ~(topspace(p2a_vtop V s) = {})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)`)) THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (W:A->bool)`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (p2a_vmetric V b) /\
                riemannian_metric (p2a_vatlas V s) (p2a_vmetric V s)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_svs]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
                 `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`; `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                 `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`; `S:A->bool`;
                 `v:real`; `v':real`; `lam:real`] P2BC_VOLUME_PB_COMPARE) THEN
  ASM_REWRITE_TAC[IMAGE_ID] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `W:A->bool`; `y:A`]
                P2A_T81_RESTRICT_METRIC_FORM) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!w':real^3. w' dot ((transp J ** mfd_pullback_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (p2a_vatlas V s)
                                       (\y:A. y) (p2a_vmetric V s) y ** J) ** w') <=
                lam * (w' dot ((transp J ** p2a_vmetric V b y ** J) ** w'))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w':real^3` THEN
    SUBGOAL_THEN `~(s:real = b)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `w':real^3`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_rmetric")) (concl th))) THEN
    ASM_REWRITE_TAC[p2a_rmetric];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J:real^3^3`;
                 `mfd_pullback_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (p2a_vatlas V s) (\y:A. y)
                    (p2a_vmetric V s) y`;
                 `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b y`; `lam:real`] P2A_T81_QF_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integrability of rvi and J on subsets of Smin (domination by the          *)
(* Gaussian), and the small part: by injectivity of Lexp at b1 < b and the   *)
(* area formula, the rvi integral at b1 over a set mapped into K with ltil   *)
(* >= -e0 is at most exp e0 b1^(-3/2) Vol K (truncation of J and dominated   *)
(* convergence).                                                             *)
(* ------------------------------------------------------------------------- *)

let P2A_T81_SMIN_LDOM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b b1 Z.
     p2a_svs V /\ Z IN p2a_Smin V tt x b /\ &0 < b1 /\ b1 <= b
     ==> Z IN p2a_Ldom V tt x b1`,
  REWRITE_TAC[p2a_Smin; IN_ELIM_THM] THEN MESON_TAC[P2A_LDOM_RESTRICT]);;

let P2A_T81_LEXP_TOPSPACE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z.
     Z IN p2a_Ldom V tt x b
     ==> &0 < b /\ p2a_Lexp V tt x b Z IN topspace(p2a_vtop V (tt - b))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LGEO_PROP) THEN
  REWRITE_TAC[p2a_Lgeod_from; p2a_Lgeod; p2a_Lexp] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2A_T81_J_NONNEG = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ Z IN p2a_Ldom V tt x b
     ==> &0 <= p2a_J V tt x b Z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_T81_LEXP_TOPSPACE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`] P2A_T81_DENS_X) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt - b`;
                 `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) tt x b Z`] P2A_T81_DENS_X) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real^N^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:real^N^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[p2a_J; GSYM p2a_zdens] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS]);;

let P2A_T81_RVI_NONNEG = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ Z IN p2a_Ldom V tt x b
     ==> &0 <= p2a_rvi V tt x b Z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_rvi] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_T81_LEXP_TOPSPACE) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE; SQRT_POS_LE; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC P2A_T81_J_NONNEG THEN ASM_REWRITE_TAC[]);;

let P2A_T81_MUL_LE_AUX = prove
 (`!a e j i. &0 <= j * i /\ a <= e ==> a * (j * i) <= (e * i) * j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e * i) * j = e * (j * i)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* The Gaussian of the metric at x is integrable on real^3.                  *)

let P2A_T81_GAUSS_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x.
     P2A_GAUSS_TAIL_STATEMENT /\ p2a_svs V /\ x IN topspace(p2a_vtop V tt)
     ==> (\Z. lift(&8 * exp(--(p2a_znorm2 V tt x Z)))) absolutely_integrable_on (:real^3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2A_T81_DENS_X) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `A:real^3^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[p2a_znorm2] THEN
  MP_TAC(ISPECL [`A:real^3^3`; `(:real^3)`] P2A_T81_GAUSS_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (\Z. (A:real^3^3) ** Z) (:real^3) = (:real^3)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`A:real^3^3`; `\t:real. T`] P2A_T81_IMAGE_COV) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[SET_RULE `{x:real^3 | T} = UNIV`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2A_T81_GAUSS_UNIV]);;

let P2A_T81_RVI_INTEGRABLE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x b b1 S.
     P2A_RVI_MONO_STATEMENT (u:A->bool) /\ P2A_RVI_ASYMP_STATEMENT u /\
     P2A_GAUSS_TAIL_STATEMENT /\
     p2a_svs V /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt /\
     lebesgue_measurable S /\ S SUBSET p2a_Smin V tt x b /\ &0 < b1 /\ b1 <= b
     ==> (\Z. lift(p2a_rvi V tt x b1 Z)) absolutely_integrable_on S`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\Z. lift(&8 * exp(--(p2a_znorm2 (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x Z)))` THEN
  SUBGOAL_THEN `!Z:real^3. Z IN S ==> Z IN p2a_Ldom (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_T81_SMIN_LDOM THEN EXISTS_TAC `b:real` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) tt x b1` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC P2A_RVI_CONTINUOUS THEN
    ASM_REWRITE_TAC[P2A_VIEW_PROJ_3];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC P2A_T81_GAUSS_X THEN ASM_REWRITE_TAC[P2A_VIEW_PROJ_3];
    X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
    SUBGOAL_THEN `&0 <= p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) tt x b1 Z` ASSUME_TAC THENL
     [MATCH_MP_TAC P2A_T81_RVI_NONNEG THEN ASM_SIMP_TAC[P2A_VIEW_PROJ_3]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC P2A_T81_RVI_GAUSS THEN EXISTS_TAC `b:real` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* The bounded measurable truncations {Z in S | J Z <= M}.                   *)

let P2A_T81_TRUNC_MEASURABLE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b S M.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     lebesgue_measurable S /\ S SUBSET p2a_Ldom V tt x b
     ==> lebesgue_measurable {Z | Z IN S /\ p2a_J V tt x b Z <= M}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{Z | Z IN S /\ p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) tt x b Z <= M} =
    S DIFF {Z | Z IN p2a_Ldom V tt x b /\ (\Z. lift(p2a_J V tt x b Z)) Z IN
                                           {y:real^1 | y$1 > M}}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; GSYM drop; LIFT_DROP] THEN
    REWRITE_TAC[real_gt; DE_MORGAN_THM; REAL_NOT_LT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
  ASM_SIMP_TAC[P2A_J_CONTINUOUS; P2A_LDOM_OPEN]);;

let P2A_T81_BOUNDED_MEASURABLE = prove
 (`!s:real^N->bool. lebesgue_measurable s /\ bounded s ==> measurable s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` ASSUME_TAC)) THEN
  MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `interval[a:real^N,b]` THEN ASM_REWRITE_TAC[MEASURABLE_INTERVAL]);;

let P2A_T81_SMALL_TRUNC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x b b1 S K e0 Q M.
     P2A_REQ_AREA_STATEMENT (u:A->bool) /\
     p2a_svs V /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt /\
     lebesgue_measurable S /\ bounded S /\ S SUBSET p2a_Smin V tt x b /\
     &0 < b1 /\ b1 <= b /\
     (!Z Z'. Z IN S /\ Z' IN S /\ p2a_Lexp V tt x b1 Z = p2a_Lexp V tt x b1 Z'
             ==> Z = Z') /\
     (!Z. Z IN S ==> p2a_Lexp V tt x b1 Z IN K /\ --e0 <= p2a_ltil V tt x b1 Z) /\
     mfd_has_volume (rfs_vtop V (tt - b1),rfs_vatlas V (tt - b1)) (rfs_vmetric V (tt - b1))
                    K Q /\
     &0 <= Q /\ (\Z. lift(p2a_rvi V tt x b1 Z)) absolutely_integrable_on S
     ==> p2a_zdens V tt x *
         drop(integral {Z | Z IN S /\ p2a_J V tt x b1 Z <= &M}
                       (\Z. lift(p2a_rvi V tt x b1 Z))) <=
         exp e0 * inv(sqrt b1 pow 3) * Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!Z:real^3. Z IN S ==> Z IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_T81_SMIN_LDOM THEN EXISTS_TAC `b:real` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt b1 pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `x:A`] P2A_T81_DENS_X) THEN
    ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable {Z | Z IN S /\ p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z <= &M}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_T81_TRUNC_MEASURABLE THEN
    ASM_REWRITE_TAC[GSYM P2A_VIEW_PROJ_3] THEN
    ASM_REWRITE_TAC[P2A_VIEW_PROJ_3; SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{Z | Z IN S /\ p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z <= &M} SUBSET S` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `measurable {Z | Z IN S /\ p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z <= &M}` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_T81_BOUNDED_MEASURABLE THEN ASM_MESON_TAC[BOUNDED_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\Z. lift(p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z)) absolutely_integrable_on
                {Z | Z IN S /\ p2a_J V tt x b1 Z <= &M}` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\Z:real^3. lift(&M)` THEN ASM_REWRITE_TAC[INTEGRABLE_ON_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1` THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC P2A_J_CONTINUOUS THEN ASM_REWRITE_TAC[P2A_VIEW_PROJ_3];
      REWRITE_TAC[IN_ELIM_THM; NORM_LIFT; LIFT_DROP] THEN
      X_GEN_TAC `Z:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z` MP_TAC THENL
       [MATCH_MP_TAC P2A_T81_J_NONNEG THEN ASM_SIMP_TAC[P2A_VIEW_PROJ_3];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x * drop(integral {Z | Z IN S /\ p2a_J V tt x b1 Z <= &M}
                                       (\Z. lift(p2a_J V tt x b1 Z))) <= Q`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `{Z | Z IN S /\ p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z <= &M} = {}` THENL
     [ASM_REWRITE_TAC[INTEGRAL_EMPTY; DROP_VEC; REAL_MUL_RZERO]; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `x:A`; `b1:real`;
                   `{Z | Z IN S /\ p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z <= &M}`] P2A_T81_AREA_APPLY) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    ANTS_TAC THENL [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `v = p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x *
                      drop(integral {Z | Z IN S /\ p2a_J V tt x b1 Z <= &M}
                                    (\Z. lift(p2a_J V tt x b1 Z)))` (SUBST1_TAC o SYM) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - b1)) (rfs_vatlas V (tt - b1)) /\
                  riemannian_metric (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - b1)) (rfs_vmetric V (tt - b1))`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `Z1:real^3` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `tt:real`; `x:A`; `b1:real`; `Z1:real^3`]
                    P2A_T81_LEXP_TOPSPACE) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[P2A_VIEW_PROJ_3] THEN STRIP_TAC THEN
      UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN
      DISCH_THEN(MP_TAC o SPEC `tt - b1`) THEN
      MATCH_MP_TAC(TAUT `p ==> (q /\ (p ==> r) ==> r)`) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - b1)`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - b1)`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - b1)`;
                   `IMAGE (p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1) {Z | Z IN S /\ p2a_J V tt x b1 Z <= &M}`;
                   `K:A->bool`; `v:real`; `Q:real`] MFD_HAS_VOLUME_MONO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp e0 * inv(sqrt b1 pow 3) *
              (p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x * drop(integral {Z | Z IN S /\ p2a_J V tt x b1 Z <= &M}
                                                  (\Z. lift(p2a_J V tt x b1 Z))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE]] THEN
  SUBGOAL_THEN
   `exp e0 * inv(sqrt b1 pow 3) *
    p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x * drop(integral {Z | Z IN S /\ p2a_J V tt x b1 Z <= &M}
                                       (\Z. lift(p2a_J V tt x b1 Z))) =
    p2a_zdens V tt x * ((exp e0 * inv(sqrt b1 pow 3)) *
                        drop(integral {Z | Z IN S /\ p2a_J V tt x b1 Z <= &M}
                                      (\Z. lift(p2a_J V tt x b1 Z))))`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REWRITE_TAC[GSYM DROP_CMUL] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    X_GEN_TAC `Z:real^3` THEN REWRITE_TAC[IN_ELIM_THM; DROP_CMUL; LIFT_DROP] THEN
    STRIP_TAC THEN REWRITE_TAC[p2a_rvi; real_div; DIMINDEX_3] THEN
    SUBGOAL_THEN `&0 <= p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z` ASSUME_TAC THENL
     [MATCH_MP_TAC P2A_T81_J_NONNEG THEN ASM_SIMP_TAC[P2A_VIEW_PROJ_3]; ALL_TAC] THEN
    MATCH_MP_TAC P2A_T81_MUL_LE_AUX THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV; REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_ltil")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let P2A_T81_SMALL_PART = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x b b1 S K e0 Q.
     P2A_REQ_AREA_STATEMENT (u:A->bool) /\
     p2a_svs V /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt /\
     lebesgue_measurable S /\ bounded S /\ S SUBSET p2a_Smin V tt x b /\
     &0 < b1 /\ b1 <= b /\
     (!Z Z'. Z IN S /\ Z' IN S /\ p2a_Lexp V tt x b1 Z = p2a_Lexp V tt x b1 Z'
             ==> Z = Z') /\
     (!Z. Z IN S ==> p2a_Lexp V tt x b1 Z IN K /\ --e0 <= p2a_ltil V tt x b1 Z) /\
     mfd_has_volume (rfs_vtop V (tt - b1),rfs_vatlas V (tt - b1)) (rfs_vmetric V (tt - b1))
                    K Q /\
     &0 <= Q /\ (\Z. lift(p2a_rvi V tt x b1 Z)) absolutely_integrable_on S
     ==> p2a_zdens V tt x * drop(integral S (\Z. lift(p2a_rvi V tt x b1 Z))) <=
         exp e0 * inv(sqrt b1 pow 3) * Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!Z:real^3. Z IN S ==> Z IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_T81_SMIN_LDOM THEN EXISTS_TAC `b:real` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt b1 pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `x:A`] P2A_T81_DENS_X) THEN
    ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!M. p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x *
        drop(integral {Z | Z IN S /\ p2a_J V tt x b1 Z <= &M}
                      (\Z. lift(p2a_rvi V tt x b1 Z))) <=
        exp e0 * inv(sqrt b1 pow 3) * Q`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2A_T81_SMALL_TRUNC THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(M:num) (Z:real^3). if Z IN {Z | p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z <= &M}
                                       then lift(p2a_rvi V tt x b1 Z) else vec 0`;
                 `\Z:real^3. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z)`;
                 `\Z:real^3. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z)`; `S:real^3->bool`]
                DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `M:num` THEN REWRITE_TAC[INTEGRABLE_RESTRICT_INTER] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET] THEN
      SUBGOAL_THEN `{Z | p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z <= &M} INTER S =
                    {Z | Z IN S /\ p2a_J V tt x b1 Z <= &M}` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC P2A_T81_TRUNC_MEASURABLE THEN
      ASM_REWRITE_TAC[GSYM P2A_VIEW_PROJ_3] THEN
      ASM_REWRITE_TAC[P2A_VIEW_PROJ_3; SUBSET] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      MAP_EVERY X_GEN_TAC [`M:num`; `Z:real^3`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z` ASSUME_TAC THENL
       [MATCH_MP_TAC P2A_T81_RVI_NONNEG THEN ASM_SIMP_TAC[P2A_VIEW_PROJ_3]; ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[NORM_LIFT; LIFT_DROP; NORM_0] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; IN_ELIM_THM] THEN
      MP_TAC(SPEC `p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z <= &m` (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
  DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_UBOUND) THEN
  EXISTS_TAC `\M. integral ({Z | p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z <= &M} INTER S)
                           (\Z. lift(p2a_rvi V tt x b1 Z))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `M:num` THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `{Z | p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x b1 Z <= &M} INTER S =
                {Z | Z IN S /\ p2a_J V tt x b1 Z <= &M}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The large part.  Below the Gaussian of the metric at x (RVI_MONO,         *)
(* RVI_ASYMP), and by the linear change of variables Z -> A Z (G = A^T A,    *)
(* density at x = abs(det A)), the rvi integral at b1 over a set inside {1   *)
(* <= 64 eps |Z|^2_G} is bounded by the Euclidean Gaussian tail.             *)
(* ------------------------------------------------------------------------- *)

let P2A_T81_LARGE_PART = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x b b1 S eps.
     P2A_RVI_MONO_STATEMENT (u:A->bool) /\ P2A_RVI_ASYMP_STATEMENT u /\
     P2A_GAUSS_TAIL_STATEMENT /\
     (\Z:real^3. lift(&8 * exp(--(Z dot Z)))) absolutely_integrable_on
       {Z | &1 <= &64 * eps * (Z dot Z)} /\
     drop(integral {Z | &1 <= &64 * eps * (Z dot Z)}
                   (\Z:real^3. lift(&8 * exp(--(Z dot Z))))) <= eps * sqrt eps /\
     p2a_svs V /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt /\
     lebesgue_measurable S /\ S SUBSET p2a_Smin V tt x b /\ &0 < b1 /\ b1 <= b /\
     (!Z. Z IN S ==> &1 <= &64 * eps * p2a_znorm2 V tt x Z)
     ==> p2a_zdens V tt x * drop(integral S (\Z. lift(p2a_rvi V tt x b1 Z))) <=
         eps * sqrt eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2A_T81_DENS_X) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[P2A_VIEW_PROJ_3]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `TG = {Z:real^3 | &1 <= &64 * eps * (Z dot ((transp (A:real^3^3) ** A) ** Z))}` THEN
  SUBGOAL_THEN `IMAGE (\Z. (A:real^3^3) ** Z) TG = {Z:real^3 | &1 <= &64 * eps * (Z dot Z)}`
  ASSUME_TAC THENL
   [EXPAND_TAC "TG" THEN
    MP_TAC(ISPECL [`A:real^3^3`; `\t. &1 <= &64 * eps * t`] P2A_T81_IMAGE_COV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^3^3`; `TG:real^3->bool`] P2A_T81_GAUSS_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(S:real^3->bool) SUBSET TG` ASSUME_TAC THENL
   [EXPAND_TAC "TG" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_znorm2")) (concl th))) THEN
    ASM_REWRITE_TAC[p2a_znorm2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\Z:real^3. lift(&8 * exp(--(Z dot ((transp (A:real^3^3) ** A) ** Z))))) absolutely_integrable_on S`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `x:A`] P2A_T81_GAUSS_X) THEN
    ASM_REWRITE_TAC[P2A_VIEW_PROJ_3; p2a_znorm2] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM P2A_VIEW_PROJ_3]; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(det(A:real^3^3)) *
              drop(integral TG (\Z:real^3. lift(&8 * exp(--(Z dot ((transp A ** A) ** Z))))))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral S
                  (\Z:real^3. lift(&8 * exp(--(Z dot ((transp (A:real^3^3) ** A) ** Z))))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC P2A_T81_RVI_INTEGRABLE THEN EXISTS_TAC `b:real` THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
        X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
        MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)`; `tt:real`; `x:A`; `b:real`; `Z:real^3`;
                       `b1:real`] P2A_T81_RVI_GAUSS) THEN
        ASM_REWRITE_TAC[p2a_znorm2] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]];
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      REWRITE_TAC[LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term (fun t -> t = `abs(det(A:real^3^3))`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "integral")) (concl th))) THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[DROP_CMUL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The estimates at tau0 (area inequality over S, minimizers of length at    *)
(* most 2 sqrt(tau0) l0, monotonicity of rvi) and at tau1 = eps r^2 (small   *)
(* and large parts), then the route obligation O4.                           *)
(* ------------------------------------------------------------------------- *)

let P2A_T81_VOL_EMPTY = prove
 (`!top atlas (g:A->real^N^N) v. mfd_has_volume (top,atlas) g {} v ==> v = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_has_volume; mfd_has_integral; mfd_chart_partition] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)` (X_CHOOSE_THEN `E:num->A->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!n. (E:num->A->bool) n = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS {(E:num->A->bool) n | n IN (:num)} = {}` THEN
    REWRITE_TAC[EMPTY_UNIONS; FORALL_IN_GSPEC; IN_UNIV];
    ALL_TAC] THEN
  UNDISCH_TAC `((\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) (E n))
                     (mfd_chart_integrand atlas (g:A->real^N^N) (\x. &1) (c n)))) real_sums v)
               (from 0)` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; INTEGRAL_EMPTY; DROP_VEC] THEN
  MESON_TAC[REAL_SERIES_UNIQUE; REAL_SERIES_0]);;

let P2A_T81_EXP_SMALL = prove
 (`!e. &0 <= e /\ e <= inv(&8) ==> exp(&8 * e) <= &3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    MP_TAC E_APPROX_32 THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REAL_ARITH_TAC]);;

(* The estimate at tau0: Vol B <= e^l0 tau0^(3/2) zdens integral_S rvi(tau1).  *)

let P2A_T81_TAU0 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x tau0 tau1 B l0 vB.
     P2A_REQ_AREA_STATEMENT (u:A->bool) /\ P2A_RVI_MONO_STATEMENT u /\
     P2A_RVI_ASYMP_STATEMENT u /\ P2A_GAUSS_TAIL_STATEMENT /\
     p2a_svs V /\ p2a_atlas_lc V /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt /\
     &0 < tau1 /\ tau1 <= tau0 /\
     open_in (rfs_vtop V (tt - tau0)) B /\ ~(B = {}) /\
     mfd_has_volume (rfs_vtop V (tt - tau0),rfs_vatlas V (tt - tau0))
                    (rfs_vmetric V (tt - tau0)) B vB /\
     (!q. q IN B
          ==> ?gamma. p2a_min V tt x tau0 gamma /\ gamma tau0 = q /\
                      p2a_L_length V tt gamma tau0 <= &2 * sqrt tau0 * l0)
     ==> vB <= exp l0 * sqrt tau0 pow 3 *
               (p2a_zdens V tt x *
                drop(integral {Z | Z IN p2a_Smin V tt x tau0 /\ p2a_Lexp V tt x tau0 Z IN B}
                              (\Z. lift(p2a_rvi V tt x tau1 Z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = {Z | Z IN p2a_Smin (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 /\
                       p2a_Lexp V tt x tau0 Z IN B}` THEN
  SUBGOAL_THEN `&0 < tau0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau0)) (rfs_vatlas V (tt - tau0)) /\
                riemannian_metric (rfs_vatlas V (tt - tau0)) (rfs_vmetric V (tt - tau0))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN
    DISCH_THEN(MP_TAC o SPEC `tt - tau0`) THEN
    MATCH_MP_TAC(TAUT `p ==> (q /\ (p ==> r) ==> r)`) THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET
      (ASSUME `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau0)) B`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `x:A`] P2A_T81_DENS_X) THEN
    ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^3->bool) SUBSET p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable (S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC P2A_T81_S_MEASURABLE THEN
    ASM_REWRITE_TAC[P2A_VIEW_PROJ_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^3. Z IN S ==> Z IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_T81_SMIN_LDOM THEN EXISTS_TAC `tau0:real` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0) S = B` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `q:A` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_min")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `x:A`; `tau0:real`; `gamma:real->A`]
                  P2A_T81_SMIN_OF_MIN) THEN
    ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(S:real^3->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^3. Z IN S ==> p2a_ltil (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 Z <= l0` ASSUME_TAC THENL
   [X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 Z IN B /\ Z IN p2a_Smin V tt x tau0`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 Z` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_min")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[p2a_ltil; p2a_Ltil] THEN
    SUBGOAL_THEN `&0 < &2 * sqrt tau0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt gamma tau0` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    UNDISCH_TAC `(Z:real^3) IN p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0` THEN
    REWRITE_TAC[p2a_Smin; IN_ELIM_THM; p2a_min] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[p2a_min]; ASM_REWRITE_TAC[GSYM p2a_Lexp]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 Z)) absolutely_integrable_on S /\
                (\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau1 Z)) absolutely_integrable_on S`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2A_T81_RVI_INTEGRABLE THEN EXISTS_TAC `tau0:real` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z:real^3. Z IN S
               ==> p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 Z <=
                   (exp l0 * sqrt tau0 pow 3) * p2a_rvi V tt x tau1 Z`
  ASSUME_TAC THENL
   [X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `x:A`; `tau0:real`; `Z:real^3`]
                  P2A_T81_J_RVI) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `&0 <= p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 Z /\
                  p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 Z <= p2a_rvi V tt x tau1 Z` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC P2A_T81_RVI_NONNEG THEN ASM_SIMP_TAC[P2A_VIEW_PROJ_3];
        UNDISCH_TAC `P2A_RVI_MONO_STATEMENT (u:A->bool)` THEN
        REWRITE_TAC[P2A_RVI_MONO_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
        EXISTS_TAC `tau0:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(p2a_ltil (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 Z) <= exp l0` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt tau0 pow 3` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE; SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_EXP_POS_LE; REAL_LE_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\Z. lift(p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 Z)) absolutely_integrable_on S` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\Z:real^3. (exp l0 * sqrt tau0 pow 3) % lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau1 Z)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0` THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC P2A_J_CONTINUOUS THEN ASM_REWRITE_TAC[P2A_VIEW_PROJ_3];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP] THEN
      SUBGOAL_THEN `&0 <= p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 Z` MP_TAC THENL
       [MATCH_MP_TAC P2A_T81_J_NONNEG THEN ASM_SIMP_TAC[P2A_VIEW_PROJ_3]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_J")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `tau0:real`; `S:real^3->bool`]
                P2A_T81_AREA_APPLY) THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  ANTS_TAC THENL [REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `vB:real = v` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau0)`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau0)`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau0)`; `B:A->bool`; `vB:real`; `v:real`]
                  MFD_HAS_VOLUME_UNIQUE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x * drop(integral S (\Z. lift(p2a_J V tt x tau0 Z)))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `a * b * (z * d):real = z * ((a * b) * d)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REWRITE_TAC[GSYM DROP_CMUL] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; INTEGRABLE_CMUL; DROP_CMUL;
               LIFT_DROP]);;

let P2A_T81_HALF_BALL_CLOSURE = prove
 (`!top atlas (g:A->real^N^N) x r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < r
     ==> top closure_of (mfd_ball (top,atlas) g x (r / &2)) SUBSET
         mfd_ball (top,atlas) g x r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) x (r / &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P2A_T81_SSMALL_BOUNDED = prove
 (`!(A:real^N^N) eps.
     invertible A /\ &0 < eps
     ==> bounded {Z:real^N | &64 * eps * (Z dot ((transp A ** A) ** Z)) <= &1}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `IMAGE (\w:real^N. matrix_inv (A:real^N^N) ** w) (cball(vec 0,&1 + inv(&64 * eps)))` THEN
  SIMP_TAC[BOUNDED_LINEAR_IMAGE; BOUNDED_CBALL; MATRIX_VECTOR_MUL_LINEAR] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_CBALL_0] THEN
  X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN EXISTS_TAC `(A:real^N^N) ** Z` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID] THEN
  SUBGOAL_THEN `((A:real^N^N) ** Z) dot (A ** Z) <= inv(&64 * eps)` ASSUME_TAC THENL
   [REWRITE_TAC[P2A_T81_DOT_COV] THEN
    ASM_SIMP_TAC[REAL_ARITH `inv x = &1 / x`; REAL_LE_RDIV_EQ; REAL_LT_MUL;
                 REAL_OF_NUM_LT; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `(A:real^N^N) ** Z` NORM_POW_2) THEN
  MP_TAC(ISPEC `(A:real^N^N) ** Z` NORM_POS_LE) THEN
  SPEC_TAC(`norm((A:real^N^N) ** Z)`,`n:real`) THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n <= &1` THENL
   [MP_TAC(SPEC `&64 * eps` REAL_LE_INV) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `n <= n pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* The estimate at tau1 = eps r^2 for a measurable S inside Smin(tau0).       *)

let P2A_T81_TAU1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x r tau0 taub S eps eps0 vr.
     P2A_REQ_AREA_STATEMENT (u:A->bool) /\ P2A_RVI_MONO_STATEMENT u /\
     P2A_RVI_ASYMP_STATEMENT u /\ P2A_GAUSS_TAIL_STATEMENT /\
     P2A_INJ_FIX_STATEMENT u /\ P2A_PARABOLIC_STATEMENT u /\
     (!(V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
       tt' x' r' e Z.
        p2a_svs V' /\ &0 < r' /\ r' pow 2 <= taub /\ x' IN topspace(rfs_vtop V' tt') /\
        p2a_region V' (rfs_vball V' tt' x' r') (tt' - r' pow 2) tt' /\
        compact_in (rfs_vtop V' tt') ((rfs_vtop V' tt') closure_of (rfs_vball V' tt' x' r')) /\
        (!s y. tt' - r' pow 2 < s /\ s <= tt' /\ y IN rfs_vball V' tt' x' r'
               ==> p3_vrm V' s y <= inv(r' pow 2)) /\
        &0 < e /\ e <= eps0 /\
        Z IN p2a_Ldom V' tt' x' (e * r' pow 2) /\
        &64 * e * p2a_znorm2 V' tt' x' Z <= &1
        ==> (!tau. &0 <= tau /\ tau <= e * r' pow 2
                   ==> p2a_Lgeo V' tt' x' Z (e * r' pow 2) tau IN
                       rfs_vball V' tt' x' (r' / &2)) /\
            --(&2 * e) <= p2a_ltil V' tt' x' (e * r' pow 2) Z) /\
     &0 < eps /\ eps <= eps0 /\ eps <= inv(&8) /\
     (\Z:real^3. lift(&8 * exp(--(Z dot Z)))) absolutely_integrable_on
       {Z | &1 <= &64 * eps * (Z dot Z)} /\
     drop(integral {Z | &1 <= &64 * eps * (Z dot Z)}
                   (\Z:real^3. lift(&8 * exp(--(Z dot Z))))) <= eps * sqrt eps /\
     p2a_svs V /\ p2a_atlas_lc V /\ &0 < r /\ r pow 2 <= tau0 /\ r pow 2 <= taub /\
     x IN topspace(rfs_vtop V tt) /\
     p2a_region V (rfs_vball V tt x r) (tt - r pow 2) tt /\
     compact_in (rfs_vtop V tt) ((rfs_vtop V tt) closure_of (rfs_vball V tt x r)) /\
     (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball V tt x r
            ==> p3_vrm V s y <= inv(r pow 2)) /\
     mfd_has_volume (rfs_vtop V tt,rfs_vatlas V tt) (rfs_vmetric V tt)
                    (rfs_vball V tt x r) vr /\
     lebesgue_measurable S /\ S SUBSET p2a_Smin V tt x tau0
     ==> p2a_zdens V tt x * drop(integral S (\Z. lift(p2a_rvi V tt x (eps * r pow 2) Z))) <=
         &3 * inv(sqrt(eps * r pow 2) pow 3) * vr + eps * sqrt eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `tau1 = eps * r pow 2` THEN
  SUBGOAL_THEN `&0 < tau1 /\ tau1 < tau0 /\ tau1 <= tau0 /\ &0 < r pow 2 /\ tau1 < r pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tau1" THEN
    SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN
    SUBGOAL_THEN `eps * r pow 2 < r pow 2` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_C712_VBALL_CENTRE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_bsmooth (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x tt` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_bsmooth] THEN
    MAP_EVERY EXISTS_TAC [`rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `tt - r pow 2`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2A_T81_DENS_X) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[P2A_VIEW_PROJ_3]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!Z:real^3. p2a_znorm2 (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x Z = Z dot ((transp (A:real^3^3) ** A) ** Z)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[p2a_znorm2]; ALL_TAC] THEN
  ABBREV_TAC `Ss = {Z | Z IN S /\ &64 * eps * p2a_znorm2 (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x Z <= &1}` THEN
  ABBREV_TAC `Sl = {Z | Z IN S /\ ~(&64 * eps * p2a_znorm2 (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x Z <= &1)}` THEN
  SUBGOAL_THEN `lebesgue_measurable (Ss:real^3->bool) /\ lebesgue_measurable (Sl:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `lebesgue_measurable {Z:real^3 | &64 * eps * (Z dot ((transp (A:real^3^3) ** A) ** Z)) <= &1}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LEBESGUE_MEASURABLE_CLOSED THEN
      SUBGOAL_THEN `{Z:real^3 | &64 * eps * (Z dot ((transp (A:real^3^3) ** A) ** Z)) <= &1} =
                    {Z | (\Z. lift(&64 * eps * (Z dot ((transp (A:real^3^3) ** A) ** Z)))) Z IN
                         {y | drop y <= &1}}` SUBST1_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
      REWRITE_TAC[drop; CLOSED_HALFSPACE_COMPONENT_LE] THEN
      GEN_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
      REPEAT(MATCH_MP_TAC CONTINUOUS_CMUL) THEN
      MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN
      SIMP_TAC[CONTINUOUS_AT_ID; LINEAR_CONTINUOUS_AT; MATRIX_VECTOR_MUL_LINEAR];
      ALL_TAC] THEN
    SUBGOAL_THEN `Ss = S INTER {Z:real^3 | &64 * eps * (Z dot ((transp (A:real^3^3) ** A) ** Z)) <= &1} /\
                  Sl = S DIFF {Z:real^3 | &64 * eps * (Z dot ((transp (A:real^3^3) ** A) ** Z)) <= &1}`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [MAP_EVERY EXPAND_TAC ["Ss"; "Sl"] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_INTER; LEBESGUE_MEASURABLE_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `Ss SUBSET (S:real^3->bool) /\ Sl SUBSET S /\ S = Ss UNION Sl /\
                Ss INTER Sl = {}` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Ss"; "Sl"] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau1 Z)) absolutely_integrable_on Ss /\
                (\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau1 Z)) absolutely_integrable_on Sl`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2A_T81_RVI_INTEGRABLE THEN EXISTS_TAC `tau0:real` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral S (\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau1 Z))) =
    drop(integral Ss (\Z. lift(p2a_rvi V tt x tau1 Z))) +
    drop(integral Sl (\Z. lift(p2a_rvi V tt x tau1 Z)))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `S:real^3->bool = Ss UNION Sl`
                            then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[GSYM DROP_ADD] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_UNION THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; NEGLIGIBLE_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC P2A_T81_LARGE_PART THEN EXISTS_TAC `tau0:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Sl" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC] THEN
  (* the small part *)
  SUBGOAL_THEN `hausdorff_space (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) /\
                smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) (p2a_vatlas V tt) /\
                riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) (p2a_vmetric V tt) /\
                hausdorff_space (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)) /\
                smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)) (p2a_vatlas V (tt - tau1)) /\
                riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)) (p2a_vmetric V (tt - tau1))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `tt - r pow 2`; `tt:real`;
                   `tt - tau1`] P2A_REGION_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN REWRITE_TAC[p2a_svs] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `tt:real` th) THEN MP_TAC(SPEC `tt - tau1` th)) THEN
    SUBGOAL_THEN `~(topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) = {}) /\
                  ~(topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)) = {})` MP_TAC THENL
     [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
        `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)) (rfs_vball V tt x r)`)) THEN
      UNDISCH_TAC `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)` THEN
      REWRITE_TAC[GSYM P2A_VIEW_PROJ_3] THEN ASM SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `K = (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) closure_of (rfs_vball V tt x (r / &2))` THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[P2A_VBALL_ALT; GSYM P2A_VIEW_PROJ_3] THEN
    MATCH_MP_TAC P2A_T81_HALF_BALL_CLOSURE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    MATCH_MP_TAC(SET_RULE `!s t (y:A). s SUBSET t /\ y IN s ==> y IN t`) THEN
    EXISTS_TAC `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x (r / &2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
      REWRITE_TAC[P2A_VBALL_ALT; GSYM P2A_VIEW_PROJ_3; mfd_ball; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      MATCH_MP_TAC P2A_C712_VBALL_CENTRE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) K /\ compact_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)) K`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `compact_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) K` ASSUME_TAC THENL
     [REWRITE_TAC[P2A_VIEW_PROJ_3] THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
      EXISTS_TAC `(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) closure_of (rfs_vball V tt x r)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
      MATCH_MP_TAC CLOSURE_OF_MONO THEN
      REWRITE_TAC[P2A_VBALL_ALT; mfd_ball; SUBSET; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `tt - r pow 2`; `tt:real`;
                   `tt - tau1`] P2A_REGION_SUBTOP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)`; `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `K:A->bool`]
                  COMPACT_IN_SUBTOPOLOGY) THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `K:A->bool`]
                  COMPACT_IN_SUBTOPOLOGY) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `K:A->bool`]
                MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `vK:real`) THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)`;
                 `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)`; `K:A->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Q:real`) THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)`;
                   `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - tau1)`; `K:A->bool`; `Q:real`]
                  MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `vK <= vr` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`;
                   `K:A->bool`; `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `vK:real`; `vr:real`]
                  MFD_HAS_VOLUME_MONO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[P2A_VIEW_PROJ_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q <= exp(&4 * eps) * sqrt(exp(&4 * eps)) * vK` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_T81_SLICE_VOLCMP THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)`; `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `tt - r pow 2`;
                          `tt:real`; `tt - tau1`; `K:A->bool`] THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    UNDISCH_TAC `P2A_PARABOLIC_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2A_PARABOLIC_STATEMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `tt:real`; `x:A`; `r:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`tt - tau1`; `y:A`; `w:real^3`] o CONJUNCT2) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(K:A->bool) SUBSET rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `&4 * (tt - (tt - tau1)) / r pow 2 = &4 * eps` SUBST1_TAC THENL
     [EXPAND_TAC "tau1" THEN UNDISCH_TAC `&0 < r pow 2` THEN CONV_TAC REAL_FIELD;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(exp(&4 * eps)) = exp(&2 * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN REWRITE_TAC[REAL_EXP_POS_LE; REAL_POW_2] THEN
    REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `tau0:real`; `tau1:real`;
                 `Ss:real^3->bool`; `K:A->bool`; `&2 * eps`; `Q:real`] P2A_T81_SMALL_PART) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GSYM P2A_VIEW_PROJ_3]) THEN
    REWRITE_TAC[GSYM P2A_VIEW_PROJ_3] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `{Z:real^3 | &64 * eps * (Z dot ((transp (A:real^3^3) ** A) ** Z)) <= &1}` THEN
      ASM_SIMP_TAC[P2A_T81_SSMALL_BOUNDED] THEN EXPAND_TAC "Ss" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`Z:real^3`; `Z':real^3`] THEN STRIP_TAC THEN
      UNDISCH_TAC `P2A_INJ_FIX_STATEMENT (u:A->bool)` THEN
      REWRITE_TAC[P2A_INJ_FIX_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
        `tt:real`; `x:A`; `tau0:real`; `tau1:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
        `tt:real`; `x:A`; `r:real`; `eps:real`; `Z:real^3`] o check (fun th ->
         is_forall(concl th) &&
         can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lgeo")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC P2A_T81_SMIN_LDOM THEN EXISTS_TAC `tau0:real` THEN
          ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
          UNDISCH_TAC `(Z:real^3) IN Ss` THEN EXPAND_TAC "Ss" THEN REWRITE_TAC[IN_ELIM_THM] THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `tau1:real`) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL; GSYM p2a_Lexp] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!s t (y:A). s SUBSET t /\ y IN s ==> y IN t`) THEN
      EXISTS_TAC `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x (r / &2)` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "K" THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
      REWRITE_TAC[P2A_VBALL_ALT; GSYM P2A_VIEW_PROJ_3; mfd_ball; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(&2 * eps) * inv(sqrt tau1 pow 3) * Q` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < inv(sqrt tau1 pow 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT; SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * eps) * exp(&4 * eps) * exp(&2 * eps) <= &3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
    SUBGOAL_THEN `&2 * eps + &4 * eps + &2 * eps = &8 * eps` SUBST1_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC P2A_T81_EXP_SMALL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q <= exp(&4 * eps) * exp(&2 * eps) * vr` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&4 * eps) * exp(&2 * eps) * vK` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= vr` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`;
                   `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `vr:real`] MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[P2A_VIEW_PROJ_3];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(&2 * eps) * inv(sqrt tau1 pow 3) * (exp(&4 * eps) * exp(&2 * eps) * vr)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * eps) * inv(sqrt tau1 pow 3) * (exp(&4 * eps) * exp(&2 * eps) * vr) =
                (inv(sqrt tau1 pow 3) * vr) * (exp(&2 * eps) * exp(&4 * eps) * exp(&2 * eps))`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  SUBGOAL_THEN `&3 * inv(sqrt tau1 pow 3) * vr = (inv(sqrt tau1 pow 3) * vr) * &3`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]);;

let P2A_T81_VBALL_RFS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x r.
     rfs_vball V t x r = mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r`,
  REWRITE_TAC[P2A_VBALL_ALT; P2A_VIEW_PROJ_3]);;

(* The arithmetic of the contradiction (eps = min of the thresholds).        *)

let P2A_T81_ARITH = prove
 (`!V0 vB l0 tau0 taub r eps c0 X vr.
     &0 < V0 /\ V0 <= vB /\ &0 < tau0 /\ tau0 <= taub /\ &0 < r /\ &0 < eps /\
     eps <= inv(&8) /\ c0 = V0 * exp(--l0) / (taub * sqrt taub) /\ eps <= c0 / &8 /\
     vB <= exp l0 * sqrt tau0 pow 3 * X /\
     X <= &3 * inv(sqrt(eps * r pow 2) pow 3) * vr + eps * sqrt eps /\
     vr < eps pow 3 * r pow 3
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < taub` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt eps /\ sqrt eps pow 2 = eps /\ sqrt eps <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(eps * r pow 2) pow 3 = eps * sqrt eps * r pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2; POW_2_SQRT] THEN
    UNDISCH_TAC `sqrt eps pow 2 = eps` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps * sqrt eps * r pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(eps * sqrt eps * r pow 3) * vr <= eps * sqrt eps` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(eps * sqrt eps * r pow 3) * vr = vr / (eps * sqrt eps * r pow 3)`
    SUBST1_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_SYM]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `(eps * sqrt eps) * eps * sqrt eps * r pow 3 = eps pow 3 * r pow 3`
    SUBST1_TAC THENL
     [UNDISCH_TAC `sqrt eps pow 2 = eps` THEN CONV_TAC REAL_RING;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `X <= c0 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&4 * eps * sqrt eps` THEN CONJ_TAC THENL
     [UNDISCH_TAC `X <= &3 * inv(sqrt(eps * r pow 2) pow 3) * vr + eps * sqrt eps` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * eps` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau0 pow 3 <= taub * sqrt taub` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt tau0 pow 3 = tau0 * sqrt tau0` SUBST1_TAC THENL
     [MP_TAC(SPEC `tau0:real` SQRT_POW_2) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE; SQRT_MONO_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp l0 * (taub * sqrt taub) * c0 = V0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < taub * sqrt taub` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `l0:real` REAL_EXP_NEG_MUL) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp l0 * sqrt tau0 pow 3 * X <= exp l0 * (taub * sqrt taub) * (c0 / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt tau0 pow 3 * c0 / &2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; SQRT_POS_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp l0 * (taub * sqrt taub) * (c0 / &2) = V0 / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `exp l0 * (taub * sqrt taub) * c0 = V0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The route obligation O4: MT Thm 8.1 (kappa-noncollapsing) for views with  *)
(* locally constant atlases from the leaves.                                 *)

let P2A_T81_CORE = prove
 (`!u:A->bool.
     P2A_RVI_MONO_STATEMENT u /\ P2A_RVI_ASYMP_STATEMENT u /\ P2A_PARABOLIC_STATEMENT u /\
     P2A_SMALLZ_STATEMENT u /\ P2A_GAUSS_TAIL_STATEMENT /\ P2A_REQ_AREA_STATEMENT u /\
     P2A_INJ_FIX_STATEMENT u
     ==> P2A_THM_8_1_VIEW_FIX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_THM_8_1_VIEW_FIX_STATEMENT] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`taub:real`; `l0:real`; `V0:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `taub:real` o GEN_REWRITE_RULE I [P2A_SMALLZ_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sz"))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2A_GAUSS_TAIL_STATEMENT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0g:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gt"))) THEN
  SUBGOAL_THEN `&0 < taub * sqrt taub` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `c0 = V0 * exp(--l0) / (taub * sqrt taub)` THEN
  SUBGOAL_THEN `&0 < c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_EXP_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `eps = min (min eps0 eps0g) (min (inv(&8)) (c0 / &8))` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= eps0 /\ eps <= eps0g /\ eps <= inv(&8) /\ eps <= c0 / &8`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `eps pow 3` THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:A`; `tt:real`; `r:real`; `tau0:real`; `B:A->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `hausdorff_space (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) /\
                smooth_manifold_atlas (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) (rfs_vatlas V tt) /\
                riemannian_metric (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) (rfs_vmetric V tt)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN
    DISCH_THEN(MP_TAC o SPEC `tt:real`) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?vr. mfd_has_volume (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt,rfs_vatlas V tt) (rfs_vmetric V tt)
                                    (rfs_vball V tt x r) vr` (X_CHOOSE_TAC `vr:real`) THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`;
                   `(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) closure_of (rfs_vball V tt x r)`]
                  MFD_HAS_VOLUME_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`; `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt`;
                   `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) closure_of (rfs_vball V tt x r)`;
                   `w:real`] MFD_HAS_VOLUME_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) (rfs_vball V tt x r)` ASSUME_TAC THENL
     [REWRITE_TAC[P2A_T81_VBALL_RFS] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]];
    ALL_TAC] THEN
  EXISTS_TAC `vr:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(B:A->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP P2A_T81_VOL_EMPTY o check (fun th ->
      can (find_term (fun t -> t = `v:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_has_volume")) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_C712_VBALL_CENTRE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_bsmooth (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x tt` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_bsmooth] THEN
    MAP_EVERY EXISTS_TAC [`rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `tt - r pow 2`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < r pow 2` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps * r pow 2 /\ eps * r pow 2 <= tau0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `r pow 2` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `tau0:real`; `eps * r pow 2`;
                 `B:A->bool`; `l0:real`; `v:real`] P2A_T81_TAU0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `r:real`; `tau0:real`;
                 `taub:real`;
                 `{Z | Z IN p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau0 /\ p2a_Lexp V tt x tau0 Z IN B}`;
                 `eps:real`; `eps0:real`; `vr:real`] P2A_T81_TAU1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "gt" (MP_TAC o SPEC `eps:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2A_T81_S_MEASURABLE THEN ASM_REWRITE_TAC[P2A_VIEW_PROJ_3];
      SET_TAC[]];
    DISCH_TAC] THEN
  MATCH_MP_TAC P2A_T81_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`V0:real`; `v:real`; `l0:real`; `tau0:real`; `taub:real`; `r:real`; `eps:real`;
    `c0:real`;
    `p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x *
     drop(integral {Z | Z IN p2a_Smin V tt x tau0 /\ p2a_Lexp V tt x tau0 Z IN B}
                   (\Z. lift(p2a_rvi V tt x (eps * r pow 2) Z)))`;
    `vr:real`] THEN
  ASM_REWRITE_TAC[]);;

let P2A_ROUTE_8_1_FIX = prove
 (`!u:A->bool. P2A_ROUTE_8_1_FIX_STATEMENT u`,
  REWRITE_TAC[P2A_ROUTE_8_1_FIX_STATEMENT] THEN MESON_TAC[P2A_T81_CORE]);;

(* C1 FIX from the leaves L5 RVI_MONO, L6 RVI_ASYMP, L8 PARABOLIC, L9        *)
(* SMALLZ, L10 GAUSS_TAIL and the area formula P2A_REQ_AREA_STATEMENT; L1,   *)
(* L2, L3, L7 and the volume comparison P2A_REQ_VOLCMP_STATEMENT are not     *)
(* needed, L4 is P2A_INJ_FIX.                                                *)

let P2A_THM_8_1_FIX_REDUCED = prove
 (`!u:A->bool.
     P2A_RVI_MONO_STATEMENT u /\ P2A_RVI_ASYMP_STATEMENT u /\ P2A_PARABOLIC_STATEMENT u /\
     P2A_SMALLZ_STATEMENT u /\ P2A_GAUSS_TAIL_STATEMENT /\ P2A_REQ_AREA_STATEMENT u
     ==> P2A_THM_8_1_VIEW_FIX_STATEMENT u`,
  MESON_TAC[P2A_T81_CORE; P2A_INJ_FIX]);;

(* The interface Thm 8.1 from the same leaves and the history bridge.      *)

let P2A_THM_8_1_FROM_LEAVES = prove
 (`!u:A->bool.
     P2A_RVI_MONO_STATEMENT u /\ P2A_RVI_ASYMP_STATEMENT u /\ P2A_PARABOLIC_STATEMENT u /\
     P2A_SMALLZ_STATEMENT u /\ P2A_GAUSS_TAIL_STATEMENT /\ P2A_REQ_AREA_STATEMENT u /\
     P2A_HIST_VIEW_STATEMENT u
     ==> P2_THM_8_1_STATEMENT u`,
  MESON_TAC[P2A_THM_8_1_FIX_REDUCED; P2A_T1_FIX]);;

