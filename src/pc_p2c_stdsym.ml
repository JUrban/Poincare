(* ========================================================================= *)
(* Unit pc_p2c_stdsym (Part 2C; MT Ch 12, the standard solution): the       *)
(* maximal standard flow and its symmetries.  The maximal partial standard  *)
(* flow Gs on [0,Tm), 0 < Tm <= 1 (p3_std_flow g0 Tm Gs), is unique: every  *)
(* partial standard flow is Gs; Gs is SO(3)-invariant (MT Thm 12.5 (4)).    *)
(* The rotational theory of SO(3)-invariant metric fields on real^3: the    *)
(* radial form, the radial distance, and the sectional curvatures K_tan and *)
(* K_rad in terms of the Euclidean radius; q >= 0 for complete metrics with *)
(* sec >= 0.                                                                *)
(* ========================================================================= *)

needs "src/pc_p2c_stdasym.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The maximal flow.  Tm = sup of the te of the partial                      *)
(* standard flows (positive by PARTIAL_EXISTS, at most 1 by Cor 12.8), Gs   *)
(* agrees with every partial flow (UNIQUE), and p3_std_flow g0 Tm Gs.       *)
(* ------------------------------------------------------------------------- *)

let stds_tm = new_definition
 `stds_tm (g0:real^3->real^3^3) =
    sup {te | ?G:real->real^3->real^3^3. p3_partial_std g0 te G}`;;

let stds_gs = new_definition
 `stds_gs (g0:real^3->real^3^3) (t:real) =
    (@G:real->real^3->real^3^3. ?te. p3_partial_std g0 te G /\ t < te) t`;;

let STDS_TM_FACTS = prove
 (`!g0 A0.
     P2C_STD_PARTIAL_EXISTS_STATEMENT /\ P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\
     P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\ P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\
     p3_std_initial g0 A0
     ==> &0 < stds_tm g0 /\ stds_tm g0 <= &1 /\
         (!te G. p3_partial_std g0 te G ==> te <= stds_tm g0) /\
         (!t. t < stds_tm g0 ==> ?te G. p3_partial_std g0 te G /\ t < te)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[stds_tm] THEN
  ABBREV_TAC `S = {te | ?G:real->real^3->real^3^3. p3_partial_std g0 te G}` THEN
  SUBGOAL_THEN `!te. te IN S <=> ?G:real->real^3->real^3^3. p3_partial_std g0 te G`
  (LABEL_TAC "S") THENL [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `?te0. &0 < te0 /\ te0 IN S` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_STD_PARTIAL_EXISTS_STATEMENT` THEN
    REWRITE_TAC[P2C_STD_PARTIAL_EXISTS_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN S ==> x <= &1` ASSUME_TAC THENL
   [USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC STDS_TE_LE_1 THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(S:real->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `te0:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "lub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "ub" MATCH_MP_TAC THEN
    USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real->bool`; `t:real`] SUP_APPROACH) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[]]);;

let STDS_GS_EQ = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) t.
     P2C_STD_UNIQUE_STATEMENT /\ p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\
     &0 <= t /\ t < te
     ==> stds_gs g0 t = G t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_gs] THEN
  ABBREV_TAC `H = @G:real->real^3->real^3^3. ?te. p3_partial_std g0 te G /\ t < te` THEN
  SUBGOAL_THEN `?te'. p3_partial_std g0 te' (H:real->real^3->real^3^3) /\ t < te'`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^3` THEN
  UNDISCH_TAC `P2C_STD_UNIQUE_STATEMENT` THEN REWRITE_TAC[P2C_STD_UNIQUE_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `te':real`;
                             `G:real->real^3->real^3^3`; `H:real->real^3->real^3^3`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:real^3`]) THEN
  ASM_REWRITE_TAC[]);;

let STDS_GS_FLOW = prove
 (`!g0 A0.
     P2C_STD_PARTIAL_EXISTS_STATEMENT /\ P2C_STD_UNIQUE_STATEMENT /\
     P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\ p3_std_initial g0 A0
     ==> p3_std_flow g0 (stds_tm g0) (stds_gs g0) /\ &0 < stds_tm g0 /\ stds_tm g0 <= &1 /\
         (!te G t. p3_partial_std g0 te G /\ &0 <= t /\ t < te
                   ==> te <= stds_tm g0 /\ stds_gs g0 t = G t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_TM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "le") (LABEL_TAC "appr")))) THEN
  ABBREV_TAC `Tm = stds_tm g0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!te G t. p3_partial_std g0 te (G:real->real^3->real^3^3) /\ &0 <= t /\ t < te
                         ==> stds_gs g0 t = G t` (LABEL_TAC "eq") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC STDS_GS_EQ THEN
    MAP_EVERY EXISTS_TAC [`A0:real`; `te:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[p3_std_flow] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`te':real`; `G':real->real^3->real^3^3`] THEN
    STRIP_TAC THEN USE_THEN "le" (MP_TAC o SPECL [`te':real`; `G':real->real^3->real^3^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]] THEN
  REWRITE_TAC[p3_partial_std] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_RFF_UNION THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `b:real` THEN STRIP_TAC THEN
    USE_THEN "appr" (MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `te:real` (X_CHOOSE_THEN `G:real->real^3->real^3^3`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC PDE_RFF_CONG THEN EXISTS_TAC `G:real->real^3->real^3^3` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`&0`; `te:real`] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[p3_partial_std]; ASM_REAL_ARITH_TAC];
      REPEAT STRIP_TAC THEN AP_THM_TAC THEN USE_THEN "eq" MATCH_MP_TAC THEN
      EXISTS_TAC `te:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    USE_THEN "appr" (MP_TAC o SPEC `&0`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `te:real` (X_CHOOSE_THEN `G:real->real^3->real^3^3`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(G:real->real^3->real^3^3) (&0)` THEN
    CONJ_TAC THENL
     [USE_THEN "eq" MATCH_MP_TAC THEN EXISTS_TAC `te:real` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      ASM_MESON_TAC[p3_partial_std]];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "appr" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `te:real` (X_CHOOSE_THEN `G:real->real^3->real^3^3`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `stds_gs g0 t = (G:real->real^3->real^3^3) t` SUBST1_TAC THENL
     [USE_THEN "eq" MATCH_MP_TAC THEN EXISTS_TAC `te:real` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[p3_partial_std]];
    X_GEN_TAC `t1:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `t1 < &0` THENL
     [EXISTS_TAC `&0` THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "appr" (MP_TAC o SPEC `t1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `te:real` (X_CHOOSE_THEN `G:real->real^3->real^3^3`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `?K. !t x. &0 <= t /\ t <= t1
                          ==> mfd_rm_norm (open_set_atlas (:real^3))
                                          ((G:real->real^3->real^3^3) t) x <= K`
    MP_TAC THENL
     [UNDISCH_TAC `p3_partial_std g0 te (G:real->real^3->real^3^3)` THEN
      REWRITE_TAC[p3_partial_std] THEN
      DISCH_THEN(MP_TAC o SPEC `t1:real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_TAC `K:real`)] THEN
    EXISTS_TAC `K:real` THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `stds_gs g0 t = (G:real->real^3->real^3^3) t` SUBST1_TAC THENL
     [USE_THEN "eq" MATCH_MP_TAC THEN EXISTS_TAC `te:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Ricci flows on R^3 (identity chart) are the local Ricci                  *)
(* flows of pc_lrg_evol, and they are carried to Ricci flows by orthogonal *)
(* maps.                                                                     *)
(* ------------------------------------------------------------------------- *)

let STDS_MFD_RICCI_UNIV = prove
 (`!(g:real^3->real^3^3) x. mfd_ricci (open_set_atlas (:real^3)) g x = lricci g x`,
  REWRITE_TAC[mfd_ricci; P2CN_OPEN_UNIV_CHART; P2C_OPEN_SET_METRIC_LOCAL_UNIV; SND]);;

let STDS_RIEM_UNIV_EQ = prove
 (`!(g:real^3->real^3^3).
     riemannian_metric (open_set_atlas (:real^3)) g <=> metric_field (:real^3) g`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC P3S_OPEN_RIEM_FIELD THEN ASM_REWRITE_TAC[OPEN_UNIV];
    DISCH_TAC THEN MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_UNIV]]);;

let STDS_RFO_EUCLID = prove
 (`!a b (g:real->real^3->real^3^3).
     ricci_flow_on (euclidean,open_set_atlas (:real^3)) a b g <=>
     lricci_flow (:real^3) a b g`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ricci_flow_on; lricci_flow; RFB_OPEN_SET_ATLAS_CASES; FORALL_UNWIND_THM2;
              FST; SND; IMAGE_ID; P2C_OPEN_SET_METRIC_LOCAL_UNIV; P2C_EUCLID_FACTS;
              OPEN_UNIV; IN_UNIV; STDS_RIEM_UNIV_EQ] THEN
  SIMP_TAC[RFB_MFD_RICCI_MATRIX_COMPONENT; STDS_MFD_RICCI_UNIV]);;

let STDS_MPULLBACK_LIN = prove
 (`!(Q:real^3^3) (G:real^3->real^3^3) y.
     mpullback (\x. Q ** x) G y = transp Q ** G (Q ** y) ** Q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (\x:real^3. (Q:real^3^3) ** x) (at y) = (\x. Q ** x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL]]);;

let STDS_ORTH_DIFFEO = prove
 (`!(Q:real^3^3). orthogonal_matrix Q
     ==> diffeomorphism_on (:real^3) (:real^3) (\x. Q ** x) (\x. transp Q ** x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diffeomorphism_on; OPEN_UNIV] THEN
  SUBGOAL_THEN `!x:real^3. transp Q ** (Q:real^3^3) ** x = x /\ Q ** transp Q ** x = x`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ORTHOGONAL_MATRIX_TRANSP_LMUL th;
                                      MATCH_MP ORTHOGONAL_MATRIX_TRANSP_RMUL th]) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `(\x:real^3. (Q:real^3^3) ** x) = (\x. Q ** x) o (\x. x)` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR];
    SUBGOAL_THEN `(\x:real^3. transp(Q:real^3^3) ** x) = (\x. transp Q ** x) o (\x. x)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR]]);;

let STDS_RFF_ROT = prove
 (`!a b (g:real->real^3->real^3^3) (Q:real^3^3).
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) a b g /\ orthogonal_matrix Q
     ==> ricci_flow_from (euclidean,open_set_atlas (:real^3)) a b
           (\t x. transp Q ** g t (Q ** x) ** Q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\t x. transp (Q:real^3^3) ** (g:real->real^3->real^3^3) t (Q ** x) ** Q) =
                (\t. mpullback (\x. Q ** x) (g t))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; STDS_MPULLBACK_LIN]; ALL_TAC] THEN
  UNDISCH_TAC `ricci_flow_from (euclidean,open_set_atlas (:real^3)) a b
                 (g:real->real^3->real^3^3)` THEN
  REWRITE_TAC[ricci_flow_from; STDS_RFO_EUCLID] THEN
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; FORALL_UNWIND_THM2; FST; SND; IMAGE_ID;
              P2C_OPEN_SET_METRIC_LOCAL_UNIV; STDS_RIEM_UNIV_EQ; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`
      STRIP_ASSUME_TAC)))) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_FLOW_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `\x:real^3. transp (Q:real^3^3) ** x`] THEN
    ASM_SIMP_TAC[STDS_ORTH_DIFFEO];
    BETA_TAC THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `\x:real^3. transp (Q:real^3^3) ** x`] THEN
    ASM_SIMP_TAC[STDS_ORTH_DIFFEO];
    ALL_TAC] THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC `(vectorize:real^3^3->real^(3,3)finite_prod) o
              (\z:real^(1,3)finite_sum.
                 transp Q ** (matrify((Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)
                                (pastecart (fstcart z) ((Q:real^3^3) ** sndcart z))) ** Q))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ABBREV_TAC `S = interval(lift(a - e),lift b) PCROSS (:real^3)` THEN
    SUBGOAL_THEN `open (S:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_CONST]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_CONST]] THEN
    REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY] THEN
    SUBGOAL_THEN
     `(\z:real^(1,3)finite_sum. (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)
                                 (pastecart (fstcart z) ((Q:real^3^3) ** sndcart z))) =
      Fx o (\z. pastecart (fstcart z) (Q ** sndcart z))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `S:real^(1,3)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "S" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART; PASTECART_IN_PCROSS; IN_UNIV] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
      ASM_SIMP_TAC[LRG_SMOOTH_LINEAR; LINEAR_FSTCART] THEN
      MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(\z:real^(1,3)finite_sum. (Q:real^3^3) ** sndcart z) =
                    (\x. Q ** x) o sndcart` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC LINEAR_COMPOSE THEN
      REWRITE_TAC[LINEAR_SNDCART; MATRIX_VECTOR_MUL_LINEAR]];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; MATRIFY_VECTORIZE;
                 STDS_MPULLBACK_LIN]]);;

(* The orthogonal maps are isometries from the rotated metric.               *)

let STDS_ROT_ISOMETRY = prove
 (`!(G:real^3->real^3^3) (Q:real^3^3).
     orthogonal_matrix Q
     ==> mfd_isometry (euclidean,open_set_atlas (:real^3)) (\x. transp Q ** G (Q ** x) ** Q)
                      (euclidean,open_set_atlas (:real^3)) G
                      (\x. Q ** x) (\x. transp Q ** x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_isometry; MFD_DIFFEO_EUCLIDEAN; TOPSPACE_EUCLIDEAN] THEN
  ASM_SIMP_TAC[STDS_ORTH_DIFFEO] THEN
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[P2C_OPEN_SET_METRIC_LOCAL_UNIV; P2CN_OPEN_UNIV_CHART; SND] THEN
  REWRITE_TAC[o_DEF] THEN REWRITE_TAC[STDS_MPULLBACK_LIN]);;

let STDS_COMPLETE_ROT = prove
 (`!(G:real^3->real^3^3) (Q:real^3^3).
     orthogonal_matrix Q /\ metric_field (:real^3) G /\
     mfd_complete (euclidean,open_set_atlas (:real^3)) G
     ==> mfd_complete (euclidean,open_set_atlas (:real^3))
                      (\x. transp Q ** G (Q ** x) ** Q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (:real^3) (\x. transp (Q:real^3^3) ** (G:real^3->real^3^3) (Q ** x) ** Q)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. transp (Q:real^3^3) ** (G:real^3->real^3^3) (Q ** x) ** Q) =
                  mpullback (\x. Q ** x) G` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; STDS_MPULLBACK_LIN]; ALL_TAC] THEN
    MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `\x:real^3. transp (Q:real^3^3) ** x`] THEN
    ASM_SIMP_TAC[STDS_ORTH_DIFFEO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `\x. transp (Q:real^3^3) ** (G:real^3->real^3^3) (Q ** x) ** Q`;
                 `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `G:real^3->real^3^3`;
                 `\x:real^3. (Q:real^3^3) ** x`; `\x:real^3. transp (Q:real^3^3) ** x`]
                MFD_DIST_ISOMETRY) THEN
  ASM_SIMP_TAC[STDS_ROT_ISOMETRY; P2C_EUCLID_FACTS; STDS_RIEM_UNIV_EQ; IN_UNIV] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `mfd_complete (euclidean,open_set_atlas (:real^3)) (G:real^3->real^3^3)` THEN
  REWRITE_TAC[mfd_complete; TOPSPACE_EUCLIDEAN; IN_UNIV; COMPACT_IN_EUCLIDEAN] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `r:real`] THEN
  SUBGOAL_THEN `mfd_cball (euclidean,open_set_atlas (:real^3))
                  (\x. transp (Q:real^3^3) ** (G:real^3->real^3^3) (Q ** x) ** Q) x r =
                IMAGE (\y. transp (Q:real^3^3) ** y)
                  (mfd_cball (euclidean,open_set_atlas (:real^3)) G ((Q:real^3^3) ** x) r)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `(Q:real^3^3) ** y` THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ORTHOGONAL_MATRIX_TRANSP_LMUL th]) THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(Q:real^3^3) ** y = z` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ORTHOGONAL_MATRIX_TRANSP_RMUL th]) THEN
        REWRITE_TAC[MATRIX_VECTOR_MUL_LID];
        ASM_MESON_TAC[]]];
    MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]]);;

(* ------------------------------------------------------------------------- *)
(* SO(3)-invariance of the maximal flow (the rotated flow is a               *)
(* partial standard flow from the same g0, so UNIQUE identifies it).        *)
(* ------------------------------------------------------------------------- *)

let STDS_RMNORM_ROT = prove
 (`!(G:real^3->real^3^3) (Q:real^3^3) y.
     orthogonal_matrix Q /\ metric_field (:real^3) G
     ==> mfd_rm_norm (open_set_atlas (:real^3)) (\x. transp Q ** G (Q ** x) ** Q) y =
         mfd_rm_norm (open_set_atlas (:real^3)) G (Q ** y)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `\x. transp (Q:real^3^3) ** (G:real^3->real^3^3) (Q ** x) ** Q`;
                 `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `G:real^3->real^3^3`;
                 `\x:real^3. (Q:real^3^3) ** x`; `\x:real^3. transp (Q:real^3^3) ** x`;
                 `y:real^3`] MTR_ISOMETRY_RM_NORM) THEN
  ASM_SIMP_TAC[STDS_ROT_ISOMETRY; P2C_EUCLID_FACTS; STDS_RIEM_UNIV_EQ; IN_UNIV]);;

let STDS_PARTIAL_ROT = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) (Q:real^3^3).
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ orthogonal_matrix Q /\ det Q = &1
     ==> p3_partial_std g0 te (\t x. transp Q ** G t (Q ** x) ** Q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < te ==> metric_field (:real^3) ((G:real->real^3->real^3^3) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM STDS_RIEM_UNIV_EQ] THEN
    MATCH_MP_TAC STDS_PARTIAL_RIEM THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `te:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `p3_partial_std g0 te (G:real->real^3->real^3^3)` THEN
  REWRITE_TAC[p3_partial_std] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC STDS_RFF_ROT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC STDS_COMPLETE_ROT THEN REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `t1:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t1:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN EXISTS_TAC `K:real` THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`] THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `metric_field (:real^3) ((G:real->real^3->real^3^3) t)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`(G:real->real^3->real^3^3) t`; `Q:real^3^3`; `x:real^3`]
                  STDS_RMNORM_ROT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* MT Thm 12.5 (4) for every partial standard flow, hence for Gs.            *)

let STDS_PARTIAL_SO3 = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) (Q:real^3^3) t x.
     P2C_STD_UNIQUE_STATEMENT /\ p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\
     orthogonal_matrix Q /\ det Q = &1 /\ &0 <= t /\ t < te
     ==> transp Q ** G t (Q ** x) ** Q = G t x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `G:real->real^3->real^3^3`;
                `Q:real^3^3`] STDS_PARTIAL_ROT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `P2C_STD_UNIQUE_STATEMENT` THEN REWRITE_TAC[P2C_STD_UNIQUE_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `te:real`; `G:real->real^3->real^3^3`;
     `\t x. transp (Q:real^3^3) ** (G:real->real^3->real^3^3) t (Q ** x) ** Q`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:real^3`]) THEN
  ASM_REWRITE_TAC[]);;

let STDS_GS_SO3 = prove
 (`!g0 A0 (Q:real^3^3) t x.
     P2C_STD_PARTIAL_EXISTS_STATEMENT /\ P2C_STD_UNIQUE_STATEMENT /\
     P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\ p3_std_initial g0 A0 /\
     orthogonal_matrix Q /\ det Q = &1 /\ &0 <= t /\ t < stds_tm g0
     ==> transp Q ** stds_gs g0 t (Q ** x) ** Q = stds_gs g0 t x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC STDS_PARTIAL_SO3 THEN
  MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`; `stds_tm g0`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_FLOW) THEN
  ASM_SIMP_TAC[p3_std_flow]);;

(* ------------------------------------------------------------------------- *)
(* The rotational theory of pc_p3_s13rot for every                          *)
(* SO(3)-invariant metric field on real^3, not only for standard initial    *)
(* metrics: the radial form with the coefficients a(r), b(r), their         *)
(* smoothness and positivity, the radial distance rho and the radial        *)
(* segment, and the sectional curvature away from the tip in terms of a, b  *)
(* and their derivatives (K_tan and K_rad as functions of the Euclidean      *)
(* radius r).  The lemmas below are the P3S_ lemmas of pc_p3_s13rot named   *)
(* in the comment before each, with the hypothesis p3_std_initial g0 A0     *)
(* weakened to stds_rotm g0 (their proofs use only the metric field and the *)
(* rotation invariance).  The definitions p3s_rad_a,                        *)
(* p3s_rad_b, p3s_rad_rho, p3s_rs_* and the hypothesis-free P3S_ lemmas are *)
(* used as they are.                                                         *)
(* ------------------------------------------------------------------------- *)

let stds_rotm = new_definition
 `stds_rotm (g:real^3->real^3^3) <=>
    metric_field (:real^3) g /\
    (!Q x. orthogonal_matrix Q /\ det Q = &1 ==> transp Q ** g (Q ** x) ** Q = g x)`;;

(* From P3S_STD_METRIC_FIELD (pc_p3_s13rot). *)
let STDS_RT_METRIC_FIELD = prove
 (`!g0. stds_rotm g0 ==> metric_field (:real^3) g0`,
  SIMP_TAC[stds_rotm]);;

(* From P3S_STD_SYM (pc_p3_s13rot). *)
let STDS_RT_STD_SYM = prove
 (`!g0 x. stds_rotm g0
             ==> (g0 x:real^3^3)$2$1 = g0 x$1$2 /\ (g0 x:real^3^3)$3$1 = g0 x$1$3 /\
                 (g0 x:real^3^3)$3$2 = g0 x$2$3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP STDS_RT_METRIC_FIELD) THEN
  REWRITE_TAC[metric_field; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `x:real^3` o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o AP_TERM `\A:real^3^3. A$1$2, A$1$3, A$2$3`) THEN
  SIMP_TAC[transp; LAMBDA_BETA; DIMINDEX_3; ARITH; PAIR_EQ]);;

(* From P3S_STD_POS (pc_p3_s13rot). *)
let STDS_RT_STD_POS = prove
 (`!g0 x v. stds_rotm g0 /\ ~(v = vec 0) ==> &0 < v dot (g0 x ** v)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP STDS_RT_METRIC_FIELD) THEN
  REWRITE_TAC[metric_field; IN_UNIV] THEN ASM_MESON_TAC[]);;

(* From P3S_ROT_FIX (pc_p3_s13rot). *)
let STDS_RT_ROT_FIX = prove
 (`!g0 Q x. stds_rotm g0 /\ orthogonal_matrix Q /\ det Q = &1 /\
               Q ** x = x
               ==> transp Q ** g0 x ** Q = g0 x`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `stds_rotm g0` THEN REWRITE_TAC[stds_rotm] THEN
  DISCH_THEN(MP_TAC o SPECL [`Q:real^3^3`; `x:real^3`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

(* From P3S_ROT_DIAG (pc_p3_s13rot). *)
let STDS_RT_ROT_DIAG = prove
 (`!g0 r. stds_rotm g0
             ==> (g0 (r % basis 1):real^3^3)$1$2 = &0 /\ g0 (r % basis 1)$1$3 = &0 /\
                 g0 (r % basis 1)$2$1 = &0 /\ g0 (r % basis 1)$3$1 = &0 /\
                 g0 (r % basis 1)$2$3 = &0 /\ g0 (r % basis 1)$3$2 = &0 /\
                 g0 (r % basis 1)$3$3 = g0 (r % basis 1)$2$2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `r % basis 1:real^3`] STDS_RT_STD_SYM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC P3S_ROTS THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `Q1:real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M1")))))
    (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `Q2:real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M2"))))) (K ALL_TAC))) THEN
  USE_THEN "M1" (MP_TAC o SPEC `(g0:real^3->real^3^3) (r % basis 1)`) THEN
  USE_THEN "M2" (MP_TAC o SPEC `(g0:real^3->real^3^3) (r % basis 1)`) THEN
  SUBGOAL_THEN `transp Q1 ** (g0:real^3->real^3^3) (r % basis 1) ** Q1 =
                g0 (r % basis 1) /\
                transp Q2 ** (g0:real^3->real^3^3) (r % basis 1) ** Q2 =
                g0 (r % basis 1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC STDS_RT_ROT_FIX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* From P3S_ROT_TIP0 (pc_p3_s13rot). *)
let STDS_RT_ROT_TIP0 = prove
 (`!g0. stds_rotm g0
           ==> (g0 (vec 0):real^3^3)$2$2 = g0 (vec 0)$1$1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC P3S_ROTS THEN
  DISCH_THEN(X_CHOOSE_THEN `Q3:real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M3")))) o
    CONJUNCT2 o CONJUNCT2) THEN
  USE_THEN "M3" MATCH_MP_TAC THEN MATCH_MP_TAC STDS_RT_ROT_FIX THEN
  ASM_REWRITE_TAC[]);;

(* From P3S_ROT_E1_BIL (pc_p3_s13rot). *)
let STDS_RT_ROT_E1_BIL = prove
 (`!g0 r (w:real^3) v.
     stds_rotm g0
     ==> w dot (g0 (r % basis 1) ** v) =
         p3s_rad_a g0 r * w$1 * v$1 + p3s_rad_b g0 r * (w dot v - w$1 * v$1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_ROT_DIAG) THEN
  ASM_REWRITE_TAC[P3S_RAD_AB_ENTRY] THEN STRIP_TAC THEN
  SIMP_TAC[DOT_3; matrix_vector_mul; LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* From P3S_ROT_BIL (pc_p3_s13rot). *)
let STDS_RT_ROT_BIL = prove
 (`!g0 (x:real^3) w v.
     stds_rotm g0 /\ ~(x = vec 0)
     ==> w dot (g0 x ** v) =
         p3s_rad_a g0 (norm x) * (w dot x) * (v dot x) / norm x pow 2 +
         p3s_rad_b g0 (norm x) * (w dot v - (w dot x) * (v dot x) / norm x pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis 1:real^3`; `inv(norm x) % x:real^3`] ROTATION_EXISTS_1) THEN
  ANTS_TAC THENL
   [SIMP_TAC[DIMINDEX_3; ARITH; NORM_BASIS; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Q = matrix(f:real^3->real^3)` THEN
  SUBGOAL_THEN `linear(f:real^3->real^3) /\ orthogonal_matrix(Q:real^3^3)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX]; ALL_TAC] THEN
  SUBGOAL_THEN `(Q:real^3^3) ** basis 1 = inv(norm x) % x` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN ASM_SIMP_TAC[MATRIX_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `(Q:real^3^3) ** (norm(x:real^3) % basis 1) = x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp (Q:real^3^3) ** (g0:real^3->real^3^3) x ** Q = g0 (norm x % basis 1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `stds_rotm g0` THEN REWRITE_TAC[stds_rotm] THEN
    DISCH_THEN(MP_TAC o SPECL [`Q:real^3^3`; `norm(x:real^3) % basis 1:real^3`] o
               CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. (Q:real^3^3) ** transp Q ** z = z` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; ORTHOGONAL_MATRIX_TRANSP_RMUL;
                 MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:real^3) dot ((g0:real^3->real^3^3) x ** v) =
    (transp (Q:real^3^3) ** w) dot (g0 (norm x % basis 1) ** (transp Q ** v))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `transp (Q:real^3^3) ** (g0:real^3->real^3^3) x ** Q = g0 (norm x % basis 1)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `norm(x:real^3)`;
                 `transp (Q:real^3^3) ** (w:real^3)`;
                 `transp (Q:real^3^3) ** (v:real^3)`] STDS_RT_ROT_E1_BIL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!z:real^3. (transp (Q:real^3^3) ** z)$1 = inv(norm(x:real^3)) * (x dot z)`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `z:real^3` THEN
    SUBGOAL_THEN `(transp (Q:real^3^3) ** (z:real^3))$1 = basis 1 dot (transp Q ** z)`
    SUBST1_TAC THENL [SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL; DOT_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(transp (Q:real^3^3) ** (w:real^3)) dot (transp Q ** (v:real^3)) = w dot v`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL]; ALL_TAC] THEN
  REWRITE_TAC[DOT_SYM] THEN
  UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD);;

(* From P3S_ROT_FORM (pc_p3_s13rot). *)
let STDS_RT_ROT_FORM = prove
 (`!g0 (x:real^3) v.
  stds_rotm g0 /\ ~(x = vec 0)
  ==> v dot (g0 x ** v) =
      p3s_rad_a g0 (norm x) * (v dot x) pow 2 / norm x pow 2 +
      p3s_rad_b g0 (norm x) * (v dot v - (v dot x) pow 2 / norm x pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `x:real^3`; `v:real^3`; `v:real^3`]
         STDS_RT_ROT_BIL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING);;

(* From P3S_ROT_TIP (pc_p3_s13rot). *)
let STDS_RT_ROT_TIP = prove
 (`!g0 (w:real^3) v. stds_rotm g0
                        ==> w dot (g0 (vec 0) ** v) = p3s_rad_a g0 (&0) * (w dot v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `&0`; `w:real^3`; `v:real^3`]
         STDS_RT_ROT_E1_BIL) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `p3s_rad_b g0 (&0) = p3s_rad_a g0 (&0)` SUBST1_TAC THENL
   [REWRITE_TAC[P3S_RAD_AB_ENTRY; VECTOR_MUL_LZERO] THEN
    MATCH_MP_TAC STDS_RT_ROT_TIP0 THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* From P3S_ROT_AB (pc_p3_s13rot). *)
let STDS_RT_ROT_AB = prove
 (`!g0. stds_rotm g0
  ==> smooth_map_on (:real^1) (lift o p3s_rad_a g0 o drop) /\
      smooth_map_on (:real^1) (lift o p3s_rad_b g0 o drop) /\
      (!r. &0 < p3s_rad_a g0 r /\ &0 < p3s_rad_b g0 r) /\
      p3s_rad_a g0 (&0) = p3s_rad_b g0 (&0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP STDS_RT_METRIC_FIELD) THEN
  SUBGOAL_THEN
   `!k. smooth_map_on (:real^1)
          (\t. lift(basis k dot ((g0:real^3->real^3^3) (drop t % basis 1) ** basis k)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `(\t. lift(basis k dot ((g0:real^3->real^3^3) (drop t % basis 1) ** basis k))) =
      (\x. lift(basis k dot (g0 x ** basis k))) o (\t:real^1. drop t % basis 1)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN REWRITE_TAC[OPEN_UNIV] THEN
      REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC LRG_DOT_METRIC_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; p3s_rad_a];
    FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; p3s_rad_b];
    GEN_TAC THEN REWRITE_TAC[p3s_rad_a; p3s_rad_b] THEN CONJ_TAC THEN
    MATCH_MP_TAC STDS_RT_STD_POS THEN ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH];
    REWRITE_TAC[P3S_RAD_AB_ENTRY; VECTOR_MUL_LZERO] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC STDS_RT_ROT_TIP0 THEN ASM_REWRITE_TAC[]]);;

(* From P3S_STD_POS_LE (pc_p3_s13rot). *)
let STDS_RT_STD_POS_LE = prove
 (`!g0 x v. stds_rotm g0 ==> &0 <= v dot (g0 x ** v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC STDS_RT_STD_POS THEN
  ASM_REWRITE_TAC[]);;

(* From P3S_SQRTA_SMOOTH (pc_p3_s13rot). *)
let STDS_RT_SQRTA_SMOOTH = prove
 (`!g0. stds_rotm g0
           ==> smooth_map_on (:real^1) (lift o (\u. sqrt(p3s_rad_a g0 u)) o drop)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDS_RT_ROT_AB) THEN
  MP_TAC(ISPECL [`(:real^1)`; `lift o p3s_rad_a g0 o drop`] SMOOTH_MAP_ON_LIFT_SQRT) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; o_THM; LIFT_DROP] THEN
  REWRITE_TAC[o_DEF]);;

(* From P3S_RHO_DERIV_WITHIN (pc_p3_s13rot). *)
let STDS_RT_RHO_DERIV_WITHIN = prove
 (`!g0 R r. stds_rotm g0 /\ r IN real_interval[&0,R]
               ==> (p3s_rad_rho g0 has_real_derivative sqrt(p3s_rad_a g0 r))
                   (atreal r within real_interval[&0,R])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P3S_RHO_ALT] THEN
  MP_TAC(ISPECL [`\u. sqrt(p3s_rad_a g0 u)`; `&0`; `R:real`]
         REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC P2C_S1_CONTINUOUS THEN MATCH_MP_TAC STDS_RT_SQRTA_SMOOTH THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[]]);;

(* From P3S_RHO_DERIV (pc_p3_s13rot). *)
let STDS_RT_RHO_DERIV = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r
             ==> (p3s_rad_rho g0 has_real_derivative sqrt(p3s_rad_a g0 r)) (atreal r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P3S_RHO_ALT] THEN
  MP_TAC(ISPECL [`\u. sqrt(p3s_rad_a g0 u)`; `&0`; `r:real`] P2C_INTEGRAL_DERIV_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC P2C_S1_CONTINUOUS THEN MATCH_MP_TAC STDS_RT_SQRTA_SMOOTH THEN
  ASM_REWRITE_TAC[]);;

(* From P3S_RHO_CONT (pc_p3_s13rot). *)
let STDS_RT_RHO_CONT = prove
 (`!g0 R. stds_rotm g0
             ==> p3s_rad_rho g0 real_continuous_on real_interval[&0,R]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[real_differentiable_on] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `sqrt(p3s_rad_a g0 x)` THEN
  MATCH_MP_TAC STDS_RT_RHO_DERIV_WITHIN THEN ASM_REWRITE_TAC[]);;

(* From P3S_RHO_STRICT (pc_p3_s13rot). *)
let STDS_RT_RHO_STRICT = prove
 (`!g0 r1 r2. stds_rotm g0 /\ &0 <= r1 /\ r1 < r2
                 ==> p3s_rad_rho g0 r1 < p3s_rad_rho g0 r2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP THEN
  EXISTS_TAC `\r. sqrt(p3s_rad_a g0 r)` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[&0,r2]` THEN CONJ_TAC THENL
     [MATCH_MP_TAC STDS_RT_RHO_DERIV_WITHIN THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDS_RT_ROT_AB) THEN ASM_REWRITE_TAC[]]);;

(* From P3S_RHO_POS_LE (pc_p3_s13rot). *)
let STDS_RT_RHO_POS_LE = prove
 (`!g0 r. stds_rotm g0 /\ &0 <= r ==> &0 <= p3s_rad_rho g0 r`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r = &0` THEN
  ASM_REWRITE_TAC[P3S_RHO_0; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `g0:real^3->real^3^3` P3S_RHO_0)] THEN
  MATCH_MP_TAC STDS_RT_RHO_STRICT THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC);;

(* From P3S_RHO_LT_EQ (pc_p3_s13rot). *)
let STDS_RT_RHO_LT_EQ = prove
 (`!g0 r1 r2. stds_rotm g0 /\ &0 <= r1 /\ &0 <= r2
                 ==> (p3s_rad_rho g0 r1 < p3s_rad_rho g0 r2 <=> r1 < r2) /\
                     (p3s_rad_rho g0 r1 <= p3s_rad_rho g0 r2 <=> r1 <= r2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s t. &0 <= s /\ s < t ==> p3s_rad_rho g0 s < p3s_rad_rho g0 t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC STDS_RT_RHO_STRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_NOT_LT; REAL_LT_REFL; REAL_LE_LT]);;

(* From P3S_SEG_FORM (pc_p3_s13rot). *)
let STDS_RT_SEG_FORM = prove
 (`!g0 (x:real^3) t.
     stds_rotm g0 /\ &0 <= t
     ==> x dot (g0 (t % x) ** x) = p3s_rad_a g0 (t * norm x) * norm x pow 2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[DOT_LZERO; NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_MUL_LZERO] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `x:real^3`; `x:real^3`]
           STDS_RT_ROT_TIP) THEN
    ASM_REWRITE_TAC[NORM_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `t % x:real^3`; `x:real^3`]
         STDS_RT_ROT_FORM) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NORM_MUL; DOT_RMUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `~(norm(x:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `~(t = &0)` THEN CONV_TAC REAL_FIELD);;

(* From P3S_RAD_SEGMENT (pc_p3_s13rot). *)
let STDS_RT_RAD_SEGMENT = prove
 (`!g0 (x:real^3).
     stds_rotm g0
     ==> mfd_length (open_set_atlas (:real^3)) g0 (\t. t % x) (&0) (&1) =
         p3s_rad_rho g0 (norm x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`;
                 `\t:real. t % (x:real^3)`; `&0`; `&1`] MFD_LENGTH_OPEN_SET_ATLAS) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; P2C_SEGMENT_C1] THEN
  DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS
   `real_integral (real_interval[&0,&1])
      (\t. sqrt(p3s_rad_a g0 (t * norm(x:real^3))) * norm x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[P2C_SEGMENT_VD] THEN
    SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `x:real^3`; `t:real`]
           STDS_RT_SEG_FORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SQRT_MUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; REAL_MUL_RZERO; REAL_INTEGRAL_0; P3S_RHO_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. p3s_rad_rho g0 (t * norm(x:real^3))`;
                 `\t. sqrt(p3s_rad_a g0 (t * norm(x:real^3))) * norm x`;
                 `&0`; `&1`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\t. t * norm(x:real^3)`; `p3s_rad_rho g0`; `norm(x:real^3)`;
                   `sqrt(p3s_rad_a g0 (t * norm(x:real^3)))`; `t:real`;
                   `real_interval[&0,&1]`] REAL_DIFF_CHAIN_WITHIN) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\t:real. t`; `&1`; `norm(x:real^3)`; `t:real`;
                     `real_interval[&0,&1]`] HAS_REAL_DERIVATIVE_RMUL_WITHIN) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_LID];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `real_interval[&0,norm(x:real^3)]` THEN CONJ_TAC THENL
       [MATCH_MP_TAC STDS_RT_RHO_DERIV_WITHIN THEN ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]]];
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; P3S_RHO_0; REAL_SUB_RZERO]]);;

(* From P3S_RHO_SMOOTH (pc_p3_s13rot). *)
let STDS_RT_RHO_SMOOTH = prove
 (`!g0. stds_rotm g0
           ==> smooth_map_on {s | &0 < drop s} (lift o p3s_rad_rho g0 o drop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_REAL_DERIVATIVE_1D THEN
  EXISTS_TAC `\u. sqrt(p3s_rad_a g0 u)` THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC STDS_RT_RHO_DERIV THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2C_S1_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC STDS_RT_SQRTA_SMOOTH THEN
    ASM_REWRITE_TAC[]]);;

(* From P3S_AB_DERIVS (pc_p3_s13rot). *)
let STDS_RT_AB_DERIVS = prove
 (`!g0. stds_rotm g0
           ==> (!x. (p3s_rad_a g0 has_real_derivative
                     real_derivative (p3s_rad_a g0) x) (atreal x)) /\
               (!x. (real_derivative (p3s_rad_a g0) has_real_derivative
                     real_derivative (real_derivative (p3s_rad_a g0)) x) (atreal x)) /\
               (!x. (p3s_rad_b g0 has_real_derivative
                     real_derivative (p3s_rad_b g0) x) (atreal x)) /\
               (!x. (real_derivative (p3s_rad_b g0) has_real_derivative
                     real_derivative (real_derivative (p3s_rad_b g0)) x) (atreal x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDS_RT_ROT_AB) THEN
  MP_TAC(ISPECL [`(:real^1)`; `p3s_rad_a g0`] P3S_S1_RDERIV) THEN
  MP_TAC(ISPECL [`(:real^1)`; `p3s_rad_b g0`] P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`(:real^1)`; `real_derivative (p3s_rad_a g0)`] P3S_S1_RDERIV);
    MP_TAC(ISPECL [`(:real^1)`; `real_derivative (p3s_rad_b g0)`] P3S_S1_RDERIV)] THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV]);;

(* From P3S_RS_C_DERIV (pc_p3_s13rot). *)
let STDS_RT_RS_C_DERIV = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r
             ==> (p3s_rs_c g0 has_real_derivative p3s_rs_dc g0 r) (atreal r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3s_rs_c g0 = (\r. (p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 2)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3s_rs_c]; ALL_TAC] THEN
  MP_TAC(DISCH_ALL(p3s_rdiff (CONJUNCTS(UNDISCH(SPEC_ALL STDS_RT_AB_DERIVS)))
    `((\r. (p3s_rad_a (g0:real^3->real^3^3) r - p3s_rad_b g0 r) / r pow 2)
      has_real_derivative f') (atreal r)`)) THEN
  ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[p3s_rs_dc] THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

(* From P3S_G0_BIL2 (pc_p3_s13rot). *)
let STDS_RT_G0_BIL2 = prove
 (`!g0 (z:real^3) w v.
     stds_rotm g0 /\ ~(z = vec 0)
     ==> w dot (g0 z ** v) =
         p3s_rad_b g0 (norm z) * (w dot v) +
         p3s_rs_c g0 (norm z) * (z dot w) * (z dot v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `z:real^3`; `w:real^3`; `v:real^3`]
         STDS_RT_ROT_BIL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p3s_rs_c; DOT_SYM] THEN
  SUBGOAL_THEN `~(norm(z:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD]);;

(* From P3S_G0_MDERIV (pc_p3_s13rot). *)
let STDS_RT_G0_MDERIV = prove
 (`!g0 (y:real^3) h w v.
     stds_rotm g0 /\ ~(y = vec 0)
     ==> w dot (mderiv g0 y h ** v) =
         (real_derivative (p3s_rad_b g0) (norm y) / norm y) * (y dot h) * (w dot v) +
         (p3s_rs_dc g0 (norm y) / norm y) * (y dot h) * (y dot w) * (y dot v) +
         p3s_rs_c g0 (norm y) * ((h dot w) * (y dot v) + (y dot w) * (h dot v))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP STDS_RT_METRIC_FIELD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDS_RT_AB_DERIVS) THEN
  SUBGOAL_THEN `(vectorize o (g0:real^3->real^3^3)) differentiable at y` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF; IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `y:real^3`; `w:real^3`; `v:real^3`]
         LRG_HAS_DERIVATIVE_GDOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "D1") THEN
  SUBGOAL_THEN
   `((\z. lift(p3s_rad_b g0 (norm z) * ((w:real^3) dot v) +
              p3s_rs_c g0 (norm z) * (z dot w) * (z dot v))) has_derivative
     (\h. lift((real_derivative (p3s_rad_b g0) (norm y) / norm y) * (y dot h) * (w dot v) +
               (p3s_rs_dc g0 (norm y) / norm y) * (y dot h) * (y dot w) * (y dot v) +
               p3s_rs_c g0 (norm y) * ((h dot w) * (y dot v) + (y dot w) * (h dot v)))))
    (at y)`
  (LABEL_TAC "D2") THENL
   [MP_TAC(ISPECL [`p3s_rad_b g0`; `real_derivative (p3s_rad_b g0) (norm(y:real^3))`;
                   `y:real^3`] P3S_RADIAL_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o ISPEC `(w:real^3) dot v` o MATCH_MP HAS_DERIVATIVE_CMUL) THEN
    MP_TAC(ISPECL [`p3s_rs_c g0`; `p3s_rs_dc g0 (norm(y:real^3))`; `y:real^3`]
           P3S_RADIAL_DERIV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC STDS_RT_RS_C_DERIV THEN
      ASM_REWRITE_TAC[NORM_POS_LT];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o BETA_RULE o SPECL [`w:real^3`; `v:real^3`] o
               MATCH_MP P3S_HAS_DERIV_QUAD) THEN
    REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP HAS_DERIVATIVE_ADD) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift((w:real^3) dot ((g0:real^3->real^3^3) z ** v))) has_derivative
     (\h. lift((real_derivative (p3s_rad_b g0) (norm y) / norm y) * (y dot h) * (w dot v) +
               (p3s_rs_dc g0 (norm y) / norm y) * (y dot h) * (y dot w) * (y dot v) +
               p3s_rs_c g0 (norm y) * ((h dot w) * (y dot v) + (y dot w) * (h dot v)))))
    (at y)`
  (LABEL_TAC "D3") THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. lift(p3s_rad_b g0 (norm z) * ((w:real^3) dot v) +
                         p3s_rs_c g0 (norm z) * (z dot w) * (z dot v))` THEN
    EXISTS_TAC `norm(y:real^3)` THEN USE_THEN "D2" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[NORM_POS_LT] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC STDS_RT_G0_BIL2 THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `dist(z:real^3,y) < norm y` THEN
    ASM_REWRITE_TAC[DIST_0; DIST_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "D1" (fun d1 -> USE_THEN "D3" (fun d3 ->
    MP_TAC(MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT (CONJ d1 d3)))) THEN
  DISCH_THEN(MP_TAC o C AP_THM `h:real^3`) THEN REWRITE_TAC[LIFT_EQ]);;

(* From P3S_G0_CHRISTOFFEL (pc_p3_s13rot). *)
let STDS_RT_G0_CHRISTOFFEL = prove
 (`!g0 (z:real^3) a b.
     stds_rotm g0 /\ ~(z = vec 0)
     ==> christoffel g0 z a b =
         p3s_rs_m1 g0 (norm z) % ((z dot a) % b + (z dot b) % a) +
         (p3s_rs_m2 g0 (norm z) * (a dot b) +
          p3s_rs_m3 g0 (norm z) * (z dot a) * (z dot b)) % z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP STDS_RT_METRIC_FIELD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDS_RT_ROT_AB) THEN
  SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p3s_rad_b g0 (norm(z:real^3)) + p3s_rs_c g0 (norm z) * (z dot z) =
    p3s_rad_a g0 (norm z) /\
    p3s_rad_b g0 (norm(z:real^3)) + p3s_rs_c g0 (norm z) * norm z pow 2 =
    p3s_rad_a g0 (norm z)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p3s_rs_c; GSYM NORM_POW_2] THEN
    UNDISCH_TAC `&0 < norm(z:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(:real^3)`; `z:real^3`;
                 `p3s_rad_b g0 (norm(z:real^3))`; `p3s_rs_c g0 (norm(z:real^3))`;
                 `real_derivative (p3s_rad_b g0) (norm(z:real^3)) / norm z`;
                 `p3s_rs_dc g0 (norm(z:real^3)) / norm z`; `a:real^3`; `b:real^3`]
                P3S_RS_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC STDS_RT_G0_BIL2 THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN MATCH_MP_TAC STDS_RT_G0_MDERIV THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[p3s_rs_m1; p3s_rs_m2; p3s_rs_m3] THEN ASM_REWRITE_TAC[]);;

(* From P3S_RS_SIDE (pc_p3_s13rot). *)
let STDS_RT_RS_SIDE = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r
             ==> ~(r = &0) /\ ~(r pow 2 = &0) /\ ~(r pow 3 = &0) /\
                 ~(p3s_rad_b g0 r = &0) /\ ~(&2 * p3s_rad_b g0 r = &0) /\
                 ~(p3s_rad_a g0 r = &0) /\
                 p3s_rad_b g0 r + (p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 2 * r pow 2 =
                 p3s_rad_a g0 r /\
                 ~(p3s_rad_b g0 r + (p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 2 * r pow 2 =
                   &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDS_RT_ROT_AB) THEN
  SUBGOAL_THEN `&0 < p3s_rad_a g0 r /\ &0 < p3s_rad_b g0 r` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(r pow 2 = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ; REAL_DIV_RMUL; REAL_ENTIRE] THEN
  ASM_REAL_ARITH_TAC);;

(* From p3s_rs_dthm (pc_p3_s13rot). *)
let stds_rt_rs_dthm i =
  let eq = List.nth [P3S_RS_M1_EQ; P3S_RS_M2_EQ; P3S_RS_M3_EQ] (i - 1) in
  let lam = rhs(concl(SPEC `g0:real^3->real^3^3` eq)) in
  let tm = mk_comb(mk_comb(mk_comb(
             `(has_real_derivative):(real->real)->real->(real)net->bool`, lam),
             `f':real`), `atreal r`) in
  DISCH_ALL(p3s_rdiff (CONJUNCTS(UNDISCH(SPEC_ALL STDS_RT_AB_DERIVS))) tm);;

(* From P3S_RS_M_DERIVS (pc_p3_s13rot). *)
let STDS_RT_RS_M_DERIVS = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r
             ==> (p3s_rs_m1 g0 has_real_derivative real_derivative (p3s_rs_m1 g0) r)
                 (atreal r) /\
                 (p3s_rs_m2 g0 has_real_derivative real_derivative (p3s_rs_m2 g0) r)
                 (atreal r) /\
                 (p3s_rs_m3 g0 has_real_derivative real_derivative (p3s_rs_m3 g0) r)
                 (atreal r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_RS_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P3S_RS_M1_EQ; P3S_RS_M2_EQ; P3S_RS_M3_EQ] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(stds_rt_rs_dthm 1); MP_TAC(stds_rt_rs_dthm 2); MP_TAC(stds_rt_rs_dthm 3)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o MATCH_MP P3S_HAS_RD));;

(* From P3S_RS_RELATION (pc_p3_s13rot). *)
let STDS_RT_RS_RELATION = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r
   ==> (real_derivative (p3s_rs_m1 g0) r / r - p3s_rs_m1 g0 r pow 2 - p3s_rs_m3 g0 r -
        p3s_rs_m1 g0 r * p3s_rs_m3 g0 r * r pow 2) * p3s_rad_b g0 r =
       (p3s_rs_m3 g0 r - p3s_rs_m2 g0 r pow 2 - real_derivative (p3s_rs_m2 g0) r / r -
        p3s_rs_m2 g0 r * p3s_rs_m3 g0 r * r pow 2) *
       (p3s_rad_b g0 r + p3s_rs_c g0 r * r pow 2) +
       (p3s_rs_m1 g0 r - p3s_rs_m2 g0 r - p3s_rs_m1 g0 r * p3s_rs_m2 g0 r * r pow 2) *
       p3s_rs_c g0 r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_RS_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(stds_rt_rs_dthm 1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
  REWRITE_TAC[GSYM P3S_RS_M1_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(stds_rt_rs_dthm 2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
  REWRITE_TAC[GSYM P3S_RS_M2_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p3s_rs_m1; p3s_rs_m2; p3s_rs_m3; p3s_rs_c; p3s_rs_dc] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC
   [`aa = p3s_rad_a (g0:real^3->real^3^3) r`; `bb = p3s_rad_b (g0:real^3->real^3^3) r`;
    `a1 = real_derivative (p3s_rad_a (g0:real^3->real^3^3)) r`;
    `b1 = real_derivative (p3s_rad_b (g0:real^3->real^3^3)) r`;
    `b2 = real_derivative (real_derivative (p3s_rad_b (g0:real^3->real^3^3))) r`] THEN
  UNDISCH_TAC `~(r = &0)` THEN UNDISCH_TAC `~(aa = &0)` THEN UNDISCH_TAC `~(bb = &0)` THEN
  CONV_TAC REAL_FIELD);;

(* From P3S_G0_RIEMANN (pc_p3_s13rot). *)
let STDS_RT_G0_RIEMANN = prove
 (`!g0 (y:real^3) a v w.
     stds_rotm g0 /\ ~(y = vec 0)
     ==> lriemann g0 y a v w =
         (p3s_rs_m1 g0 (norm y) - p3s_rs_m2 g0 (norm y) -
          p3s_rs_m1 g0 (norm y) * p3s_rs_m2 g0 (norm y) * (y dot y)) %
         ((a dot w) % v - (v dot w) % a) +
         (real_derivative (p3s_rs_m1 g0) (norm y) / norm y - p3s_rs_m1 g0 (norm y) pow 2 -
          p3s_rs_m3 g0 (norm y) -
          p3s_rs_m1 g0 (norm y) * p3s_rs_m3 g0 (norm y) * (y dot y)) %
         (((y dot a) * (y dot w)) % v - ((y dot v) * (y dot w)) % a) +
         (p3s_rs_m3 g0 (norm y) - p3s_rs_m2 g0 (norm y) pow 2 -
          real_derivative (p3s_rs_m2 g0) (norm y) / norm y -
          p3s_rs_m2 g0 (norm y) * p3s_rs_m3 g0 (norm y) * (y dot y)) %
         (((y dot v) * (a dot w) - (y dot a) * (v dot w)) % y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `norm(y:real^3)`] STDS_RT_RS_M_DERIVS) THEN
  ASM_REWRITE_TAC[NORM_POS_LT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(:real^3) DELETE vec 0`;
                 `\z:real^3. p3s_rs_m1 g0 (norm z)`; `\z:real^3. p3s_rs_m2 g0 (norm z)`;
                 `\z:real^3. p3s_rs_m3 g0 (norm z)`;
                 `real_derivative (p3s_rs_m1 g0) (norm(y:real^3)) / norm y`;
                 `real_derivative (p3s_rs_m2 g0) (norm(y:real^3)) / norm y`;
                 `real_derivative (p3s_rs_m3 g0) (norm(y:real^3)) / norm y`;
                 `y:real^3`; `a:real^3`; `v:real^3`; `w:real^3`] P3S_RAD3_RIEMANN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[P3S_OPEN_PUNCT; IN_DELETE; IN_UNIV] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC STDS_RT_G0_CHRISTOFFEL THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3S_RADIAL_DERIV THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC P3S_RADIAL_DERIV THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC P3S_RADIAL_DERIV THEN ASM_REWRITE_TAC[ETA_AX]]);;

(* From P3S_G0_SECTIONAL (pc_p3_s13rot). *)
let STDS_RT_G0_SECTIONAL = prove
 (`!g0 (y:real^3) u v.
     stds_rotm g0 /\ ~(y = vec 0)
     ==> mfd_sectional (open_set_atlas (:real^3)) g0 y u v =
         (p3s_rs_ktan g0 (norm y) * p3s_rad_b g0 (norm y) pow 2 *
            ((u dot u - (u dot y) pow 2 / norm y pow 2) *
             (v dot v - (v dot y) pow 2 / norm y pow 2) -
             (u dot v - (u dot y) * (v dot y) / norm y pow 2) pow 2) +
          p3s_rs_krad g0 (norm y) *
            ((u dot (g0 y ** u)) * (v dot (g0 y ** v)) - (u dot (g0 y ** v)) pow 2 -
             p3s_rad_b g0 (norm y) pow 2 *
             ((u dot u - (u dot y) pow 2 / norm y pow 2) *
              (v dot v - (v dot y) pow 2 / norm y pow 2) -
              (u dot v - (u dot y) * (v dot y) / norm y pow 2) pow 2))) /
         ((u dot (g0 y ** u)) * (v dot (g0 y ** v)) - (u dot (g0 y ** v)) pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2C_OPEN_SET_MFD_SECTIONAL] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `norm(y:real^3)`] STDS_RT_RS_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`;
                 `p3s_rad_b g0 (norm(y:real^3))`; `p3s_rs_c g0 (norm(y:real^3))`;
                 `p3s_rs_m1 g0 (norm y) - p3s_rs_m2 g0 (norm y) -
                  p3s_rs_m1 g0 (norm y) * p3s_rs_m2 g0 (norm y) * ((y:real^3) dot y)`;
                 `real_derivative (p3s_rs_m1 g0) (norm y) / norm y -
                  p3s_rs_m1 g0 (norm y) pow 2 - p3s_rs_m3 g0 (norm y) -
                  p3s_rs_m1 g0 (norm y) * p3s_rs_m3 g0 (norm y) * ((y:real^3) dot y)`;
                 `p3s_rs_m3 g0 (norm y) - p3s_rs_m2 g0 (norm y) pow 2 -
                  real_derivative (p3s_rs_m2 g0) (norm y) / norm y -
                  p3s_rs_m2 g0 (norm y) * p3s_rs_m3 g0 (norm y) * ((y:real^3) dot y)`]
                P3S_RS_SECTIONAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC STDS_RT_G0_BIL2 THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN MATCH_MP_TAC STDS_RT_G0_RIEMANN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM NORM_POW_2] THEN MATCH_MP_TAC STDS_RT_RS_RELATION THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[p3s_rs_ktan; p3s_rs_krad; GSYM NORM_POW_2] THEN
  REWRITE_TAC[real_div; REAL_MUL_AC]);;

(* From p3s_rs_hthm (pc_p3_s13rot). *)
let stds_rt_rs_hthm () =
  DISCH_ALL(p3s_rdiff (CONJUNCTS(UNDISCH(SPEC_ALL STDS_RT_AB_DERIVS)))
    `((\r. r * sqrt(p3s_rad_b (g0:real^3->real^3^3) r)) has_real_derivative f')
     (atreal r)`);;

(* From p3s_rs_f1thm (pc_p3_s13rot). *)
let stds_rt_rs_f1thm () =
  let lam = rhs(concl(SPEC `g0:real^3->real^3^3` P3S_RS_F1_EQ)) in
  let tm = mk_comb(mk_comb(mk_comb(
             `(has_real_derivative):(real->real)->real->(real)net->bool`, lam),
             `f':real`), `atreal r`) in
  DISCH_ALL(p3s_rdiff (CONJUNCTS(UNDISCH(SPEC_ALL STDS_RT_AB_DERIVS))) tm);;

(* From P3S_RS_AB_SQRT (pc_p3_s13rot). *)
let STDS_RT_RS_AB_SQRT = prove
 (`!g0 r. stds_rotm g0
             ==> &0 < p3s_rad_a g0 r /\ &0 < p3s_rad_b g0 r /\
                 &0 < sqrt(p3s_rad_a g0 r) /\ &0 < sqrt(p3s_rad_b g0 r) /\
                 ~(sqrt(p3s_rad_a g0 r) = &0) /\ ~(&2 * sqrt(p3s_rad_b g0 r) = &0) /\
                 sqrt(p3s_rad_a g0 r) pow 2 = p3s_rad_a g0 r /\
                 sqrt(p3s_rad_b g0 r) pow 2 = p3s_rad_b g0 r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDS_RT_ROT_AB) THEN
  SUBGOAL_THEN `&0 < p3s_rad_a g0 r /\ &0 < p3s_rad_b g0 r` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE; REAL_LT_IMP_NZ; REAL_ENTIRE] THEN
  REAL_ARITH_TAC);;

(* From P3S_H_DERIV (pc_p3_s13rot). *)
let STDS_RT_H_DERIV = prove
 (`!g0 r. stds_rotm g0
             ==> ((\r. r * sqrt(p3s_rad_b g0 r)) has_real_derivative
                  p3s_rs_f1 g0 r * sqrt(p3s_rad_a g0 r)) (atreal r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(stds_rt_rs_hthm ()) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[p3s_rs_f1] THEN
  UNDISCH_TAC `~(sqrt(p3s_rad_a g0 r) = &0)` THEN
  UNDISCH_TAC `~(&2 * sqrt(p3s_rad_b g0 r) = &0)` THEN CONV_TAC REAL_FIELD);;

(* From P3S_RS_F1_DIFF (pc_p3_s13rot). *)
let STDS_RT_RS_F1_DIFF = prove
 (`!g0 r. stds_rotm g0
             ==> (p3s_rs_f1 g0 has_real_derivative real_derivative (p3s_rs_f1 g0) r)
                 (atreal r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P3S_RS_F1_EQ] THEN
  MP_TAC(stds_rt_rs_f1thm ()) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP P3S_HAS_RD));;

(* From P3S_RHO_POS (pc_p3_s13rot). *)
let STDS_RT_RHO_POS = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r ==> &0 < p3s_rad_rho g0 r`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `g0:real^3->real^3^3` P3S_RHO_0)] THEN
  MATCH_MP_TAC STDS_RT_RHO_STRICT THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* From P3S_E1_FACTS (pc_p3_s13rot). *)
let STDS_RT_E1_FACTS = prove
 (`!g0 r. stds_rotm g0
             ==> basis 1 dot (g0 (r % basis 1) ** basis 1) = p3s_rad_a g0 r /\
                 basis 2 dot (g0 (r % basis 1) ** basis 2) = p3s_rad_b g0 r /\
                 basis 3 dot (g0 (r % basis 1) ** basis 3) = p3s_rad_b g0 r /\
                 basis 1 dot (g0 (r % basis 1) ** basis 2) = &0 /\
                 basis 2 dot (g0 (r % basis 1) ** basis 3) = &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(GEN `w:real^3` (GEN `v:real^3` (UNDISCH(ISPECL
    [`g0:real^3->real^3^3`; `r:real`; `w:real^3`; `v:real^3`]
    STDS_RT_ROT_E1_BIL)))) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SIMP_TAC[BASIS_COMPONENT; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
  REAL_ARITH_TAC);;

(* From P3S_SEC_RADIAL_PLANE (pc_p3_s13rot). *)
let STDS_RT_SEC_RADIAL_PLANE = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r
             ==> mfd_sectional (open_set_atlas (:real^3)) g0 (r % basis 1)
                               (basis 1) (basis 2) =
                 p3s_rs_krad g0 r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `r % basis 1:real^3`;
                 `basis 1:real^3`; `basis 2:real^3`] STDS_RT_G0_SECTIONAL) THEN
  ASM_REWRITE_TAC[P3S_NONCOLL_BASIS; VECTOR_MUL_EQ_0] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_E1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DOT_RMUL; DOT_LMUL; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC [`aa = p3s_rad_a (g0:real^3->real^3^3) r`;
                        `bb = p3s_rad_b (g0:real^3->real^3^3) r`;
                        `kk = p3s_rs_krad g0 r`] THEN
  SUBGOAL_THEN `~(aa = &0) /\ ~(bb = &0) /\ ~(r = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD]);;

(* From P3S_SEC_TANG_PLANE (pc_p3_s13rot). *)
let STDS_RT_SEC_TANG_PLANE = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r
             ==> mfd_sectional (open_set_atlas (:real^3)) g0 (r % basis 1)
                               (basis 2) (basis 3) =
                 p3s_rs_ktan g0 r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `r % basis 1:real^3`;
                 `basis 2:real^3`; `basis 3:real^3`] STDS_RT_G0_SECTIONAL) THEN
  ASM_REWRITE_TAC[P3S_NONCOLL_BASIS; VECTOR_MUL_EQ_0] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_E1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DOT_RMUL; DOT_LMUL; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC [`aa = p3s_rad_a (g0:real^3->real^3^3) r`;
                        `bb = p3s_rad_b (g0:real^3->real^3^3) r`;
                        `kk = p3s_rs_ktan g0 r`] THEN
  SUBGOAL_THEN `~(aa = &0) /\ ~(bb = &0) /\ ~(r = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* The sectional curvature of an SO(3)-invariant metric in                  *)
(* terms of the Euclidean radius r.  With F(r) = r sqrt(b r) and            *)
(* q = p3s_rs_f1 = F'/sqrt(a) (the derivative of the warping function in    *)
(* arclength): K_tan = (1 - q^2)/F^2 and K_rad = -q'/(sqrt(a) F)            *)
(* (STDS_RT_KTAN_EQ, STDS_RT_KRAD_EQ, the algebra of P3S_SEC_TAN_RHO and     *)
(* P3S_SEC_RAD_RHO without the radial distance).  Every sectional curvature *)
(* at y is a convex combination of K_tan and K_rad at |y|                   *)
(* (STDS_RT_SEC_COMB).  For sec >= 0: q' <= 0 and q^2 <= 1; completeness    *)
(* makes rho unbounded, and then q >= 0 (STDS_RT_Q_NONNEG).                 *)
(* ------------------------------------------------------------------------- *)

let STDS_RT_KTAN_EQ = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r
          ==> p3s_rs_ktan g0 r =
              (&1 - p3s_rs_f1 g0 r pow 2) / (r * sqrt(p3s_rad_b g0 r)) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3s_rs_f1; p3s_rs_ktan; p3s_rs_m1; p3s_rs_m2; p3s_rs_c] THEN
  MAP_EVERY ABBREV_TAC [`sa = sqrt(p3s_rad_a (g0:real^3->real^3^3) r)`;
                        `sb = sqrt(p3s_rad_b (g0:real^3->real^3^3) r)`] THEN
  SUBGOAL_THEN `p3s_rad_a (g0:real^3->real^3^3) r = sa pow 2 /\
                p3s_rad_b (g0:real^3->real^3^3) r = sb pow 2`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["sa"; "sb"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `b1 = real_derivative (p3s_rad_b (g0:real^3->real^3^3)) r` THEN
  SUBGOAL_THEN `~(r = &0) /\ ~(sa = &0) /\ ~(sb = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let STDS_RT_KRAD_EQ = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r
          ==> p3s_rs_krad g0 r = --(p3s_rs_f2 g0 r) / (r * sqrt(p3s_rad_b g0 r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_RS_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3s_rs_f2; p3s_rs_krad] THEN
  MP_TAC(stds_rt_rs_f1thm ()) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
  REWRITE_TAC[GSYM P3S_RS_F1_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(stds_rt_rs_dthm 2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
  REWRITE_TAC[GSYM P3S_RS_M2_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p3s_rs_m1; p3s_rs_m2; p3s_rs_m3; p3s_rs_c; p3s_rs_dc] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC [`sa = sqrt(p3s_rad_a (g0:real^3->real^3^3) r)`;
                        `sb = sqrt(p3s_rad_b (g0:real^3->real^3^3) r)`] THEN
  SUBGOAL_THEN `p3s_rad_a (g0:real^3->real^3^3) r = sa pow 2 /\
                p3s_rad_b (g0:real^3->real^3^3) r = sb pow 2`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["sa"; "sb"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`a1 = real_derivative (p3s_rad_a (g0:real^3->real^3^3)) r`;
    `b1 = real_derivative (p3s_rad_b (g0:real^3->real^3^3)) r`;
    `b2 = real_derivative (real_derivative (p3s_rad_b (g0:real^3->real^3^3))) r`] THEN
  SUBGOAL_THEN `~(r = &0) /\ ~(sa = &0) /\ ~(sb = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* The convex combination.                                                    *)

let STDS_RT_SEC_COMB = prove
 (`!g0 (y:real^3) u v.
     stds_rotm g0 /\ ~(y = vec 0) /\ ~collinear {vec 0,u,v}
     ==> ?X Y. &0 <= X /\ &0 <= Y /\ &0 < X + Y /\
               mfd_sectional (open_set_atlas (:real^3)) g0 y u v =
               (p3s_rs_ktan g0 (norm y) * X + p3s_rs_krad g0 (norm y) * Y) / (X + Y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`]
         STDS_RT_G0_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < (u dot ((g0:real^3->real^3^3) y ** u)) * (v dot (g0 y ** v)) -
                     (u dot (g0 y ** v)) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_SECT_DEN_POS THEN EXISTS_TAC `(:real^3)` THEN
    ASM_SIMP_TAC[IN_UNIV; STDS_RT_METRIC_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC `nn = norm(y:real^3) pow 2` THEN
  SUBGOAL_THEN `&0 < nn` ASSUME_TAC THENL
   [EXPAND_TAC "nn" THEN ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `TT = (u dot u - (u dot y) pow 2 / nn) * (v dot v - (v dot y) pow 2 / nn) -
                  ((u:real^3) dot v - (u dot y) * (v dot y) / nn) pow 2` THEN
  ABBREV_TAC `bb = p3s_rad_b (g0:real^3->real^3^3) (norm(y:real^3))` THEN
  ABBREV_TAC `aa = p3s_rad_a (g0:real^3->real^3^3) (norm(y:real^3))` THEN
  ABBREV_TAC `D = (u dot u) * (v dot v) - ((u:real^3) dot v) pow 2` THEN
  ABBREV_TAC `E = (v dot y) pow 2 * (u dot u) + (u dot y) pow 2 * (v dot v) -
                  &2 * (u dot y) * (v dot y) * ((u:real^3) dot v)` THEN
  SUBGOAL_THEN `&0 < aa /\ &0 < bb` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN ASM_MESON_TAC[STDS_RT_ROT_AB]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    MP_TAC(ISPEC `(v dot y) % u - (u dot y) % (v:real^3)` DOT_POS_LE) THEN
    REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `E <= nn * D` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E"; "D"; "nn"] THEN REWRITE_TAC[NORM_POW_2] THEN
    MP_TAC(SPECL [`u:real^3`; `v:real^3`; `y:real^3`] STDS_GRAM3) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> (a - b = s) ==> b <= a`) THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `TT = D - E / nn` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["TT"; "D"; "E"] THEN UNDISCH_TAC `&0 < nn` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= TT` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LE] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u dot ((g0:real^3->real^3^3) y ** u)) * (v dot (g0 y ** v)) -
    (u dot (g0 y ** v)) pow 2 = bb pow 2 * TT + aa * bb / nn * E`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `!w v:real^3. w dot ((g0:real^3->real^3^3) y ** v) =
                               aa * (w dot y) * (v dot y) / nn +
                               bb * (w dot v - (w dot y) * (v dot y) / nn)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN MAP_EVERY EXPAND_TAC ["aa"; "bb"; "nn"] THEN
      MATCH_MP_TAC STDS_RT_ROT_BIL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["D"; "E"] THEN
    REWRITE_TAC[DOT_SYM] THEN UNDISCH_TAC `&0 < nn` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`bb pow 2 * TT`; `aa * bb / nn * E`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < (u dot ((g0:real^3->real^3^3) y ** u)) * (v dot (g0 y ** v)) -
                      (u dot (g0 y ** v)) pow 2` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

let STDS_RT_SEC_NONNEG = prove
 (`!g0 (y:real^3) u v.
     stds_rotm g0 /\ ~(y = vec 0) /\ ~collinear {vec 0,u,v} /\
     &0 <= p3s_rs_ktan g0 (norm y) /\ &0 <= p3s_rs_krad g0 (norm y)
     ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) g0 y u v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`]
         STDS_RT_SEC_COMB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:real` (X_CHOOSE_THEN `Y:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]);;

let STDS_RT_SEC_ABS = prove
 (`!g0 (y:real^3) u v K.
     stds_rotm g0 /\ ~(y = vec 0) /\ ~collinear {vec 0,u,v} /\
     abs(p3s_rs_ktan g0 (norm y)) <= K /\ abs(p3s_rs_krad g0 (norm y)) <= K
     ==> abs(mfd_sectional (open_set_atlas (:real^3)) g0 y u v) <= K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`]
         STDS_RT_SEC_COMB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:real` (X_CHOOSE_THEN `Y:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < a ==> abs a = a`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(p3s_rs_ktan g0 (norm(y:real^3))) * X +
              abs(p3s_rs_krad g0 (norm y)) * Y` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs a <= a' /\ abs b <= b' ==> abs(a + b) <= a' + b'`) THEN
    ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LE_REFL];
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
    CONJ_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* For sec >= 0: K_tan, K_rad >= 0, hence q' <= 0 and q^2 <= 1.               *)

let STDS_RT_K_NONNEG = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r /\
          (!x u v. ~collinear {vec 0,u,v}
                   ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) g0 x u v)
          ==> &0 <= p3s_rs_ktan g0 r /\ &0 <= p3s_rs_krad g0 r`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_SEC_TANG_PLANE);
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_SEC_RADIAL_PLANE)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[P3S_NONCOLL_BASIS]);;

let STDS_RT_Q_FACTS = prove
 (`!g0 r. stds_rotm g0 /\ &0 < r /\
          (!x u v. ~collinear {vec 0,u,v}
                   ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) g0 x u v)
          ==> real_derivative (p3s_rs_f1 g0) r <= &0 /\ p3s_rs_f1 g0 r pow 2 <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_K_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_KTAN_EQ) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_KRAD_EQ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`] STDS_RT_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r * sqrt(p3s_rad_b g0 r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (r * sqrt(p3s_rad_b g0 r)) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN
  REWRITE_TAC[p3s_rs_f2] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(p3s_rad_a g0 r))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= --x <=> x <= &0`] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < real_derivative (p3s_rs_f1 g0) r * inv(sqrt(p3s_rad_a g0 r))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* Completeness: the radial distance is unbounded.                             *)

let STDS_RT_DIST_LE = prove
 (`!g0 (x:real^3). stds_rotm g0
     ==> mfd_dist (euclidean,open_set_atlas (:real^3)) g0 (vec 0) x <=
         p3s_rad_rho g0 (norm x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `\t. t % (x:real^3)`; `&0`; `&1`]
         MFD_DIST_LE_LENGTH) THEN
  REWRITE_TAC[P2C_SEGMENT_C1; P2C_EUCLID_FACTS; BETA_THM; VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
  ASM_SIMP_TAC[STDS_RIEM_UNIV_EQ; STDS_RT_METRIC_FIELD; STDS_RT_RAD_SEGMENT]);;

let STDS_RT_RHO_UNBOUNDED = prove
 (`!g0 M. stds_rotm g0 /\ mfd_complete (euclidean,open_set_atlas (:real^3)) g0
          ==> ?r. &0 <= r /\ M < p3s_rad_rho g0 r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  SUBGOAL_THEN
   `compact_in euclidean
      (mfd_cball (euclidean,open_set_atlas (:real^3)) g0 (vec 0) M)`
  MP_TAC THENL
   [UNDISCH_TAC `mfd_complete (euclidean,open_set_atlas (:real^3)) g0` THEN
    REWRITE_TAC[mfd_complete] THEN
    DISCH_THEN(MP_TAC o SPECL [`vec 0:real^3`; `M:real`]) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_cball (euclidean,open_set_atlas (:real^3)) g0 (vec 0) M = (:real^3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM; IN_UNIV; P2C_RAD_JOINABLE] THEN
    X_GEN_TAC `y:real^3` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p3s_rad_rho g0 (norm(y:real^3))` THEN
    ASM_SIMP_TAC[STDS_RT_DIST_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `norm(y:real^3)`) THEN REWRITE_TAC[NORM_POS_LE];
    REWRITE_TAC[COMPACT_IN_EUCLIDEAN] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[NOT_BOUNDED_UNIV]]);;

(* A real function with nonpositive derivative on [r0,inf) is nonincreasing   *)
(* there.                                                                     *)

let STDS_DECR_FROM = prove
 (`!f f' r0 r. (!x. r0 <= x ==> (f has_real_derivative f' x) (atreal x)) /\
               (!x. r0 <= x ==> f' x <= &0) /\ r0 <= r
               ==> f r <= f r0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. --((f:real->real) x)`; `\x. --((f':real->real) x)`;
                 `{x:real | r0 <= x}`; `r0:real`; `r:real`]
         HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL; BETA_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* q >= 0 for complete metrics with sec >= 0.                                 *)

let STDS_RT_Q_NONNEG = prove
 (`!g0 r. stds_rotm g0 /\ mfd_complete (euclidean,open_set_atlas (:real^3)) g0 /\
          (!x u v. ~collinear {vec 0,u,v}
                   ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) g0 x u v) /\
          &0 < r
          ==> &0 <= p3s_rs_f1 g0 r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `c = --(p3s_rs_f1 g0 r)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x. r <= x ==> p3s_rs_f1 g0 x <= --c` ASSUME_TAC THENL
   [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p3s_rs_f1 g0`; `real_derivative (p3s_rs_f1 g0)`; `r:real`; `x:real`]
           STDS_DECR_FROM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THEN X_GEN_TAC `z:real` THEN DISCH_TAC THENL
       [MATCH_MP_TAC STDS_RT_RS_F1_DIFF THEN ASM_REWRITE_TAC[];
        MP_TAC(SPECL [`g0:real^3->real^3^3`; `z:real`] STDS_RT_Q_FACTS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      EXPAND_TAC "c" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `H = \x. x * sqrt(p3s_rad_b g0 x) + c * p3s_rad_rho g0 x` THEN
  SUBGOAL_THEN `!x. r <= x ==> (H:real->real) x <= H r` ASSUME_TAC THENL
   [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC STDS_DECR_FROM THEN
    EXISTS_TAC `\x. (p3s_rs_f1 g0 x + c) * sqrt(p3s_rad_a g0 x)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `z:real` THEN DISCH_TAC THENL
     [EXPAND_TAC "H" THEN BETA_TAC THEN REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC STDS_RT_H_DERIV THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC STDS_RT_RHO_DERIV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      BETA_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a * --b ==> a * b <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[STDS_RT_RS_AB_SQRT; REAL_LT_IMP_LE] THEN
      FIRST_ASSUM(MP_TAC o SPEC `z:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `max (p3s_rad_rho g0 r) ((H:real->real) r / c)`]
         STDS_RT_RHO_UNBOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `x <= r` THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `x:real`; `r:real`] STDS_RT_RHO_LT_EQ) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `max (p3s_rad_rho g0 r) ((H:real->real) r / c) < p3s_rad_rho g0 x` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "H" THEN BETA_TAC THEN
  SUBGOAL_THEN `&0 < x * sqrt(p3s_rad_b g0 x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LT; STDS_RT_ROT_AB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `p3s_rad_rho g0 x * c < (H:real->real) r` MP_TAC THENL
   [EXPAND_TAC "H" THEN BETA_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
  UNDISCH_TAC `max (p3s_rad_rho g0 r) ((H:real->real) r / c) < p3s_rad_rho g0 x` THEN
  REAL_ARITH_TAC);;

