(* ========================================================================= *)
(* Unit pc_p2a_rigid: FL5R P2A_FLOW_RV_RIGID at N = 3 (MT Prop 7.27,         *)
(* rigidity of the reduced volume).  If V(tau0) = (4 pi)^(3/2) then, with    *)
(* V(tau0) <= zdens times the integral of rvi(tau0) over Smin(tau0)          *)
(* (P2AU_FRV_UPPER), the monotonicity of rvi in tau (P2A_RVI_MONO) and the   *)
(* Gaussian bound (P2A_T81_RVI_GAUSS) all inequalities are equalities:       *)
(* Smin(tau0) is conull and rvi(tau1) is the Gaussian almost everywhere on   *)
(* Smin(tau0) for every tau1 in (0,tau0] (P2AU_FRV_EQ_AE).  The step from    *)
(* this equality case to flatness is the statement constant                  *)
(* P2AU_RIGID_CORE_STATEMENT (pc_p2a_rigstmt).  Headline P2AU_FLOW_RV_RIGID: *)
(*   P2AU_RIGID_CORE_STATEMENT u ==> W3 ==> FL5R,                            *)
(* with FL2 discharged by P2AK_FLOW_MIN_EXISTS_3 and FL3 from W3.            *)
(* ========================================================================= *)

needs "src/pc_p2a_frv.ml";;
needs "src/pc_p2a_l72f.ml";;
needs "src/pc_p2a_rigstmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Two auxiliary facts.  A nonnegative integrand with integral at most 0     *)
(* vanishes almost everywhere (HAS_INTEGRAL_NEGLIGIBLE_EQ); the Gaussian 8   *)
(* exp(-Z.G Z) of the metric at x integrates to 8 pi^(3/2) / zdens           *)
(* (P2A_T81_DENS_X, P2A_T81_GAUSS_LINEAR, P2AU_GAUSS_SPACE).                 *)
(* ------------------------------------------------------------------------- *)

let P2AU_INTEGRAL_ZERO_NEGLIGIBLE = prove
 (`!(h:real^N->real) s.
     (\x. lift(h x)) integrable_on s /\ (!x. x IN s ==> &0 <= h x) /\
     drop(integral s (\x. lift(h x))) <= &0
     ==> negligible {x | x IN s /\ ~(h x = &0)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `drop(integral s (\x:real^N. lift(h x))) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x:real^N. lift(h x)) has_integral vec 0) s` MP_TAC THENL
   [SUBGOAL_THEN `vec 0:real^1 = integral s (\x:real^N. lift(h x))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. lift(h x)`; `s:real^N->bool`] HAS_INTEGRAL_NEGLIGIBLE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_1] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  BETA_TAC THEN REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ]);;

(* The Gaussian of the metric at x over the whole Z-space. *)

let P2AU_ZDENS_GAUSS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x.
     p2a_svs V /\ x IN topspace(rfs_vtop V tt)
     ==> (\Z. lift(&8 * exp(--(p2a_znorm2 V tt x Z)))) absolutely_integrable_on (:real^3) /\
         &0 < p2a_zdens V tt x /\
         p2a_zdens V tt x *
         drop(integral (:real^3) (\Z. lift(&8 * exp(--(p2a_znorm2 V tt x Z))))) =
         &8 * pi * sqrt pi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2A_T81_DENS_X) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[P2A_VIEW_PROJ_3]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:real^3^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[p2a_znorm2] THEN
  SUBGOAL_THEN `IMAGE (\Z:real^3. (A0:real^3^3) ** Z) (:real^3) = (:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `z:real^3` THEN
    EXISTS_TAC `matrix_inv(A0:real^3^3) ** z` THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\Z:real^3. lift(&8 * exp(--(Z dot Z)))) has_integral
                 lift(&8 * pi * sqrt pi)) (:real^3) /\
                (\Z:real^3. lift(&8 * exp(--(Z dot Z)))) absolutely_integrable_on (:real^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `&8` (MATCH_MP HAS_INTEGRAL_CMUL (CONJUNCT2 P2AU_GAUSS_SPACE))) THEN
      REWRITE_TAC[GSYM LIFT_CMUL];
      MP_TAC(SPEC `&8` (MATCH_MP ABSOLUTELY_INTEGRABLE_CMUL (CONJUNCT1 P2AU_GAUSS_SPACE))) THEN
      REWRITE_TAC[GSYM LIFT_CMUL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A0:real^3^3`; `(:real^3)`] P2A_T81_GAUSS_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM DROP_CMUL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && p2au_mentions "integral" th && p2au_mentions "det" th)) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE o check (fun th ->
    p2au_mentions "has_integral" th)) THEN
  REWRITE_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* The equality case at the level of integrals.  If V(tau0) =                *)
(* (4 pi)^(3/2) then, with S = Smin(tau0) and zd the density at p,           *)
(*   (4 pi)^(3/2) <= zd int_S rvi(tau0) <= zd int_S rvi(tau1)               *)
(*               <= zd int_S Gauss <= zd int_R3 Gauss = (4 pi)^(3/2)        *)
(* for 0 < tau1 <= tau0, so the complement of S is null and rvi(tau1) is    *)
(* the Gaussian almost everywhere on S.                                       *)
(* ------------------------------------------------------------------------- *)

let P2AU_FRV_EQ_AE = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p tau0.
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\ P2A_FLOW_LX_CONT_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < tau0 /\ tau0 < b - a /\
     p2a_frv (top,atlas) a b g p tau0 = sqrt(&4 * pi) pow 3
     ==> negligible((:real^3) DIFF
                    p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0) /\
         !tau1. &0 < tau1 /\ tau1 <= tau0
                ==> negligible
                     {Z | Z IN p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                        b p tau0 /\
                          ~(p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                    b p tau1 Z =
                            &8 * exp(--(p2a_znorm2
                                         (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                         b p Z)))}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[P2AU_SQRT_4PI_POW3]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  (* the value and the upper bound at tau0 *)
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau0:real`] P2AU_FRV_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau0:real`] P2AU_FRV_VALUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `v = &8 * pi * sqrt pi` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && p2au_mentions "p2a_frv" th)) THEN
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_HAS_INTEGRAL_UNIQUE) THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `(g:real->A->real^3^3)(b - tau0)`;
      `\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                           (g:real->A->real^3^3)) b p tau0 q)) / sqrt tau0 pow 3`;
      `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau0:real`] P2AU_SMIN_COVER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b:real`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `(p:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b) /\ p2a_bsmooth V p b`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `p:A`] P2AU_ZDENS_GAUSS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `S = p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b p tau0` THEN
  ABBREV_TAC `zd = p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b p` THEN
  ABBREV_TAC `gs = \Z. &8 * exp(--(p2a_znorm2 (V:(real->A topology)#(real->((A->bool)#
                         (A->real^3))->bool)#(real->A->real^3^3)) b p Z))` THEN
  SUBGOAL_THEN `!Z:real^3. &0 < gs Z` ASSUME_TAC THENL
   [EXPAND_TAC "gs" THEN GEN_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\Z:real^3. lift(gs Z)) absolutely_integrable_on (:real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "gs" THEN BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `zd * drop(integral (:real^3) (\Z:real^3. lift(gs Z))) = &8 * pi * sqrt pi`
  ASSUME_TAC THENL [EXPAND_TAC "gs" THEN BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\Z:real^3. lift(gs Z)) absolutely_integrable_on S /\
                (\Z:real^3. lift(gs Z)) absolutely_integrable_on ((:real^3) DIFF S)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  (* the chain for a time tau1 in (0,tau0] *)
  SUBGOAL_THEN
   `!tau1. &0 < tau1 /\ tau1 <= tau0
           ==> (\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#
                   (A->real^3))->bool)#(real->A->real^3^3)) b p tau1 Z))
               absolutely_integrable_on S /\
               (!Z. Z IN S ==> p2a_rvi V b p tau0 Z <= p2a_rvi V b p tau1 Z) /\
               (!Z. Z IN S ==> p2a_rvi V b p tau1 Z <= gs Z)`
  (LABEL_TAC "CH") THENL
   [X_GEN_TAC `tau1:real` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)`; `b:real`; `p:A`; `tau0:real`; `tau1:real`;
                    `S:real^3->bool`] P2A_T81_RVI_INTEGRABLE) THEN
      REWRITE_TAC[P2A_RVI_MONO; P2AV_RVI_ASYMP; P2AG_GAUSS_TAIL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET_REFL];
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPEC `u:A->bool` P2A_RVI_MONO) THEN REWRITE_TAC[P2A_RVI_MONO_STATEMENT] THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `tau0:real` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN UNDISCH_TAC `(Z:real^3) IN S` THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[];
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "gs" THEN BETA_TAC THEN
      MATCH_MP_TAC P2A_T81_RVI_GAUSS THEN EXISTS_TAC `tau0:real` THEN
      REWRITE_TAC[P2A_RVI_MONO; P2AV_RVI_ASYMP] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(Z:real^3) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau1. &0 < tau1 /\ tau1 <= tau0
           ==> drop(integral S (\Z. lift(gs Z))) =
               drop(integral S (\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#
                   (A->real^3))->bool)#(real->A->real^3^3)) b p tau1 Z))) /\
               drop(integral (:real^3) (\Z:real^3. lift(gs Z))) =
               drop(integral S (\Z. lift(gs Z)))`
  (LABEL_TAC "EQ") THENL
   [X_GEN_TAC `tau1:real` THEN STRIP_TAC THEN
    USE_THEN "CH" (MP_TAC o SPEC `tau1:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "CH" (MP_TAC o SPEC `tau0:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `drop(integral S (\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#
         (A->real^3))->bool)#(real->A->real^3^3)) b p tau0 Z))) <=
      drop(integral S (\Z. lift(p2a_rvi V b p tau1 Z))) /\
      drop(integral S (\Z. lift(p2a_rvi V b p tau1 Z))) <=
      drop(integral S (\Z:real^3. lift(gs Z))) /\
      drop(integral S (\Z:real^3. lift(gs Z))) <=
      drop(integral (:real^3) (\Z:real^3. lift(gs Z)))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP];
        MATCH_MP_TAC INTEGRAL_DROP_LE THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP];
        MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP; SUBSET_UNIV;
                     REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `drop(integral (:real^3) (\Z:real^3. lift(gs Z))) <=
      drop(integral S (\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#
         (A->real^3))->bool)#(real->A->real^3^3)) b p tau0 Z)))`
    MP_TAC THENL
     [SUBGOAL_THEN `&0 < zd` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ th)]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the complement of S is null *)
    USE_THEN "EQ" (MP_TAC o SPEC `tau0:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`gs:real^3->real`; `(:real^3) DIFF S`] P2AU_INTEGRAL_ZERO_NEGLIGIBLE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `integral ((:real^3) DIFF S) (\Z:real^3. lift(gs Z)) =
                    integral (:real^3) (\Z. lift(gs Z)) - integral S (\Z. lift(gs Z))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC INTEGRAL_DIFF THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; SET_RULE `s DIFF (:real^3) = {}`;
                     NEGLIGIBLE_EMPTY];
        ALL_TAC] THEN
      REWRITE_TAC[DROP_SUB] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  (* rvi(tau1) is the Gaussian almost everywhere on S *)
  X_GEN_TAC `tau1:real` THEN STRIP_TAC THEN
  USE_THEN "EQ" (MP_TAC o SPEC `tau1:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "CH" (MP_TAC o SPEC `tau1:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`\Z. gs Z - p2a_rvi (V:(real->A topology)#(real->((A->bool)#
                      (A->real^3))->bool)#(real->A->real^3^3)) b p tau1 Z`;
                 `S:real^3->bool`] P2AU_INTEGRAL_ZERO_NEGLIGIBLE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN
    ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRAL_SUB; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
                 DROP_SUB; REAL_SUB_LE] THEN
    ABBREV_TAC `i1 = drop(integral S (\Z. lift(p2a_rvi (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b p tau1 Z)))` THEN
    ABBREV_TAC `ig = drop(integral S (\Z:real^3. lift(gs Z)))` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `Z:real^3` THEN
  EXPAND_TAC "gs" THEN BETA_TAC THEN REWRITE_TAC[REAL_SUB_0] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* FL5R from the CORE statement and W3.  FL3 comes from W3                   *)
(* (P2AU_FLOW_LX_CONT) and FL2 is proved (P2AK_FLOW_MIN_EXISTS_3,            *)
(* pc_p2a_l72f); P2AU_FRV_EQ_AE turns V(tau0) = (4 pi)^(3/2) into the        *)
(* hypotheses of the CORE statement, whose conclusion is the flatness        *)
(* required by FL5R.                                                         *)
(* ------------------------------------------------------------------------- *)

let P2AU_FLOW_RV_RIGID = prove
 (`!(u:A->bool) (n:3->bool).
     P2AU_RIGID_CORE_STATEMENT u
     ==> P2B_REQ_P2A_WEAK_STATEMENT u ==> P2A_FLOW_RV_RIGID_STATEMENT u n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2AU_RIGID_CORE_STATEMENT] THEN
  DISCH_THEN(fun core -> DISCH_THEN(fun w3 -> ASSUME_TAC w3 THEN ASSUME_TAC(MP core w3))) THEN
  SUBGOAL_THEN `P2A_FLOW_LX_CONT_STATEMENT (u:A->bool) (n:3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_FLOW_LX_CONT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P2A_FLOW_MIN_EXISTS_STATEMENT (u:A->bool) (n:3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[P2AK_FLOW_MIN_EXISTS_3]; ALL_TAC] THEN
  REWRITE_TAC[P2A_FLOW_RV_RIGID_STATEMENT; DIMINDEX_3] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`; `tau0:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau0:real`] P2AU_FRV_EQ_AE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `p:A`; `tau0:real`] o
   check (fun th -> is_forall(concl th) && p2au_mentions "mfd_sectional" th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

