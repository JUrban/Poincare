(* ========================================================================= *)
(* pc_moi_s35_apxsep: main theorem APPROX_R2 = MOI_S35_APPROX_R2 of          *)
(* pc_moi_s35_stmt_r2.ml: the 34.1 approximations of pc_moi_s35_approx also  *)
(* satisfy the per-edge model separation moi_s35_sep (the B-chart image of   *)
(* the cube part x3 >= 1/8 misses the A-chart image of the slab part         *)
(* x3 <= 1/16), which the final step needs.  Method: one more per-edge       *)
(* goodness from MOI_S5A_EDGE_SEP_MODEL, and the final error choice of       *)
(* APPROX (MOI_S5A_ERR_CHOICE .. APPROX) re-run with the minimum of the two  *)
(* per-edge bounds.                                                          *)
(* ========================================================================= *)

needs "src/pc_moi_s35_approx.ml";;
needs "src/pc_moi_s35_stmt_r2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. The separation as a per-edge goodness (MOI_S5A_EDGE_SEP_MODEL on the   *)
(* compact disjoint model sets slab INTER x3 <= 1/16 and cube INTER          *)
(* x3 >= 1/8).                                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_S5Q_SEP_MODEL_FACTS = prove
 (`compact {x:real^3 | x IN moi_s35_slab /\ x$3 <= &1 / &16} /\
   compact {x:real^3 | x IN moi_s35_cube /\ &1 / &8 <= x$3} /\
   {x:real^3 | x IN moi_s35_slab /\ x$3 <= &1 / &16} SUBSET moi_s35_dom /\
   {x:real^3 | x IN moi_s35_cube /\ &1 / &8 <= x$3} SUBSET
   moi_s35_bcell UNION moi_s35_upper /\
   DISJOINT {x:real^3 | x IN moi_s35_slab /\ x$3 <= &1 / &16}
            {x:real^3 | x IN moi_s35_cube /\ &1 / &8 <= x$3}`,
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `{x:real^3 | x IN moi_s35_slab /\ x$3 <= &1 / &16} =
                  moi_s35_slab INTER {x:real^3 | x$3 <= &1 / &16}` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    REWRITE_TAC[MOI_S5A_MODEL_COMPACT; CLOSED_HALFSPACE_COMPONENT_LE];
    SUBGOAL_THEN `{x:real^3 | x IN moi_s35_cube /\ &1 / &8 <= x$3} =
                  moi_s35_cube INTER {x:real^3 | x$3 >= &1 / &8}` SUBST1_TAC THENL
     [REWRITE_TAC[real_ge] THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    REWRITE_TAC[MOI_S5A_MODEL_COMPACT; CLOSED_HALFSPACE_COMPONENT_GE];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC]);;

let MOI_S5Q_SEP_GOOD = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?d. &0 < d /\
             moi_s5a_good t l h av bv psi e d
              (\ff cc. DISJOINT (IMAGE (moi_s35_bch ff bv psi e)
                                       {x | x IN moi_s35_cube /\ &1 / &8 <= x$3})
                                (IMAGE (moi_s35_ach ff av psi e)
                                       {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5Q_SEP_MODEL_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`; `{x:real^3 | x IN moi_s35_slab /\ x$3 <= &1 / &16}`;
    `{x:real^3 | x IN moi_s35_cube /\ &1 / &8 <= x$3}`] MOI_S5A_EDGE_SEP_MODEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[moi_s5a_good] THEN
  MAP_EVERY X_GEN_TAC [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `cc:(real^N->bool)->real`] THEN
  STRIP_TAC THEN BETA_TAC THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
  EXISTS_TAC `err:real^N->real` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. The main theorem APPROX_R2: the top-level proof of APPROX              *)
(* (pc_moi_s35_approx.ml) with the per-edge bound d replaced by min d d2 (d2 *)
(* from MOI_S5Q_SEP_GOOD) and the separation proved for the chosen maps      *)
(* (MOI_S5Q_SEP_TAC).                                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S5Q_SEP_TAC =
  REWRITE_TAC[moi_s35_sep] THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "sg" (MP_TAC o SPEC `e:real^N->bool`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[moi_s5a_good] THEN
  DISCH_THEN(MP_TAC o SPECL [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                             `cc:(real^N->bool)->real`]) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "err" (MP_TAC o SPEC `(av:(real^N->bool)->real^N) e`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o CONJUNCT2 o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "err" (MP_TAC o SPEC `(bv:(real^N->bool)->real^N) e`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o CONJUNCT2 o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `(err:real^N->real) ((av:(real^N->bool)->real^N) e) <=
               min ((d:(real^N->bool)->real) e) ((d2:(real^N->bool)->real) e) / &2` THEN
  UNDISCH_TAC `(err:real^N->real) ((bv:(real^N->bool)->real^N) e) <=
               min ((d:(real^N->bool)->real) e) ((d2:(real^N->bool)->real) e) / &2` THEN
  REAL_ARITH_TAC;;

let APPROX_R2 = prove
 (MOI_S35_APPROX_R2,
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`] MOI_S5A_CTX_INTRO) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `kk:real^N->real^N->bool`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  MP_TAC(moi_s5a_cs [] MOI_S5A_ETA_EXISTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `eta:real^N->real`) THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
   (REWRITE_RULE[ASSUME `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk`]
     (moi_s5a_cs [] (MP MOI_S5A_MARK_V (ASSUME MOI_S35_MARKER))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `rm:real^N->real` (LABEL_TAC "rm")) THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
   (REWRITE_RULE[ASSUME `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk`]
     (moi_s5a_cs [] (MP MOI_S5A_FILL_V (ASSUME MOI_S35_FILL))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `rf:real^N->real` (LABEL_TAC "rf")) THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
   (REWRITE_RULE[ASSUME `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk`]
     (moi_s5a_cs [] (MP MOI_S5A_EDGE_GOOD
       (CONJ (ASSUME MOI_S35_MARKER)
             (CONJ (ASSUME MOI_S35_LOCAL_SIGN) (ASSUME MOI_S35_CLOSE_SIGN))))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->real` (LABEL_TAC "dg")) THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
   (REWRITE_RULE[ASSUME `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk`]
     (moi_s5a_cs [] MOI_S5Q_SEP_GOOD))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:(real^N->bool)->real` (LABEL_TAC "sg")) THEN
  MP_TAC(moi_s5a_cs [`eta:real^N->real`; `rm:real^N->real`; `rf:real^N->real`;
                     `\e:real^N->bool. min ((d:(real^N->bool)->real) e)
                                           ((d2:(real^N->bool)->real) e)`]
    MOI_S5A_ERR_CHOICE) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `moi_s5a_etaok t l (h:real^N->real^3) av bv psi kk eta` THEN
        REWRITE_TAC[moi_s5a_etaok] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
        USE_THEN "rm" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
        USE_THEN "rf" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]];
      X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [USE_THEN "dg" (MP_TAC o SPEC `e:real^N->bool`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
        USE_THEN "sg" (MP_TAC o SPEC `e:real^N->bool`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]]];
    DISCH_THEN(X_CHOOSE_THEN `err:real^N->real` (LABEL_TAC "err"))] THEN
  MP_TAC(moi_s5a_cs [`err:real^N->real`]
    (MP MOI_S5A_FF_CHOICE (CONJ (ASSUME `MOISE_341_STATEMENT`)
                                (ASSUME MOI_S35_CELL_341)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "err" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `ff:real^N->real^N->real^3`)] THEN
  SUBGOAL_THEN moi_s5a_body_gen (LABEL_TAC "body") THENL
   [MAP_EVERY X_GEN_TAC [`e:real^N->bool`; `cc:(real^N->bool)->real`] THEN
    STRIP_TAC THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "dg" (MP_TAC o SPEC `e:real^N->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[moi_s5a_good] THEN
    DISCH_THEN(MP_TAC o SPECL [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                               `cc:(real^N->bool)->real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "err" (MP_TAC o SPEC `(av:(real^N->bool)->real^N) e`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o CONJUNCT2 o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      USE_THEN "err" (MP_TAC o SPEC `(bv:(real^N->bool)->real^N) e`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o CONJUNCT2 o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      UNDISCH_TAC `(err:real^N->real) ((av:(real^N->bool)->real^N) e) <=
                   min ((d:(real^N->bool)->real) e) ((d2:(real^N->bool)->real) e) / &2` THEN
      UNDISCH_TAC `(err:real^N->real) ((bv:(real^N->bool)->real^N) e) <=
                   min ((d:(real^N->bool)->real) e) ((d2:(real^N->bool)->real) e) / &2` THEN
      REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`;
    `\e. {x | x IN moi_s35_dom /\
              moi_s35_ach (ff:real^N->real^N->real^3) av psi e x IN
              IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann}`] MOI_S5A_CC_CHOICE) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN BETA_TAC THEN
    USE_THEN "body" (MP_TAC o SPECL [`e:real^N->bool`;
                                     `\e:real^N->bool. &0`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_S5A_TRI_EXISTS THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`;
      `w:real^N->real^3->bool`; `kk:real^N->real^N->bool`; `err:real^N->real`;
      `Phi:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `cc:(real^N->bool)->real`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cct")))] THEN
  MAP_EVERY EXISTS_TAC
   [`ff:real^N->real^N->real^3`;
    `\v. IMAGE ((ff:real^N->real^N->real^3) v) (moi_s35_csrc t l av bv psi cc v)`;
    `cc:(real^N->bool)->real`] THEN
  SUBGOAL_THEN moi_s5a_fill_all ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S5A_F1E THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `kk:real^N->real^N->bool`;
      `err:real^N->real`; `(rf:real^N->real) v`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rf" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      USE_THEN "err" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      X_GEN_TAC `e:real^N->bool` THEN
      DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
      MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "err" (MP_TAC o SPEC `(av:(real^N->bool)->real^N) e`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT2 o CONJUNCT2 o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match []
        `(bv:(real^N->bool)->real^N) e = v`) o concl)) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; MOI_S5Q_SEP_TAC] THEN
  REWRITE_TAC[moi_s35_pre] THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5A_FRAME_ALL THEN
    MAP_EVERY EXISTS_TAC [`kk:real^N->real^N->bool`; `eta:real^N->real`;
                          `err:real^N->real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
      USE_THEN "err" (MP_TAC o SPEC `u:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      USE_THEN "rm" (MP_TAC o SPEC `v:real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
        `ff:real^N->real^N->real^3`; `err:real^N->real`;
        `v:real^N`] MOI_S5A_APX_AT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(err:real^N->real) v` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
          `!x. x IN moi_s35_cplus t l av bv psi v
               ==> dist((ff:real^N->real^N->real^3) v x,(h:real^N->real^3) x) <
                   err v`) o concl)) THEN
        FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "err" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]];
      X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      ACCEPT_TAC(MP (SPECL [`e:real^N->bool`; `cc:(real^N->bool)->real`]
                     (ASSUME moi_s5a_body_gen))
                    (CONJ (ASSUME `moi_s35_edge l (e:real^N->bool)`)
                          (ASSUME `!e:real^N->bool.
                                     abs((cc:(real^N->bool)->real) e) <=
                                     &1 / &512`)))];
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S5A_PRE_EDGE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `kk:real^N->real^N->bool`;
                          `err:real^N->real`] THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cct" (fun cct -> ACCEPT_TAC(end_itlist CONJ
     [ASSUME `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk`;
      ASSUME `moi_s5a_apx t l av bv psi (h:real^N->real^3) ff err`;
      ASSUME `!e:real^N->bool. abs((cc:(real^N->bool)->real) e) <= &1 / &512`;
      ASSUME `moi_s35_edge l (e:real^N->bool)`;
      MP (SPECL [`e:real^N->bool`; `cc:(real^N->bool)->real`]
           (ASSUME moi_s5a_body_gen))
         (CONJ (ASSUME `moi_s35_edge l (e:real^N->bool)`)
               (ASSUME `!e:real^N->bool.
                          abs((cc:(real^N->bool)->real) e) <= &1 / &512`));
      MP (SPEC `(bv:(real^N->bool)->real^N) e` (ASSUME moi_s5a_fill_all))
         (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`);
      MP (SPEC `e:real^N->bool` cct) (ASSUME `moi_s35_edge l (e:real^N->bool)`)]))]);;

