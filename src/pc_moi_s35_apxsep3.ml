(* ========================================================================= *)
(* pc_moi_s35_apxsep3: main theorem APPROX_R3 = MOI_S35_APPROX_R3 of         *)
(* pc_moi_s35_stmt_r3.ml: the 34.1 approximations of pc_moi_s35_approx       *)
(* (with the error choice of pc_moi_s35_apxsep) also satisfy moi_s35_sep2    *)
(* (the B-chart image of bcell INTER slab misses the A-chart image of the    *)
(* slab of every other edge).  Method: as the frame clause for the level     *)
(* 1/8 (MOI_S5A_FRAME_SEP): psi e(slab) and psi e'(slab) are separation      *)
(* pieces, so eta bounds their setdist; the bound passes to the subset       *)
(* psi e(bcell INTER slab) of cplus(bv e); MOI_S5A_APPROX_DISJOINT.  The     *)
(* top-level proof is that of APPROX_R2 with one more conjunct.              *)
(* ========================================================================= *)

needs "src/pc_moi_s35_apxsep.ml";;
needs "src/pc_moi_s35_stmt_r3.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. sep2 for approximations within a third of the separation radii.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S5X_SEP2 = prove
 (`!t l (h:real^N->real^3) w av bv psi kk eta ff err.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s5a_etaok t l h av bv psi kk eta /\
     (!u. {u} IN l ==> &3 * err u <= eta u) /\
     moi_s5a_apx t l av bv psi h ff err
     ==> moi_s35_sep2 l av bv psi ff`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s35_sep2] THEN
  MAP_EVERY X_GEN_TAC [`e:real^N->bool`; `e':real^N->bool`] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e':real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CPLUS_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e':real^N->bool`] MOI_S5A_CPLUS_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`; `e':real^N->bool`] MOI_S5A_SLAB_DISJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab IN
    moi_s5a_pieces t l av bv psi kk ((bv:(real^N->bool)->real^N) e) /\
    IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab IN
    moi_s5a_pieces t l av bv psi kk ((av:(real^N->bool)->real^N) e')`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5a_pieces; IN_UNION; IN_IMAGE; moi_s5a_edges; IN_ELIM_THM;
                IN_INSERT] THEN
    CONJ_TAC THEN DISJ2_TAC THEN DISJ1_TAC THENL
     [EXISTS_TAC `e:real^N->bool`; EXISTS_TAC `e':real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
          (moi_s35_bcell INTER moi_s35_slab) SUBSET IMAGE (psi e) moi_s35_slab /\
    IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
          (moi_s35_bcell INTER moi_s35_slab) SUBSET
    moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab`;
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_bcell`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)
         ==> dist((ff:real^N->real^N->real^3) (bv e) x,(h:real^N->real^3) x) <
             (err:real^N->real) (bv e)) /\
    (!x. x IN moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e')
         ==> dist((ff:real^N->real^N->real^3) (av e') x,(h:real^N->real^3) x) <
             (err:real^N->real) (av e'))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s5a_apx t l av bv psi (h:real^N->real^3) ff err` THEN
    REWRITE_TAC[moi_s5a_apx] THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `(av:(real^N->bool)->real^N) e'` th) THEN
      MP_TAC(SPEC `(bv:(real^N->bool)->real^N) e` th)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_bch; moi_s35_ach; IMAGE_o] THEN
  MATCH_MP_TAC MOI_S5A_APPROX_DISJOINT THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`;
                        `(err:real^N->real) ((bv:(real^N->bool)->real^N) e)`;
                        `(err:real^N->real) ((av:(real^N->bool)->real^N) e')`] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `S = setdist(IMAGE (h:real^N->real^3)
                                (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                       moi_s35_slab),
                          IMAGE h (IMAGE (psi e') moi_s35_slab))` THEN
  SUBGOAL_THEN
   `~(IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab = {})`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`~(IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
             (moi_s35_bcell INTER moi_s35_slab) = {})`;
      `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
             (moi_s35_bcell INTER moi_s35_slab) SUBSET IMAGE (psi e) moi_s35_slab`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(eta:real^N->real) ((bv:(real^N->bool)->real^N) e) <= S /\
    (eta:real^N->real) ((av:(real^N->bool)->real^N) e') <= S`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s5a_etaok t l (h:real^N->real^3) av bv psi kk eta` THEN
    REWRITE_TAC[moi_s5a_etaok] THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `(bv:(real^N->bool)->real^N) e`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`(av:(real^N->bool)->real^N) e'`;
        `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab`;
        `IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab`] o CONJUNCT2) THEN
      EXPAND_TAC "S" THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `(av:(real^N->bool)->real^N) e'`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[SETDIST_SYM] o SPECL
        [`(bv:(real^N->bool)->real^N) e`;
         `IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab`;
         `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab`] o CONJUNCT2) THEN
      EXPAND_TAC "S" THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `S <= setdist(IMAGE (h:real^N->real^3)
                       (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                              (moi_s35_bcell INTER moi_s35_slab)),
                 IMAGE h (IMAGE (psi e') moi_s35_slab)) /\ &0 <= S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SETDIST_POS_LE] THEN
    MATCH_MP_TAC SETDIST_SUBSET_LEFT THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&3 * (err:real^N->real) ((bv:(real^N->bool)->real^N) e) <= eta (bv e) /\
    &3 * (err:real^N->real) ((av:(real^N->bool)->real^N) e') <= eta (av e')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. The main theorem APPROX_R3: the proof of APPROX_R2 with sep2 added     *)
(* (MOI_S5X_SEP2).                                                           *)
(* ------------------------------------------------------------------------- *)

let APPROX_R3 = prove
 (MOI_S35_APPROX_R3,
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
  CONJ_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL
     [MOI_S5Q_SEP_TAC;
      MATCH_MP_TAC MOI_S5X_SEP2 THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `h:real^N->real^3`;
        `w:real^N->real^3->bool`; `kk:real^N->real^N->bool`; `eta:real^N->real`;
        `err:real^N->real`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
      USE_THEN "err" (MP_TAC o SPEC `u:real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]]] THEN
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


