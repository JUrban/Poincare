(* ========================================================================= *)
(* pc_moi_s35_stmt_r1: the R1 form of the 35.1 glue.  The statement          *)
(* MOI_S35_COMBINE of pc_moi_s35_stmt.ml assumes only moi_s35_pre, which     *)
(* carries no graph or chart facts (av e, bv e need not be vertices; a       *)
(* vertex may have infinitely many B-side edges), too little for the         *)
(* combination.  MOI_S35_COMBINE_R1 adds graph_in_complex and                *)
(* moi_s35_charts as antecedents (as MOI_S35_FINAL_CELLS has); the glue is   *)
(* proved with it as MOI_S5D_351_FROM_CORES_R1 and MOI_S5D_PROD_351_R1,      *)
(* which conclude MOI_PROD_351; the final assembly does not use              *)
(* MOI_S35_COMBINE.                                                          *)
(* ========================================================================= *)

needs "src/pc_moi_s35_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_S35_COMBINE_R1 = mk_imp(MOI_S35_REMOVAL,
 `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w (g:real^N->real^N->bool)
   av bv psi ff xx cc.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_pre t l h w av bv psi ff xx cc
     ==> ?xx'. moi_s35_post t l h w av bv psi ff xx' cc`);;

let MOI_S35_UNIT_TARGETS_R1 =
  [MOI_S35_TUBE_TRIPLE; MOI_S35_MARKER; MOI_S35_CELL_341; MOI_S35_FILL;
   MOI_S35_LOCAL_SIGN; MOI_S35_CLOSE_SIGN; MOI_S35_ONE_DISK_EXT;
   MOI_S35_TWO_DISK_EXT; MOI_S35_SLAB_PRODUCT; MOI_S35_CHARTS; MOI_S35_SOURCE;
   MOI_S35_APPROX; MOI_S35_LEMMA1; MOI_S35_SINGLE_FROM_ONE; MOI_S35_DISK_SWAP;
   MOI_S35_ANNULUS_SWAP; MOI_S35_COMBINE_R1; MOI_S35_FINAL_CELLS; MOI_S35_FINAL];;

map type_of [MOI_S35_COMBINE_R1];;
map frees [MOI_S35_COMBINE_R1];;

(* The glue of pc_moi_s35_stmt.ml section 8 with COMBINE replaced by       *)
(* COMBINE_R1 (one more specialization: g = the preimage of w by h).        *)

let MOI_S5D_351_FROM_CORES_R1 = prove
 (mk_imp(list_mk_conj [MOI_FND_DERIVED_NBHD_BASIC; rand MOI_S35_CHARTS;
                       rand MOI_S35_SOURCE; rand MOI_S35_APPROX;
                       rand MOI_S35_COMBINE_R1; rand MOI_S35_FINAL],
         `!u:N->bool. MOISE_351_STATEMENT u`),
  DISCH_THEN(fun hs ->
    let dnb,r1 = CONJ_PAIR hs in
    let ch,r2 = CONJ_PAIR r1 in
    let so,r3 = CONJ_PAIR r2 in
    let ap,r4 = CONJ_PAIR r3 in
    let cb,fi = CONJ_PAIR r4 in
    GEN_TAC THEN REWRITE_TAC[MOISE_351_STATEMENT; graph_approximable] THEN
    MAP_EVERY X_GEN_TAC
     [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^3`] THEN
    STRIP_TAC THEN X_GEN_TAC `w:real^N->real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                  `\v:real^N. {x | x IN UNIONS t /\ (h:real^N->real^3) x IN w v}`] ch) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] dnb) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[graph_in_complex]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      SUBGOAL_THEN `IMAGE (h:real^N->real^3) (derived_dual_cell t l v) SUBSET w v`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[derived_dual_cell] THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `av:(real^N->bool)->real^N`
      (X_CHOOSE_THEN `bv:(real^N->bool)->real^N`
        (X_CHOOSE_TAC `psi:(real^N->bool)->real^3->real^N`))) THEN
    MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                  `\v:real^N. {x | x IN UNIONS t /\ (h:real^N->real^3) x IN w v}`;
                  `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                  `psi:(real^N->bool)->real^3->real^N`] so) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                  `h:real^N->real^3`; `w:real^N->real^3->bool`;
                  `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                  `psi:(real^N->bool)->real^3->real^N`] ap) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ff:real^N->real^N->real^3`
      (X_CHOOSE_THEN `xx:real^N->real^3->bool`
        (X_CHOOSE_TAC `cc:(real^N->bool)->real`))) THEN
    MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                  `h:real^N->real^3`; `w:real^N->real^3->bool`;
                  `\v:real^N. {x | x IN UNIONS t /\ (h:real^N->real^3) x IN w v}`;
                  `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                  `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                  `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`] cb) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `xx':real^N->real^3->bool`) THEN
    MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                  `h:real^N->real^3`; `w:real^N->real^3->bool`;
                  `\v:real^N. {x | x IN UNIONS t /\ (h:real^N->real^3) x IN w v}`;
                  `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                  `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                  `xx':real^N->real^3->bool`; `cc:(real^N->bool)->real`] fi) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC));;


let MOI_S5D_PROD_351_R1 = prove
 (mk_imp(list_mk_conj (MOI_FND_DERIVED_NBHD_BASIC :: MOI_FND_GRAPH_TUBE ::
                       MOI_S35_UNIT_TARGETS_R1),
         MOI_PROD_351),
  DISCH_THEN(fun hs ->
    match CONJUNCTS hs with
      [dnb; gt; tri; mrk; c341; fil; lsg; csg; one_e; two_e; slb; chs; src; apx;
       l1; one1; dsk; ann; cmb; fcl; fin] ->
        GEN_TAC THEN DISCH_THEN(fun ins ->
          match CONJUNCTS ins with
            [h341; _; h273; hsch; _] ->
              let gtt = CONJ gt tri in
              let pre = CONJ hsch (CONJ l1 slb) in
              let rem = MP MOI_S5D_REMOVAL
                         (end_itlist CONJ [hsch; h273; slb; l1; one1; dsk; ann]) in
              let cores =
                end_itlist CONJ
                 [dnb; MP chs gtt; MP src gtt;
                  MP apx (end_itlist CONJ [h341; mrk; c341; fil; lsg; csg; gt; tri]);
                  MP cmb rem;
                  MP fin (end_itlist CONJ [gt; tri; fcl; one_e; two_e; lsg; hsch])] in
              ignore pre;
              ACCEPT_TAC (SPEC `u:N->bool` (MP MOI_S5D_351_FROM_CORES_R1 cores))
          | _ -> failwith "MOI_S5D_PROD_351: producer antecedent")
    | _ -> failwith "MOI_S5D_PROD_351: hypotheses"));;

