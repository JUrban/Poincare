(* ========================================================================= *)
(* pc_moi_s35_stmt_r3: the R3 form of the 35.1 glue, used by                 *)
(* pc_moi_s35_all.ml.  The final step (FINAL, unit s35_fin_b) splits D_v     *)
(* along the B-chart level squares E_e of its B-side edges and must know on  *)
(* which side of E_e the disk ddisk e lies; for that the finger of e (the    *)
(* B-chart image of bcell INTER slab) must miss the A-slabs (hence the       *)
(* tubes) of all other edges, which the frame moi_s35_frame says only for    *)
(* the level 1/8.  moi_s35_sep2 is that clause; it mentions only ff, psi,    *)
(* av, bv and l, so COMBINE keeps it.  MOI_S35_APPROX_R3 adds it to the      *)
(* conclusion of the R2 form of APPROX, MOI_S35_FINAL_R3 to the hypotheses   *)
(* of the R2 form of FINAL; the glue is proved again as                      *)
(* MOI_S5D_351_FROM_CORES_R3 and MOI_S5D_PROD_351_R3, which conclude         *)
(* MOI_PROD_351.                                                             *)
(* ========================================================================= *)

needs "src/pc_moi_s35_stmt_r2.ml";;

prioritize_real();;
type_invention_error := true;;

let moi_s35_sep2 = new_definition
 `moi_s35_sep2 (l:(real^N->bool)->bool) (av:(real^N->bool)->real^N)
               (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)
               (ff:real^N->real^N->real^3) <=>
    !e e'. moi_s35_edge l e /\ moi_s35_edge l e' /\ ~(e = e')
           ==> DISJOINT (IMAGE (moi_s35_bch ff bv psi e)
                               (moi_s35_bcell INTER moi_s35_slab))
                        (IMAGE (moi_s35_ach ff av psi e') moi_s35_slab)`;;

let MOI_S35_APPROX_R3 = mk_imp(list_mk_conj
  [`MOISE_341_STATEMENT`; MOI_S35_MARKER; MOI_S35_CELL_341; MOI_S35_FILL;
   MOI_S35_LOCAL_SIGN; MOI_S35_CLOSE_SIGN; MOI_FND_GRAPH_TUBE; MOI_S35_TUBE_TRIPLE],
 `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w av bv psi.
     graph_in_complex t l /\ h continuous_on UNIONS t /\
     (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
     (!v. {v} IN l ==> open (w v) /\ IMAGE h (derived_dual_cell t l v) SUBSET w v) /\
     moi_s35_charts t l (\v. {x | x IN UNIONS t /\ h x IN w v}) av bv psi /\
     moi_s35_source_ok t l av bv psi
     ==> ?ff xx cc. moi_s35_pre t l h w av bv psi ff xx cc /\
                    moi_s35_sep l av bv psi ff /\ moi_s35_sep2 l av bv psi ff`);;

let MOI_S35_FINAL_R3 = mk_imp(list_mk_conj
  [MOI_FND_GRAPH_TUBE; MOI_S35_TUBE_TRIPLE; MOI_S35_FINAL_CELLS; MOI_S35_ONE_DISK_EXT;
   MOI_S35_TWO_DISK_EXT; MOI_S35_LOCAL_SIGN; `PL_SCHOENFLIES_3_STATEMENT`],
 `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_source_ok t l av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_sep2 l av bv psi ff
     ==> ?f. pl_map_on (derived_nbhd t l) f /\
             (!x y. x IN derived_nbhd t l /\ y IN derived_nbhd t l /\ f x = f y
                    ==> x = y) /\
             IMAGE h (UNIONS l) SUBSET interior (IMAGE f (derived_nbhd t l)) /\
             (!v. {v} IN l ==> IMAGE f (derived_dual_cell t l v) SUBSET w v)`);;

let MOI_S35_UNIT_TARGETS_R3 =
  [MOI_S35_TUBE_TRIPLE; MOI_S35_MARKER; MOI_S35_CELL_341; MOI_S35_FILL;
   MOI_S35_LOCAL_SIGN; MOI_S35_CLOSE_SIGN; MOI_S35_ONE_DISK_EXT;
   MOI_S35_TWO_DISK_EXT; MOI_S35_SLAB_PRODUCT; MOI_S35_CHARTS; MOI_S35_SOURCE;
   MOI_S35_APPROX_R3; MOI_S35_LEMMA1; MOI_S35_SINGLE_FROM_ONE; MOI_S35_DISK_SWAP;
   MOI_S35_ANNULUS_SWAP; MOI_S35_COMBINE_R1; MOI_S35_FINAL_CELLS; MOI_S35_FINAL_R3];;

map type_of [MOI_S35_APPROX_R3; MOI_S35_FINAL_R3];;
map frees [MOI_S35_APPROX_R3; MOI_S35_FINAL_R3];;

(* The glue of pc_moi_s35_stmt_r2.ml with APPROX and FINAL replaced by      *)
(* their R3 forms: both separations produced with the 34.1 maps are passed  *)
(* through COMBINE (same ff) to FINAL.                                       *)

let MOI_S5D_351_FROM_CORES_R3 = prove
 (mk_imp(list_mk_conj [MOI_FND_DERIVED_NBHD_BASIC; rand MOI_S35_CHARTS;
                       rand MOI_S35_SOURCE; rand MOI_S35_APPROX_R3;
                       rand MOI_S35_COMBINE_R1; rand MOI_S35_FINAL_R3],
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
        (X_CHOOSE_THEN `cc:(real^N->bool)->real` STRIP_ASSUME_TAC))) THEN
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

let MOI_S5D_PROD_351_R3 = prove
 (mk_imp(list_mk_conj (MOI_FND_DERIVED_NBHD_BASIC :: MOI_FND_GRAPH_TUBE ::
                       MOI_S35_UNIT_TARGETS_R3),
         MOI_PROD_351),
  DISCH_THEN(fun hs ->
    match CONJUNCTS hs with
      [dnb; gt; tri; mrk; c341; fil; lsg; csg; one_e; two_e; slb; chs; src; apx;
       l1; one1; dsk; ann; cmb; fcl; fin] ->
        GEN_TAC THEN DISCH_THEN(fun ins ->
          match CONJUNCTS ins with
            [h341; _; h273; hsch; _] ->
              let gtt = CONJ gt tri in
              let rem = MP MOI_S5D_REMOVAL
                         (end_itlist CONJ [hsch; h273; slb; l1; one1; dsk; ann]) in
              let cores =
                end_itlist CONJ
                 [dnb; MP chs gtt; MP src gtt;
                  MP apx (end_itlist CONJ [h341; mrk; c341; fil; lsg; csg; gt; tri]);
                  MP cmb rem;
                  MP fin (end_itlist CONJ [gt; tri; fcl; one_e; two_e; lsg; hsch])] in
              ACCEPT_TAC (SPEC `u:N->bool` (MP MOI_S5D_351_FROM_CORES_R3 cores))
          | _ -> failwith "MOI_S5D_PROD_351_R3: producer antecedent")
    | _ -> failwith "MOI_S5D_PROD_351_R3: hypotheses"));;

