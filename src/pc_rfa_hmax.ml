(* ========================================================================= *)
(* Unit pc_rfa_hmax: the maximum principle for the perturbed Harnack         *)
(* quadratic.  At a first time where positive definiteness fails, the        *)
(* touching inequality (RFA_TOUCH_INEQ of pc_rfa_hext) and the push          *)
(* (RFA_PUSH_CHART of pc_rfa_hpush) contradict each other                    *)
(* (RFA_TOUCH_CONTRA); the global argument uses the barrier of pc_rfa_hbar.  *)
(* Main theorem: RFA_HARNACK_MATRIX, Hamilton's matrix Harnack in dimension  *)
(* 3 in chart form for a complete flow with the frame bounds of rfa_hset and *)
(* a Ricci bound.                                                            *)
(* ========================================================================= *)

needs "src/pc_rfa_hpush.ml";;
needs "src/pc_rfa_hbar.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Frame tools at a point.  The 1-jet of the extension fields                *)
(* in a frame (RFA_XU_JET_FRAME) and a witness that the hypotheses of        *)
(* RFA_HARNACK_DEFECT_3D_PERT are satisfiable with W not 0                   *)
(* (RFA_PERT_JET_SATISFIABLE); the frame forms of the perturbed form, of the *)
(* norm and of the positivity predicates (RFA_HZA_FT, RFA_NRM2_VAL,          *)
(* RFA_PQFORM_FT, RFA_HPD_CC_FT, RFA_HPSD_CC_FT); the shift identity         *)
(* (RFA_HZ_SHIFT) and the pointwise positivity of F + c N (RFA_PSD_FN); the  *)
(* time factors d exp(B (t - s)) and e exp(A (t - s)) / (t - s).             *)
(* ========================================================================= *)

let RFA_XU_JET_FRAME = prove
 (`!U (G:real^3->real^3^3) y0 (S:real^3^3) A0 w0 tau.
     metric_field U G /\ y0 IN U
     ==> !i j e.
           lnabla 2 G (rfa_xu G y0 A0 w0 tau) y0 (rfa_ft S [i; j; e]) =
           inv(&2) * (lric2 G y0 (rfa_ft S [e; i]) * rfa_xw G y0 w0 y0 (rfa_ft S [j]) -
                      lric2 G y0 (rfa_ft S [e; j]) * rfa_xw G y0 w0 y0 (rfa_ft S [i])) +
           inv(&4 * tau) * (lmetric2 G y0 (rfa_ft S [e; i]) * rfa_xw G y0 w0 y0 (rfa_ft S [j]) -
                            lmetric2 G y0 (rfa_ft S [e; j]) * rfa_xw G y0 w0 y0 (rfa_ft S [i]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y0:real^3`; `A0:real^3^3`;
                 `w0:real^3`; `tau:real`; `rfa_ft (S:real^3^3) [i; j; e]`] RFA_XU_NABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y0:real^3`; `w0:real^3`;
                 `rfa_ft (S:real^3^3) [i]`] RFA_XW_AT) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y0:real^3`; `w0:real^3`;
                 `rfa_ft (S:real^3^3) [j]`] RFA_XW_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[rfa_xform; lric2; lmetric2; RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH]);;

let RFA_PERT_JET_SATISFIABLE = prove
 (`!U a b (G:real->real^3->real^3^3) s t y (S:real^3^3).
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\ invertible S
     ==> ?Uf Wf. rfa_sf 2 U Uf /\ rfa_sf 1 U Wf /\
                 Wf y (rfa_ft S [1]) = &1 /\
                 (!i j. Uf y (rfa_ft S [i; j]) = --(Uf y (rfa_ft S [j; i]))) /\
                 (!w. lnabla 1 (G t) Wf y w = &0) /\
                 (!i j e. lnabla 2 (G t) Uf y (rfa_ft S [i; j; e]) =
                    inv(&2) * (lric2 (G t) y (rfa_ft S [e; i]) * Wf y (rfa_ft S [j]) -
                               lric2 (G t) y (rfa_ft S [e; j]) * Wf y (rfa_ft S [i])) +
                    inv(&4 * (t - s)) * (lmetric2 (G t) y (rfa_ft S [e; i]) * Wf y (rfa_ft S [j]) -
                                         lmetric2 (G t) y (rfa_ft S [e; j]) * Wf y (rfa_ft S [i])))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^3->real^3^3) t)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP LRG_FLOW_BASIC (ASSUME `lricci_flow U a b (G:real->real^3->real^3^3)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o el 4 o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w0 = matrix_inv(S:real^3^3) ** basis 1` THEN
  EXISTS_TAC `rfa_xu ((G:real->real^3->real^3^3) t) y (mat 0) w0 (t - s)` THEN
  EXISTS_TAC `rfa_xw ((G:real->real^3->real^3^3) t) y w0` THEN
  ASM_SIMP_TAC[RFA_SF_XU; RFA_SF_XW] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t`; `y:real^3`;
                 `S:real^3^3`; `mat 0:real^3^3`; `w0:real^3`; `t - s:real`] RFA_XU_JET_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `!w. lnabla 1 ((G:real->real^3->real^3^3) t) (rfa_xw (G t) y w0) y w = &0`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_XW_NABLA THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t`; `y:real^3`;
                 `mat 0:real^3^3`; `w0:real^3`; `t - s:real`] RFA_XU_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LZERO; DOT_RZERO; REAL_NEG_0] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t`; `y:real^3`; `w0:real^3`;
                 `rfa_ft (S:real^3^3) [1]`] RFA_XW_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL_CONS; ARITH] THEN
  EXPAND_TAC "w0" THEN REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
  SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_3; ARITH]);;

let RFA_HZA_FT = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t alpha beta (u:num->num->real) (w:num->real).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S
     ==> rfa_hza (rfa_ric_a G y S) (rfa_dr_a G y S) (rfa_ddr_a G y S) (t - s) alpha beta u w =
         rfa_hz 3 (\a b c d. lrm4 G y (rfa_ft S [a; b; d; c]) + alpha * rfa_i4 a b c d)
                  (\a b c. rfa_hP G y (rfa_ft S [a; b; c]))
                  (\a b. rfa_hM s t G y (rfa_ft S [a; b]) + beta * rfa_kd a b) u w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_hza] THEN MATCH_MP_TAC RFA_HZ_EQ THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `a:num`; `b:num`; `c:num`; `d:num`] RFA_LRM4_ARR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `a:num`; `b:num`; `c:num`] RFA_HP_ARR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `s:real`; `t:real`; `a:num`; `b:num`] RFA_HM_ARR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let RFA_NRM2_VAL_DERIVE asm w =
  let hs = map ASSUME (conjuncts asm) in
  let h k = el k hs in
  let mf = h 0 and h_y = h 1 and h_invS = h 2 and h_frame = h 3 in
  let sfs = [h 4; h 5] in
  let saved = RFA_ENGINE_SAVE () in
  RFA_ENGINE_RESET ();
  rfa_sf_bases := sfs @ [RFA_SF_LMETRIC2];
  rfa_sf_unfolds := [];
  rfa_lnf_unfolds := [rfa_nrm2];
  rfa_frv_unfolds := [rfa_nrm2];
  let gg = rand(concl mf) and uu = rand(rator(concl mf)) in
  let yv = rand(rator(concl h_y)) and sv = rand(rand(concl h_frame)) in
  let met_f = mk_comb(`lmetric2:(real^3->real^3^3)->real^3->(num->real^3)->real`, gg) in
  let h_all = end_itlist CONJ [mf; h_y; h_invS; h_frame] in
  let nm = mk_small_numeral in
  let hook tm =
    match (try Some(dest_comb(rator tm), rand tm) with Failure _ -> None) with
      Some((f, yy), wt) when yy = yv && rfa_is_ft wt && f = met_f ->
        let l = map dest_small_numeral (dest_list (rand wt)) in
        (match l with [i;j] -> MP (REWRITE_RULE[DIMINDEX_3; ARITH]
                                   (ISPECL [uu; gg; yv; sv; nm i; nm j] RFA_FT_METRIC)) h_all
         | _ -> failwith "met")
    | _ -> failwith "atom" in
  rfa_mp_hook := (fun t -> try hook t with Failure s -> failwith s
                                          | Match_failure _ -> failwith "atom");
  let res =
    try
      let th1 = RFA_FRV_CONV mf h_y h_frame (lhs w) in
      let nfl = TRANS th1 (RFA_MPOLY (rand(concl th1))) in
      let th2 = (REWRITE_CONV[] THENC DEPTH_CONV BETA_CONV) (rhs w) in
      let nfr = TRANS th2 (RFA_MPOLY (rand(concl th2))) in
      if aconv (rand(concl nfl)) (rand(concl nfr)) then TRANS nfl (SYM nfr)
      else failwith "RFA_NRM2_VAL_DERIVE: normal forms"
    with e -> (RFA_ENGINE_RESTORE saved; raise e) in
  RFA_ENGINE_RESTORE saved;
  itlist PROVE_HYP (CONJUNCTS (ASSUME asm)) res;;

let RFA_NRM2_VAL = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) Uf Wf (u:num->real^3).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     rfa_sf 2 U Uf /\ rfa_sf 1 U Wf
     ==> rfa_nrm2 G Uf Wf y u =
         sum(1..3) (\a. sum(1..3) (\b. Uf y (rfa_ft S [a; b]) pow 2)) +
         sum(1..3) (\a. Wf y (rfa_ft S [a]) pow 2)`,
  REPEAT GEN_TAC THEN
  W(fun (_, w) -> let a, c = dest_imp w in ACCEPT_TAC (DISCH a (RFA_NRM2_VAL_DERIVE a c))));;

let RFA_PQFORM_FT = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t pa pb Uf Wf (u:num->real^3).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     rfa_sf 2 U Uf /\ rfa_sf 1 U Wf
     ==> rfa_qform G (\y u. rfa_hM s t G y u + pb * lmetric2 G y u) (rfa_hP G)
                     (\y u. lrm4 G y u + pa * rfa_ifld G y u) Uf Wf y u =
         rfa_hz 3 (\a b c d. lrm4 G y (rfa_ft S [a; b; d; c]) + pa * rfa_i4 a b c d)
                  (\a b c. rfa_hP G y (rfa_ft S [a; b; c]))
                  (\a b. rfa_hM s t G y (rfa_ft S [a; b]) + pb * rfa_kd a b)
                  (\a b. Uf y (rfa_ft S [a; b])) (\a. Wf y (rfa_ft S [a]))`,
  REPEAT STRIP_TAC THEN
  W(fun (asl, w) ->
    let mf = ASSUME `metric_field U (G:real^3->real^3^3)` in
    let sfm = MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `s:real`; `t:real`]
                         RFA_SF_HM) mf
    and sfi = MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`] RFA_SF_IFLD) mf in
    let saved = RFA_ENGINE_SAVE () in
    RFA_ENGINE_RESET ();
    rfa_sf_bases := [sfm; sfi; RFA_SF_LRIC2; RFA_SF_LMETRIC2; RFA_SF_LRM4];
    rfa_sf_unfolds := [];
    let th1 = RFA_SF_PROVE mf `\y u. rfa_hM s t (G:real^3->real^3^3) y u + pb * lmetric2 G y u`
    and th2 = RFA_SF_PROVE mf `\y u. lrm4 (G:real^3->real^3^3) y u + pa * rfa_ifld G y u` in
    RFA_ENGINE_RESTORE saved;
    let thp = MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`] RFA_SF_HP) mf in
    MP_TAC (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                    `\y u. rfa_hM s t (G:real^3->real^3^3) y u + pb * lmetric2 G y u`;
                    `rfa_hP (G:real^3->real^3^3)`;
                    `\y u. lrm4 (G:real^3->real^3^3) y u + pa * rfa_ifld G y u`;
                    `Uf:real^3->(num->real^3)->real`; `Wf:real^3->(num->real^3)->real`;
                    `u:num->real^3`] RFA_QFORM_FRAME) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC; ACCEPT_TAC th1; ACCEPT_TAC th2; ACCEPT_TAC thp];
      DISCH_THEN SUBST1_TAC]) THEN
  MATCH_MP_TAC RFA_HZ_EQ THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `a:num`; `b:num`; `c:num`; `d:num`] RFA_IFLD_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `a:num`; `b:num`] RFA_FT_METRIC) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[rfa_kd]]);;

let RFA_NZ_SUMSQ = prove
 (`!(u:num->num->real) (w:num->real).
     ~((!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 ==> u i j = &0) /\
       (!i. 1 <= i /\ i <= 3 ==> w i = &0)) <=>
     &0 < sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) + sum(1..3) (\a. w a pow 2)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!x:real. &0 <= x pow 2 /\ (x pow 2 = &0 <=> x = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2; REAL_POW_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
  EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LT] THEN
    REWRITE_TAC[SUM_3] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(u:num->num->real) 1 1 = &0 /\ u 1 2 = &0 /\ u 1 3 = &0 /\ u 2 1 = &0 /\
      u 2 2 = &0 /\ u 2 3 = &0 /\ u 3 1 = &0 /\ u 3 2 = &0 /\ u 3 3 = &0 /\
      (w:num->real) 1 = &0 /\ w 2 = &0 /\ w 3 = &0`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN
      MATCH_MP_TAC(MESON[REAL_POW_EQ_0; ARITH_RULE `~(2 = 0)`]
        `!x:real. x pow 2 = &0 ==> x = &0`) THEN
      FIRST_X_ASSUM(fun th -> MP_TAC th THEN
        MAP_EVERY (fun t -> MP_TAC(CONJUNCT1(SPEC t (ASSUME
          `!x:real. &0 <= x pow 2 /\ (x pow 2 = &0 <=> x = &0)`))))
         [`(u:num->num->real) 1 1`; `(u:num->num->real) 1 2`; `(u:num->num->real) 1 3`;
          `(u:num->num->real) 2 1`; `(u:num->num->real) 2 2`; `(u:num->num->real) 2 3`;
          `(u:num->num->real) 3 1`; `(u:num->num->real) 3 2`; `(u:num->num->real) 3 3`;
          `(w:num->real) 1`; `(w:num->real) 2`; `(w:num->real) 3`]) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      RFA_INDEX_CASES_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN RFA_INDEX_CASES_TAC [`i:num`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN STRIP_TAC THEN UNDISCH_TAC
     `&0 < sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2)) +
           sum(1..3) (\a. (w:num->real) a pow 2)` THEN
    SUBGOAL_THEN `sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2)) = &0 /\
                  sum(1..3) (\a. (w:num->real) a pow 2) = &0`
    (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
    CONJ_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_EQ_0] THEN ARITH_TAC]);;

let RFA_HPD_CC_FT = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t alpha beta.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S
     ==> (rfa_hpd_cc G s t alpha beta y <=>
          !(u:num->num->real) (w:num->real).
            (!i j. u i j = --(u j i)) /\
            &0 < sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) + sum(1..3) (\a. w a pow 2)
            ==> &0 < rfa_hz 3
                      (\a b c d. lrm4 G y (rfa_ft S [a; b; d; c]) + alpha * rfa_i4 a b c d)
                      (\a b c. rfa_hP G y (rfa_ft S [a; b; c]))
                      (\a b. rfa_hM s t G y (rfa_ft S [a; b]) + beta * rfa_kd a b) u w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `alpha:real`; `beta:real`] RFA_HPD_CC_FR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rfa_hpd_fr; RFA_NZ_SUMSQ] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `alpha:real`; `beta:real`] RFA_HZA_FT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let RFA_HPSD_CC_FT = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t alpha beta.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S
     ==> (rfa_hpsd_cc G s t alpha beta y <=>
          !(u:num->num->real) (w:num->real).
            (!i j. u i j = --(u j i))
            ==> &0 <= rfa_hz 3
                      (\a b c d. lrm4 G y (rfa_ft S [a; b; d; c]) + alpha * rfa_i4 a b c d)
                      (\a b c. rfa_hP G y (rfa_ft S [a; b; c]))
                      (\a b. rfa_hM s t G y (rfa_ft S [a; b]) + beta * rfa_kd a b) u w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `alpha:real`; `beta:real`] RFA_HPSD_CC_FR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rfa_hpsd_fr] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `alpha:real`; `beta:real`] RFA_HZA_FT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let RFA_HZ_SHIFT = prove
 (`!(R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real)
    (u:num->num->real) (w:num->real) pa pb cc.
     (!i j. u i j = --(u j i))
     ==> rfa_hz 3 (\a b c d. R a b c d + (pa + cc) * rfa_i4 a b c d) P
                  (\a b. M a b + (pb + cc) * rfa_kd a b) u w =
         rfa_hz 3 (\a b c d. R a b c d + pa * rfa_i4 a b c d) P
                  (\a b. M a b + pb * rfa_kd a b) u w +
         cc * (sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) + sum(1..3) (\a. w a pow 2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`R:num->num->num->num->real`; `P:num->num->num->real`;
                 `M:num->num->real`; `u:num->num->real`; `w:num->real`;
                 `pa + cc:real`; `pb + cc:real`] RFA_HZ_PERTURB) THEN
  MP_TAC(ISPECL [`R:num->num->num->num->real`; `P:num->num->num->real`;
                 `M:num->num->real`; `u:num->num->real`; `w:num->real`;
                 `pa:real`; `pb:real`] RFA_HZ_PERTURB) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM rfa_kd] THEN DISCH_THEN SUBST1_TAC THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM rfa_kd] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RFA_XU_FT_ANTI = prove
 (`!(G:real^3->real^3^3) y0 A0 w0 tau.
     transp A0 = --A0
     ==> !z (S:real^3^3) i j.
           rfa_xu G y0 A0 w0 tau z (rfa_ft S [i; j]) =
           --(rfa_xu G y0 A0 w0 tau z (rfa_ft S [j; i]))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. rfa_xu (G:real^3->real^3^3) y0 A0 w0 tau z (rfa_ft (S:real^3^3) [a; b]) =
          rfa_xu G y0 A0 w0 tau z (\m. if m = 1 then transp S ** basis a
                                       else transp S ** basis b)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[rfa_xu; RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL_CONS; ARITH];
    MATCH_MP_TAC RFA_XU_ANTI THEN FIRST_ASSUM ACCEPT_TAC]);;

let RFA_FN_EVAL = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t pa pb cc Uf Wf (u:num->real^3).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     rfa_sf 2 U Uf /\ rfa_sf 1 U Wf /\
     (!i j. Uf y (rfa_ft S [i; j]) = --(Uf y (rfa_ft S [j; i])))
     ==> rfa_qform G (\y u. rfa_hM s t G y u + pb * lmetric2 G y u) (rfa_hP G)
                     (\y u. lrm4 G y u + pa * rfa_ifld G y u) Uf Wf y u +
         cc * rfa_nrm2 G Uf Wf y u =
         rfa_hz 3 (\a b c d. lrm4 G y (rfa_ft S [a; b; d; c]) + (pa + cc) * rfa_i4 a b c d)
                  (\a b c. rfa_hP G y (rfa_ft S [a; b; c]))
                  (\a b. rfa_hM s t G y (rfa_ft S [a; b]) + (pb + cc) * rfa_kd a b)
                  (\a b. Uf y (rfa_ft S [a; b])) (\a. Wf y (rfa_ft S [a]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `pa:real`; `pb:real`; `Uf:real^3->(num->real^3)->real`;
                 `Wf:real^3->(num->real^3)->real`; `u:num->real^3`] RFA_PQFORM_FT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                 `Uf:real^3->(num->real^3)->real`; `Wf:real^3->(num->real^3)->real`;
                 `u:num->real^3`] RFA_NRM2_VAL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`\a b c d. lrm4 (G:real^3->real^3^3) y (rfa_ft (S:real^3^3) [a; b; d; c])`;
                 `\a b c. rfa_hP (G:real^3->real^3^3) y (rfa_ft (S:real^3^3) [a; b; c])`;
                 `\a b. rfa_hM s t (G:real^3->real^3^3) y (rfa_ft (S:real^3^3) [a; b])`;
                 `\a b. (Uf:real^3->(num->real^3)->real) y (rfa_ft (S:real^3^3) [a; b])`;
                 `\a. (Wf:real^3->(num->real^3)->real) y (rfa_ft (S:real^3^3) [a])`;
                 `pa:real`; `pb:real`; `cc:real`] RFA_HZ_SHIFT) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN REFL_TAC);;

let RFA_PSD_FN = prove
 (`!U (G:real^3->real^3^3) y s t pa pb cc Uf Wf (u:num->real^3).
     metric_field U G /\ y IN U /\ rfa_sf 2 U Uf /\ rfa_sf 1 U Wf /\
     (!(S:real^3^3) i j. Uf y (rfa_ft S [i; j]) = --(Uf y (rfa_ft S [j; i]))) /\
     rfa_hpsd_cc G s t (pa + cc) (pb + cc) y
     ==> &0 <= rfa_qform G (\y u. rfa_hM s t G y u + pb * lmetric2 G y u) (rfa_hP G)
                          (\y u. lrm4 G y u + pa * rfa_ifld G y u) Uf Wf y u +
               cc * rfa_nrm2 G Uf Wf y u /\
         &0 <= rfa_nrm2 G Uf Wf y u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_METRIC_INV_FACTOR) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `pa:real`; `pb:real`; `cc:real`; `Uf:real^3->(num->real^3)->real`;
                 `Wf:real^3->(num->real^3)->real`; `u:num->real^3`] RFA_FN_EVAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o SPEC `S:real^3^3` o check (is_forall o concl));
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                 `Uf:real^3->(num->real^3)->real`; `Wf:real^3->(num->real^3)->real`;
                 `u:num->real^3`] RFA_NRM2_VAL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC THEN RFA_SUMSQ_POS_TAC THEN NO_TAC ORELSE
                           (MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN RFA_SUMSQ_POS_TAC)] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `pa + cc:real`; `pb + cc:real`] RFA_HPSD_CC_FT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o EQ_MP th o
    check (fun th' -> try fst(dest_const(fst(strip_comb(concl th')))) = "rfa_hpsd_cc"
                      with Failure _ -> false))) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_ACCEPT_TAC o SPEC `S:real^3^3` o check (is_forall o concl)));;

let RFA_AFFINE_TIME_SMOOTH = prove
 (`!(S:real^1->bool) B s0. open S ==> smooth_map_on S (\x. lift(B * (drop x - s0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(B * (drop x - s0))) = (\x:real^1. B % (x - lift s0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL; LIFT_SUB; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let RFA_EXP_TIME_SMOOTH = prove
 (`!(S:real^1->bool) c B s0.
     open S ==> smooth_map_on S (\x. lift(c * exp(B * (drop x - s0))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^1->bool`; `c:real`; `\x. lift(exp(B * (drop x - s0)))`]
         SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^1->bool`; `(:real^1)`; `\x. lift(B * (drop x - s0))`; `exp`]
         SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_EXP_1D] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[RFA_AFFINE_TIME_SMOOTH]);;

let RFA_EXPDIV_TIME_SMOOTH = prove
 (`!a b c A s0.
     s0 <= a
     ==> smooth_map_on (interval(lift a,lift b))
           (\x. lift(c * exp(A * (drop x - s0)) / (drop x - s0)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`interval(lift a,lift b)`; `c:real`;
                 `\x. lift(exp(A * (drop x - s0)) / (drop x - s0))`]
         SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[OPEN_INTERVAL] THEN
  MP_TAC(ISPECL [`interval(lift a,lift b)`; `\x. lift(exp(A * (drop x - s0)))`;
                 `\x. lift(drop x - s0)`] SMOOTH_MAP_ON_LIFT_DIV) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_INTERVAL] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`interval(lift a,lift b)`; `&1`; `A:real`; `s0:real`]
           RFA_EXP_TIME_SMOOTH) THEN
    REWRITE_TAC[OPEN_INTERVAL; REAL_MUL_LID];
    MP_TAC(ISPECL [`interval(lift a,lift b)`; `&1`; `s0:real`] RFA_AFFINE_TIME_SMOOTH) THEN
    REWRITE_TAC[OPEN_INTERVAL; REAL_MUL_LID];
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC]);;

let RFA_EXP_TIME_DERIV = prove
 (`!c B s0 t. ((\t. c * exp(B * (t - s0))) has_real_derivative
               (B * (c * exp(B * (t - s0))))) (atreal t)`,
  REPEAT GEN_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC);;

let RFA_EXPDIV_TIME_DERIV = prove
 (`!c A s0 t. s0 < t
              ==> ((\t. c * exp(A * (t - s0)) / (t - s0)) has_real_derivative
                   (A * (c * exp(A * (t - s0)) / (t - s0)) -
                    (c * exp(A * (t - s0)) / (t - s0)) / (t - s0))) (atreal t)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(t - s0 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The contradiction at a touching point (RFA_TOUCH_CONTRA).                 *)
(* In a chart flow, at (T0, y0) with a nonzero null vector of the perturbed *)
(* form, positive semidefiniteness at time T0 near y0 and at earlier times   *)
(* at y0, the barrier data (q, psi0, C) and the constants of                 *)
(* RFA_PUSH_COEFFS, the extension fields give a quantity that RFA_TOUCH_INEQ *)
(* bounds by 0 and RFA_PUSH_CHART shows positive.                            *)
(* ========================================================================= *)

let RFA_TOUCH_CONTRA = prove
 (`!U a b (G:real->real^3->real^3^3) s T0 y0 (S:real^3^3) (u0:num->num->real) (w0:num->real)
    (psiC:real->real^3->real) W q dl C psi0 dd e eta tau0 tauM KR KP KM0 K CZ B A L.
     lricci_flow U a b G /\ s <= a /\ a < T0 /\ T0 < b /\ y0 IN U /\
     invertible S /\ matrix_inv(G T0 y0) = transp S ** S /\
     &0 <= KR /\ &0 <= KP /\ &0 <= KM0 /\ &0 <= K /\ &0 <= C /\
     &0 < e /\ &0 < dd /\ &0 < eta /\ &0 < tau0 /\ tau0 <= T0 - s /\ T0 - s <= tauM /\
     B = &12 * KP + &324 * KR + &2 /\ A = &18 * KR + &2 /\
     CZ = &3 * (KM0 + K / (&2 * tau0)) + &9 * KP + &9 * KR /\
     L = &2 * C + &2 * ((C + &1) * (&5 * K + inv tau0)) +
         (&6 * (KM0 + K / (&2 * tau0)) + &36 * KP) + (&12 * KP + &324 * KR) + &2 +
         &2 * (e * exp(A * tauM) / tau0) + &2 * CZ + &18 * KR +
         &2 * (&18 * K pow 2 + inv(&2 * tau0 pow 2)) + &1 /\
     dd * exp(B * tauM) <= &1 /\
     dd * exp(B * tauM) *
       (tauM pow 2 * (&6 * KM0 + &36 * KP + &36 * K pow 2) + &3 * K * tauM + &1) < e /\
     (!i j. u0 i j = --(u0 j i)) /\
     &0 < sum(1..3) (\a. sum(1..3) (\b. u0 a b pow 2)) + sum(1..3) (\a. w0 a pow 2) /\
     rfa_hz 3 (\a b c d. lrm4 (G T0) y0 (rfa_ft S [a; b; d; c]) +
                         (dd * exp(B * (T0 - s)) + eta * exp(L * (T0 - s)) * psi0) *
                         rfa_i4 a b c d)
              (\a b c. rfa_hP (G T0) y0 (rfa_ft S [a; b; c]))
              (\a b. rfa_hM s T0 (G T0) y0 (rfa_ft S [a; b]) +
                     (e * exp(A * (T0 - s)) / (T0 - s) + eta * exp(L * (T0 - s)) * psi0) *
                     rfa_kd a b) u0 w0 = &0 /\
     open W /\ y0 IN W /\ W SUBSET U /\
     (!y. y IN W
          ==> rfa_hpsd_cc (G T0) s T0
                (dd * exp(B * (T0 - s)) + eta * exp(L * (T0 - s)) * psiC T0 y)
                (e * exp(A * (T0 - s)) / (T0 - s) + eta * exp(L * (T0 - s)) * psiC T0 y) y) /\
     smooth_map_on W (\y. lift(q y)) /\ (!y. y IN W ==> psiC T0 y <= q y) /\
     q y0 = psi0 /\ psiC T0 y0 = psi0 /\ &1 <= psi0 /\
     llap (G T0) q y0 <= C * psi0 /\ lgrad2 (G T0) q y0 <= C * psi0 pow 2 /\
     &0 < dl /\ a <= T0 - dl /\
     (!t. T0 - dl < t /\ t < T0
          ==> rfa_hpsd_cc (G t) s t
                (dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * psiC t y0)
                (e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psiC t y0) y0 /\
              psiC t y0 <= psi0 * (&1 + C * (T0 - t))) /\
     (!a b c d. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
                1 <= d /\ d <= 3
                ==> abs(lrm4 (G T0) y0 (rfa_ft S [a; b; d; c])) <= KR) /\
     (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
              ==> abs(rfa_hP (G T0) y0 (rfa_ft S [a; b; c])) <= KP) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
            ==> abs(rfa_hM s T0 (G T0) y0 (rfa_ft S [a; b]) -
                    inv(&2 * (T0 - s)) * lric2 (G T0) y0 (rfa_ft S [a; b])) <= KM0) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
            ==> abs(lric2 (G T0) y0 (rfa_ft S [a; b])) <= K)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[REAL_ARITH `x = --y <=> x + y = &0`] o
    check (fun th -> concl th = `!i j. (u0:num->num->real) i j = --(u0 j i)`)) THEN
  SUBGOAL_THEN `!i j. (u0:num->num->real) i j = --(u0 j i)` (LABEL_TAC "anti0") THENL
   [REPEAT GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o
      check (fun th -> concl th = `!i j. (u0:num->num->real) i j + u0 j i = &0`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "anti0" (fun th ->
    SUBGOAL_THEN `transp((lambda i j. (u0:num->num->real) i j):real^3^3) = --(lambda i j. u0 i j)`
    ASSUME_TAC THENL [MATCH_MP_TAC RFA_LAMBDA_ANTI THEN ACCEPT_TAC th; ALL_TAC]) THEN
  MP_TAC(MATCH_MP LRG_FLOW_BASIC (ASSUME `lricci_flow U a b (G:real->real^3->real^3^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^3->real^3^3) T0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < T0 - s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the extension fields *)
  ABBREV_TAC `A0 = matrix_inv(S:real^3^3) ** ((lambda i j. (u0:num->num->real) i j):real^3^3) **
                   transp(matrix_inv S)` THEN
  ABBREV_TAC `wv = matrix_inv(S:real^3^3) ** ((lambda i. (w0:num->real) i):real^3)` THEN
  SUBGOAL_THEN `transp(A0:real^3^3) = --A0` ASSUME_TAC THENL
   [EXPAND_TAC "A0" THEN MATCH_MP_TAC RFA_CONJ_ANTI THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Uf = rfa_xu ((G:real->real^3->real^3^3) T0) y0 A0 wv (T0 - s)` THEN
  ABBREV_TAC `Wf = rfa_xw ((G:real->real^3->real^3^3) T0) y0 wv` THEN
  SUBGOAL_THEN `rfa_sf 2 U (Uf:real^3->(num->real^3)->real) /\
                rfa_sf 1 U (Wf:real^3->(num->real^3)->real)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Uf"; "Wf"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_SF_XU; MATCH_MP_TAC RFA_SF_XW] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                       ==> (Uf:real^3->(num->real^3)->real) y0 (rfa_ft S [i; j]) = u0 i j) /\
                (!i. 1 <= i /\ i <= 3 ==> (Wf:real^3->(num->real^3)->real) y0 (rfa_ft S [i]) = w0 i)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Uf"; "Wf"] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) T0`; `y0:real^3`;
                     `A0:real^3^3`; `wv:real^3`; `T0 - s:real`; `rfa_ft (S:real^3^3) [i; j]`]
             RFA_XU_AT);
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) T0`; `y0:real^3`;
                     `wv:real^3`; `rfa_ft (S:real^3^3) [i]`] RFA_XW_AT)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[RFA_FT_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL_CONS; ARITH] THENL
     [REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `(S:real^3^3) ** (A0:real^3^3) ** transp S = (lambda i j. (u0:num->num->real) i j)`
      MP_TAC THENL [EXPAND_TAC "A0" THEN MATCH_MP_TAC RFA_CONJ_INV THEN FIRST_ASSUM ACCEPT_TAC;
                    ALL_TAC] THEN
      REWRITE_TAC[MATRIX_MUL_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_3; LAMBDA_BETA] THEN
      ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3; LAMBDA_BETA];
      REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
      EXPAND_TAC "wv" THEN
      ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
      ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3; LAMBDA_BETA]];
    ALL_TAC] THEN
  (* antisymmetry of the field and its 1-jet *)
  SUBGOAL_THEN `!z (S':real^3^3) i j. (Uf:real^3->(num->real^3)->real) z (rfa_ft S' [i; j]) =
                                      --(Uf z (rfa_ft S' [j; i]))` ASSUME_TAC THENL
   [EXPAND_TAC "Uf" THEN MATCH_MP_TAC RFA_XU_FT_ANTI THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* the heat families *)
  ABBREV_TAC `HU = \t:real. \y:real^3. \v:num->real^3.
                 rfa_rcact 2 ((G:real->real^3->real^3^3) t) Uf y v - ltlap 2 (G t) Uf y v` THEN
  ABBREV_TAC `HW = \t:real. \y:real^3. \v:num->real^3.
                 rfa_rcact 1 ((G:real->real^3->real^3^3) t) Wf y v - ltlap 1 (G t) Wf y v` THEN
  SUBGOAL_THEN `rfa_heat 2 U a b (G:real->real^3->real^3^3) (\t. Uf) HU` ASSUME_TAC THENL
   [EXPAND_TAC "HU" THEN MATCH_MP_TAC RFA_HEAT_STATIC THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `rfa_sf 2 U (Uf:real^3->(num->real^3)->real)` THEN REWRITE_TAC[rfa_sf]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfa_heat 1 U a b (G:real->real^3->real^3^3) (\t. Wf) HW` ASSUME_TAC THENL
   [EXPAND_TAC "HW" THEN MATCH_MP_TAC RFA_HEAT_STATIC THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `rfa_sf 1 U (Wf:real^3->(num->real^3)->real)` THEN REWRITE_TAC[rfa_sf]];
    ALL_TAC] THEN
  ABBREV_TAC `pa = \t. dd * exp(B * (t - s))` THEN
  ABBREV_TAC `pb = \t. e * exp(A * (t - s)) / (t - s)` THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`; `s:real`;
                 `pa:real->real`; `\t. B * (pa:real->real) t`;
                 `pb:real->real`; `\t. A * (pb:real->real) t - pb t / (t - s)`;
                 `\t:real. (Uf:real^3->(num->real^3)->real)`; `HU:real->real^3->(num->real^3)->real`;
                 `\t:real. (Wf:real^3->(num->real^3)->real)`; `HW:real->real^3->(num->real^3)->real`]
         RFA_HEAT_PQUAD) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "pa" THEN REWRITE_TAC[] THEN
      REWRITE_TAC[RFA_EXP_TIME_DERIV];
      EXPAND_TAC "pa" THEN REWRITE_TAC[] THEN MATCH_MP_TAC RFA_EXP_TIME_SMOOTH THEN
      REWRITE_TAC[OPEN_INTERVAL];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "pb" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_EXPDIV_TIME_DERIV THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "pb" THEN REWRITE_TAC[] THEN MATCH_MP_TAC RFA_EXPDIV_TIME_SMOOTH THEN
      FIRST_ASSUM ACCEPT_TAC];
    BETA_TAC THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                 `\t:real. (Uf:real^3->(num->real^3)->real)`; `HU:real->real^3->(num->real^3)->real`;
                 `\t:real. (Wf:real^3->(num->real^3)->real)`; `HW:real->real^3->(num->real^3)->real`]
         RFA_HEAT_NRM2) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; BETA_TAC THEN DISCH_TAC] THEN
  (* expand the time factors *)
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `pa:real->real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `pb:real->real`)) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  (* the touching inequality *)
  W(fun (asl, w) ->
    let heat0 = filter (fun (_, th) ->
      try let f, args = strip_comb (concl th) in
          fst(dest_const f) = "rfa_heat" && hd args = `0`
      with Failure _ -> false) asl in
    let pick name = snd(find (fun (_, th) ->
      can (find_term (fun t -> try fst(dest_const t) = name with Failure _ -> false))
          (concl th)) heat0) in
    let thF = pick "rfa_qform" and thN = pick "rfa_nrm2" in
    let argsF = rfa_heat_args thF and argsN = rfa_heat_args thN in
    MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                   el 5 argsF; el 6 argsF; el 5 argsN; el 6 argsN;
                   `\t. eta * exp(L * (t - s))`; `L * (eta * exp(L * (T0 - s)))`;
                   `C:real`; `psi0:real`; `W:real^3->bool`; `q:real^3->real`; `T0:real`;
                   `y0:real^3`; `(\m:num. vec 0:real^3)`; `dl:real`] RFA_TOUCH_INEQ)) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [(* the time factor *)
      MATCH_ACCEPT_TAC RFA_EXP_TIME_DERIV;
      (* the space test *)
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) T0`; `y:real^3`; `s:real`;
                     `T0:real`; `dd * exp(B * (T0 - s))`; `e * exp(A * (T0 - s)) / (T0 - s)`;
                     `eta * exp(L * (T0 - s)) * (psiC:real->real^3->real) T0 y`;
                     `Uf:real^3->(num->real^3)->real`; `Wf:real^3->(num->real^3)->real`;
                     `(\m:num. vec 0:real^3)`] RFA_PSD_FN) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
         [ASM SET_TAC[];
          FIRST_ASSUM(fun th -> ACCEPT_TAC(SPEC `y:real^3` th));
          FIRST_ASSUM(fun th -> ACCEPT_TAC(MP (SPEC `y:real^3` th)
                                              (ASSUME `(y:real^3) IN W`)))];
        STRIP_TAC] THEN
      SUBGOAL_THEN `&0 <= (eta * exp(L * (T0 - s))) *
                          ((q:real^3->real) y - psiC T0 y) *
                          rfa_nrm2 ((G:real->real^3->real^3^3) T0) Uf Wf y (\m. vec 0)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_SUB_LE]];
        ALL_TAC] THEN
      UNDISCH_TAC `&0 <=
        rfa_qform ((G:real->real^3->real^3^3) T0)
          (\y u. rfa_hM s T0 (G T0) y u + (e * exp(A * (T0 - s)) / (T0 - s)) * lmetric2 (G T0) y u)
          (rfa_hP (G T0))
          (\y u. lrm4 (G T0) y u + (dd * exp(B * (T0 - s))) * rfa_ifld (G T0) y u)
          Uf Wf y (\m. vec 0) +
        (eta * exp(L * (T0 - s)) * (psiC:real->real^3->real) T0 y) *
        rfa_nrm2 (G T0) Uf Wf y (\m. vec 0)` THEN
      REAL_ARITH_TAC;
      (* the time test *)
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `metric_field U ((G:real->real^3->real^3^3) t)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `metric_field:(real^3->bool)->(real^3->real^3^3)->bool`))
              (concl th) && is_forall (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> if can (find_term ((=) `dl:real`)) (concl th) && is_forall (concl th)
                              then MP_TAC(SPEC `t:real` th) else failwith "no") THEN
      ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t`; `y0:real^3`; `s:real`;
                     `t:real`; `dd * exp(B * (t - s))`; `e * exp(A * (t - s)) / (t - s)`;
                     `eta * exp(L * (t - s)) * (psiC:real->real^3->real) t y0`;
                     `Uf:real^3->(num->real^3)->real`; `Wf:real^3->(num->real^3)->real`;
                     `(\m:num. vec 0:real^3)`] RFA_PSD_FN) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        FIRST_ASSUM(fun th -> ACCEPT_TAC(SPEC `y0:real^3` th));
        STRIP_TAC] THEN
      SUBGOAL_THEN `&0 <= (eta * exp(L * (t - s))) *
                          (psi0 * (&1 + C * (T0 - t)) - (psiC:real->real^3->real) t y0) *
                          rfa_nrm2 ((G:real->real^3->real^3^3) t) Uf Wf y0 (\m. vec 0)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_SUB_LE]];
        ALL_TAC] THEN
      UNDISCH_TAC `&0 <=
        rfa_qform ((G:real->real^3->real^3^3) t)
          (\y u. rfa_hM s t (G t) y u + (e * exp(A * (t - s)) / (t - s)) * lmetric2 (G t) y u)
          (rfa_hP (G t))
          (\y u. lrm4 (G t) y u + (dd * exp(B * (t - s))) * rfa_ifld (G t) y u)
          Uf Wf y0 (\m. vec 0) +
        (eta * exp(L * (t - s)) * (psiC:real->real^3->real) t y0) *
        rfa_nrm2 (G t) Uf Wf y0 (\m. vec 0)` THEN
      REAL_ARITH_TAC;
      (* the null condition *)
      MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) T0`; `y0:real^3`;
                     `S:real^3^3`; `s:real`; `T0:real`; `dd * exp(B * (T0 - s))`;
                     `e * exp(A * (T0 - s)) / (T0 - s)`; `eta * exp(L * (T0 - s)) * psi0`;
                     `Uf:real^3->(num->real^3)->real`; `Wf:real^3->(num->real^3)->real`;
                     `(\m:num. vec 0:real^3)`] RFA_FN_EVAL) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        FIRST_ASSUM(fun th -> ACCEPT_TAC(SPECL [`y0:real^3`; `S:real^3^3`] th));
        ALL_TAC] THEN
      SUBGOAL_THEN
       `rfa_hz 3 (\a b c d. lrm4 ((G:real->real^3->real^3^3) T0) y0 (rfa_ft S [a; b; d; c]) +
                            (dd * exp(B * (T0 - s)) + eta * exp(L * (T0 - s)) * psi0) *
                            rfa_i4 a b c d)
                 (\a b c. rfa_hP (G T0) y0 (rfa_ft S [a; b; c]))
                 (\a b. rfa_hM s T0 (G T0) y0 (rfa_ft S [a; b]) +
                        (e * exp(A * (T0 - s)) / (T0 - s) + eta * exp(L * (T0 - s)) * psi0) *
                        rfa_kd a b)
                 (\a b. (Uf:real^3->(num->real^3)->real) y0 (rfa_ft S [a; b]))
                 (\a. (Wf:real^3->(num->real^3)->real) y0 (rfa_ft S [a])) = &0`
      MP_TAC THENL
       [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `&0` &&
                                   can (find_term ((=) `u0:num->num->real`)) (lhs(concl th)) &&
                                   can (find_term ((=) `rfa_hz:num->(num->num->num->num->real)->(num->num->num->real)->(num->num->real)->(num->num->real)->(num->real)->real`)) (concl th)
                                then GEN_REWRITE_TAC RAND_CONV [SYM th] else failwith "no") THEN
        MATCH_MP_TAC RFA_HZ_EQ THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
        REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REAL_ARITH_TAC];
    DISCH_TAC] THEN
  (* the push: the same quantity is positive *)
  SUBGOAL_THEN `rfa_sf 2 U ((HU:real->real^3->(num->real^3)->real) T0) /\
                rfa_sf 1 U ((HW:real->real^3->(num->real^3)->real) T0)` STRIP_ASSUME_TAC THENL
   [(let fin = ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; MESON_TAC[]] in
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`2`; `U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                     `\t:real. (Uf:real^3->(num->real^3)->real)`;
                     `HU:real->real^3->(num->real^3)->real`; `T0:real`] RFA_HEAT_SF_AT) THEN fin;
      MP_TAC(ISPECL [`1`; `U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                     `\t:real. (Wf:real^3->(num->real^3)->real)`;
                     `HW:real->real^3->(num->real^3)->real`; `T0:real`] RFA_HEAT_SF_AT) THEN fin]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> abs(rfa_hM s T0 ((G:real->real^3->real^3^3) T0) y0 (rfa_ft S [i; j])) <=
              KM0 + K / (&2 * (T0 - s))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th ->
      can (find_term ((=) `KM0:real`)) (concl th) && is_forall (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th ->
      can (find_term ((=) `K:real`)) (concl th) && is_forall (concl th) &&
      not (can (find_term ((=) `KM0:real`)) (concl th)) &&
      can (find_term ((=) `lric2:(real^3->real^3^3)->real^3->(num->real^3)->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < inv(&2 * (T0 - s))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    ABBREV_TAC `iv = inv(&2 * (T0 - s))` THEN
    ABBREV_TAC `r = lric2 ((G:real->real^3->real^3^3) T0) y0 (rfa_ft S [i; j])` THEN
    ABBREV_TAC `m = rfa_hM s T0 ((G:real->real^3->real^3^3) T0) y0 (rfa_ft S [i; j])` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `abs(iv * r) <= K * iv` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs iv = iv` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. (u0:num->num->real) i j = --(u0 j i)` (LABEL_TAC "anti0") THENL
   [REPEAT GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o
      check (fun th -> concl th = `!i j. (u0:num->num->real) i j + u0 j i = &0`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eta * exp(L * (T0 - s)) * psi0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* c <= CZ at the null vector *)
  SUBGOAL_THEN `eta * exp(L * (T0 - s)) * psi0 <= CZ` ASSUME_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
     [`\a b c d. lrm4 ((G:real->real^3->real^3^3) T0) y0 (rfa_ft (S:real^3^3) [a; b; d; c])`;
      `\a b c. rfa_hP ((G:real->real^3->real^3^3) T0) y0 (rfa_ft (S:real^3^3) [a; b; c])`;
      `\a b. rfa_hM s T0 ((G:real->real^3->real^3^3) T0) y0 (rfa_ft (S:real^3^3) [a; b])`;
      `u0:num->num->real`; `w0:num->real`; `dd * exp(B * (T0 - s))`;
      `e * exp(A * (T0 - s)) / (T0 - s)`; `eta * exp(L * (T0 - s)) * psi0`;
      `KR:real`; `KP:real`; `KM0 + K / (&2 * (T0 - s))`] RFA_NULL_C_LE)) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div] THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        TRY(MATCH_MP_TAC REAL_LE_INV) THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
        ASM_REAL_ARITH_TAC;
        FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `&0` &&
                                 can (find_term ((=) `u0:num->num->real`)) (lhs(concl th))
                              then MP_TAC th else failwith "no") THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    UNDISCH_TAC `CZ = &3 * (KM0 + K / (&2 * tau0)) + &9 * KP + &9 * KR` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> &3 * (m + x) + p <= &3 * (m + y) + p`) THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the constants *)
  MP_TAC(ISPECL [`KR:real`; `KP:real`; `KM0:real`; `K:real`; `C:real`; `CZ:real`; `e:real`;
                 `dd:real`; `tau0:real`; `tauM:real`; `T0 - s:real`;
                 `(eta * exp(L * (T0 - s))) * psi0`; `B:real`; `A:real`;
                 `dd * exp(B * (T0 - s))`; `e * exp(A * (T0 - s)) / (T0 - s)`;
                 `KM0 + K / (&2 * (T0 - s))`; `(C + &1) * (&5 * K + inv(T0 - s))`; `L:real`]
         RFA_PUSH_COEFFS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST [UNDISCH_TAC `CZ = &3 * (KM0 + K / (&2 * tau0)) + &9 * KP + &9 * KR` THEN
           DISCH_THEN SUBST1_TAC THEN
           SUBGOAL_THEN `&0 <= K / (&2 * tau0)` MP_TAC THENL
            [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
           ASM_REAL_ARITH_TAC;
           ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  (* the push *)
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`; `s:real`;
                 `T0:real`; `y0:real^3`; `S:real^3^3`; `Uf:real^3->(num->real^3)->real`;
                 `(HU:real->real^3->(num->real^3)->real) T0`; `Wf:real^3->(num->real^3)->real`;
                 `(HW:real->real^3->(num->real^3)->real) T0`; `(\m:num. vec 0:real^3)`;
                 `q:real^3->real`; `dd * exp(B * (T0 - s))`; `B * (dd * exp(B * (T0 - s)))`;
                 `e * exp(A * (T0 - s)) / (T0 - s)`;
                 `A * (e * exp(A * (T0 - s)) / (T0 - s)) -
                  (e * exp(A * (T0 - s)) / (T0 - s)) / (T0 - s)`;
                 `eta * exp(L * (T0 - s))`; `L * (eta * exp(L * (T0 - s)))`; `psi0:real`;
                 `C:real`; `KR:real`; `KP:real`; `KM0 + K / (&2 * (T0 - s))`; `K:real`;
                 `B:real`; `A:real`; `L:real`; `(C + &1) * (&5 * K + inv(T0 - s))`]
         RFA_PUSH_CHART) THEN
  SUBGOAL_THEN
   `rfa_hz 3 (\a b c d. lrm4 ((G:real->real^3->real^3^3) T0) y0 (rfa_ft S [a; b; d; c]) +
                        (dd * exp(B * (T0 - s)) + (eta * exp(L * (T0 - s))) * psi0) *
                        rfa_i4 a b c d)
             (\a b c. rfa_hP (G T0) y0 (rfa_ft S [a; b; c]))
             (\a b. rfa_hM s T0 (G T0) y0 (rfa_ft S [a; b]) +
                    (e * exp(A * (T0 - s)) / (T0 - s) + (eta * exp(L * (T0 - s))) * psi0) *
                    rfa_kd a b)
             (\a b. (Uf:real^3->(num->real^3)->real) y0 (rfa_ft S [a; b]))
             (\a. (Wf:real^3->(num->real^3)->real) y0 (rfa_ft S [a])) = &0`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `&0` &&
                               can (find_term ((=) `u0:num->num->real`)) (lhs(concl th)) &&
                               can (find_term ((=) `rfa_hz:num->(num->num->num->num->real)->(num->num->num->real)->(num->num->real)->(num->num->real)->(num->real)->real`)) (concl th)
                            then GEN_REWRITE_TAC RAND_CONV [SYM th] else failwith "no") THEN
    MATCH_MP_TAC RFA_HZ_EQ THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < sum(1..3) (\a. sum(1..3) (\b. (Uf:real^3->(num->real^3)->real) y0 (rfa_ft S [a; b]) pow 2)) +
         sum(1..3) (\a. (Wf:real^3->(num->real^3)->real) y0 (rfa_ft S [a]) pow 2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `sum(1..3) (\a. sum(1..3) (\b. (Uf:real^3->(num->real^3)->real) y0 (rfa_ft S [a; b]) pow 2)) =
      sum(1..3) (\a. sum(1..3) (\b. (u0:num->num->real) a b pow 2)) /\
      sum(1..3) (\a. (Wf:real^3->(num->real^3)->real) y0 (rfa_ft S [a]) pow 2) =
      sum(1..3) (\a. (w0:num->real) a pow 2)`
    (fun th -> REWRITE_TAC[th] THEN FIRST_ASSUM ACCEPT_TAC) THEN
    CONJ_TAC THEN REPEAT(MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST
     [FIRST_ASSUM ACCEPT_TAC; REFL_TAC;
      FIRST_ASSUM(fun th -> ACCEPT_TAC(SPECL [`y0:real^3`; `S:real^3^3`] th));
      (GEN_TAC THEN EXPAND_TAC "Wf" THEN MATCH_MP_TAC RFA_XW_NABLA THEN
       EXISTS_TAC `U:real^3->bool` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC);
      (MAP_EVERY EXPAND_TAC ["Uf"; "Wf"] THEN MATCH_MP_TAC RFA_XU_JET_FRAME THEN
       EXISTS_TAC `U:real^3->bool` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC);
      (MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) T0`; `y0:real^3`;
                      `S:real^3^3`; `s:real`; `T0:real`;
                      `dd * exp(B * (T0 - s)) + (eta * exp(L * (T0 - s))) * psi0`;
                      `e * exp(A * (T0 - s)) / (T0 - s) + (eta * exp(L * (T0 - s))) * psi0`]
              RFA_HPSD_CC_FT) THEN
       ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
       DISCH_THEN(SUBST1_TAC o SYM) THEN
       SUBGOAL_THEN `(eta * exp(L * (T0 - s))) * psi0 =
                     eta * exp(L * (T0 - s)) * (psiC:real->real^3->real) T0 y0`
       SUBST1_TAC THENL
        [UNDISCH_TAC `(psiC:real->real^3->real) T0 y0 = psi0` THEN DISCH_THEN SUBST1_TAC THEN
         REWRITE_TAC[REAL_MUL_ASSOC];
         ALL_TAC] THEN
       FIRST_ASSUM(fun th -> ACCEPT_TAC(MP (SPEC `y0:real^3` th) (ASSUME `(y0:real^3) IN W`)))
       THEN NO_TAC);
      (REWRITE_TAC[real_div] THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
       TRY(MATCH_MP_TAC REAL_LE_INV) THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
       ASM_REAL_ARITH_TAC THEN NO_TAC);
      ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_lt" (concl th) &&
     can (find_term (fun t -> try fst(dest_const t) = "rfa_hqform" with Failure _ -> false))
         (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th) &&
     can (find_term (fun t -> try fst(dest_const t) = "rfa_hqform" with Failure _ -> false))
         (concl th))) THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Positivity of the perturbed form in a chart.  At small times              *)
(* (RFA_HPD_SMALL_CC: R(u,u) >= 0, Ric >= 0 and beta large against alpha),   *)
(* for a large barrier coefficient c (RFA_HPD_LARGE_CC), and a nonzero null  *)
(* vector where the form is semidefinite but not definite                   *)
(* (RFA_NULL_EXISTS_CC).                                                     *)
(* ========================================================================= *)

let RFA_HPD_SMALL_CC = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t alpha beta KM0 KP.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\ s < t /\
     (!u. (!i j. u i j = --(u j i))
          ==> &0 <= sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
                       lrm4 G y (rfa_ft S [a; b; d; c]) * u a b * u d c))))) /\
     (!w. &0 <= sum(1..3) (\a. sum(1..3) (\b. lric2 G y (rfa_ft S [a; b]) * w a * w b))) /\
     (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
              ==> abs(rfa_hP G y (rfa_ft S [a; b; c])) <= KP) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
            ==> abs(rfa_hM s t G y (rfa_ft S [a; b]) -
                    inv(&2 * (t - s)) * lric2 G y (rfa_ft S [a; b])) <= KM0) /\
     &0 < alpha /\ &3 * KM0 + &9 * KP * (&6 * KP + &1) / alpha < beta
     ==> rfa_hpd_cc G s t alpha beta y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `alpha:real`; `beta:real`] RFA_HPD_CC_FT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:num->num->real`; `w:num->real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\a b c d. lrm4 (G:real^3->real^3^3) y (rfa_ft (S:real^3^3) [a; b; d; c])`;
    `\a b c. rfa_hP (G:real^3->real^3^3) y (rfa_ft (S:real^3^3) [a; b; c])`;
    `\a b. rfa_hM s t (G:real^3->real^3^3) y (rfa_ft (S:real^3^3) [a; b]) -
           inv(&2 * (t - s)) * lric2 G y (rfa_ft S [a; b])`;
    `\a b. lric2 (G:real^3->real^3^3) y (rfa_ft (S:real^3^3) [a; b])`;
    `u:num->num->real`; `w:num->real`; `t - s:real`; `alpha:real`; `beta:real`;
    `KM0:real`; `KP:real`] RFA_HZ_PD_SMALL) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_REAL_ARITH_TAC THEN
    TRY(FIRST_ASSUM(fun th -> ACCEPT_TAC(SPEC `w:num->real` th))) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      is_imp(snd(dest_forall(concl th))) &&
      can (find_term ((=) `lrm4:(real^3->real^3^3)->real^3->(num->real^3)->real`)) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> &0 < a ==> &0 < b`) THEN
  MATCH_MP_TAC RFA_HZ_EQ THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let RFA_HPD_LARGE_CC = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t pa pb cc KR KP KM.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     (!a b c d. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
                1 <= d /\ d <= 3 ==> abs(lrm4 G y (rfa_ft S [a; b; d; c])) <= KR) /\
     (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
              ==> abs(rfa_hP G y (rfa_ft S [a; b; c])) <= KP) /\
     (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
            ==> abs(rfa_hM s t G y (rfa_ft S [a; b])) <= KM) /\
     &0 <= pa /\ &0 <= pb /\ &3 * KM + &9 * KP + &9 * KR < cc
     ==> rfa_hpd_cc G s t (pa + cc) (pb + cc) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `pa + cc:real`; `pb + cc:real`] RFA_HPD_CC_FT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:num->num->real`; `w:num->real`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\a b c d. lrm4 (G:real^3->real^3^3) y (rfa_ft (S:real^3^3) [a; b; d; c])`;
    `\a b c. rfa_hP (G:real^3->real^3^3) y (rfa_ft (S:real^3^3) [a; b; c])`;
    `\a b. rfa_hM s t (G:real^3->real^3^3) y (rfa_ft (S:real^3^3) [a; b])`;
    `u:num->num->real`; `w:num->real`; `pa:real`; `pb:real`; `cc:real`;
    `KR:real`; `KP:real`; `KM:real`] RFA_NULL_C_LE)) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]);;

let RFA_NULL_EXISTS_CC = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t alpha beta.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     rfa_hpsd_cc G s t alpha beta y /\ ~rfa_hpd_cc G s t alpha beta y
     ==> ?(u:num->num->real) (w:num->real).
           (!i j. u i j = --(u j i)) /\
           &0 < sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) + sum(1..3) (\a. w a pow 2) /\
           rfa_hz 3 (\a b c d. lrm4 G y (rfa_ft S [a; b; d; c]) + alpha * rfa_i4 a b c d)
                    (\a b c. rfa_hP G y (rfa_ft S [a; b; c]))
                    (\a b. rfa_hM s t G y (rfa_ft S [a; b]) + beta * rfa_kd a b) u w = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `alpha:real`; `beta:real`] RFA_HPSD_CC_FT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(ASSUME_TAC o EQ_MP th o check (fun th' ->
    try fst(dest_const(fst(strip_comb(concl th')))) = "rfa_hpsd_cc" with Failure _ -> false))) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `alpha:real`; `beta:real`] RFA_HPD_CC_FT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[th] o check (fun th' -> is_neg(concl th')))) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:num->num->real` (X_CHOOSE_THEN `w:num->real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u:num->num->real`; `w:num->real`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfa_hz" with Failure _ -> false)) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* ========================================================================= *)
(* The first bad time (RFA_FIRST_BAD_TIME), an abstract                      *)
(* topological lemma: if a property holds at small times, fails only inside  *)
(* a compact set, is open in (t, x), and cannot fail first at a point where  *)
(* it holds at all earlier times, then it holds everywhere.                  *)
(* ========================================================================= *)

let RFA_FIRST_BAD_TIME = prove
 (`!(top:A topology) X K (Good:real->A->bool) s Tm tau0.
     X SUBSET topspace top /\ closed_in top X /\ compact_in top K /\ &0 < tau0 /\
     (!t x. s < t /\ t <= Tm /\ t <= s + tau0 /\ x IN X ==> Good t x) /\
     (!t x. s < t /\ t <= Tm /\ x IN X /\ ~Good t x ==> x IN K) /\
     (!t x. s < t /\ t <= Tm /\ x IN X /\ Good t x
            ==> ?N d. open_in top N /\ x IN N /\ &0 < d /\
                      !t' x'. s < t' /\ t' <= Tm /\ abs(t' - t) < d /\ x' IN N /\ x' IN X
                              ==> Good t' x') /\
     (!t x. s < t /\ t <= Tm /\ x IN X /\ ~Good t x /\
            (!t' x'. s < t' /\ t' < t /\ x' IN X ==> Good t' x') ==> F)
     ==> !t x. s < t /\ t <= Tm /\ x IN X ==> Good t x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "small") (CONJUNCTS_THEN2 (LABEL_TAC "cpt")
    (CONJUNCTS_THEN2 (LABEL_TAC "open") (LABEL_TAC "touch")))))))) THEN
  MAP_EVERY X_GEN_TAC [`t1:real`; `x1:A`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `Bs = {t | s < t /\ t <= Tm /\ ?x:A. x IN X /\ ~Good t x}` THEN
  SUBGOAL_THEN `~(Bs:real->bool = {}) /\ (t1:real) IN Bs` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [EXPAND_TAC "Bs" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `x1:A` THEN ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN Bs ==> s + tau0 < t /\ t <= Tm /\ s < t` ASSUME_TAC THENL
   [EXPAND_TAC "Bs" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `t:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(Good:real->A->bool) t x` THEN REWRITE_TAC[] THEN
    USE_THEN "small" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `T1 = inf Bs` THEN
  SUBGOAL_THEN `s + tau0 <= T1 /\ T1 <= Tm` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INF THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_INF_LE THEN MAP_EVERY EXISTS_TAC [`s:real`; `t1:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN Bs ==> T1 <= t` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "T1" THEN MATCH_MP_TAC REAL_INF_LE THEN
    MAP_EVERY EXISTS_TAC [`s:real`; `t:real`] THEN ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. &0 < e ==> ?t. t IN Bs /\ t < T1 + e` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
    MP_TAC(ISPECL [`Bs:real->bool`; `T1 + e:real`] REAL_LE_INF_EQ) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN EXISTS_TAC `s:real` THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
        try is_conj(snd(dest_imp(snd(dest_forall(concl th))))) with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
        try is_disj(snd(dest_forall(concl th))) with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t' x'. s < t' /\ t' < T1 /\ (x':A) IN X ==> Good t' x'` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `t' IN (Bs:real->bool)` MP_TAC THENL
     [EXPAND_TAC "Bs" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC;
                             EXISTS_TAC `x':A` THEN ASM_REWRITE_TAC[]];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t':real` o check (fun th ->
        try fst(dest_binary "real_le" (snd(dest_imp(snd(dest_forall(concl th)))))) = `T1:real`
        with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `?x:A. x IN X /\ ~(Good:real->A->bool) T1 x` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `xs:A` STRIP_ASSUME_TAC) THEN
    USE_THEN "touch" (MP_TAC o SPECL [`T1:real`; `xs:A`]) THEN
    MATCH_MP_TAC(TAUT `p ==> (p ==> F) ==> F`) THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* all points are good at T1: an open cover of K gives a uniform time step *)
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM] o
    check (fun th -> is_neg(concl th) && is_exists(rand(concl th)))) THEN
  SUBGOAL_THEN
   `?N d. !x:A. x IN X
                ==> open_in top (N x) /\ x IN N x /\ &0 < d x /\
                    !t' x'. s < t' /\ t' <= Tm /\ abs(t' - T1) < d x /\ x' IN N x /\
                            x' IN X ==> (Good:real->A->bool) t' x'`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN USE_THEN "open" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_REAL_ARITH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th ->
      try is_disj(snd(dest_forall(concl th))) with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cov = \x:A. if x IN X then (N:A->A->bool) x else topspace top DIFF X` THEN
  ABBREV_TAC `dd = \x:A. if x IN X then (d:A->real) x else &1` THEN
  SUBGOAL_THEN `?Fs. FINITE Fs /\ Fs SUBSET (K:A->bool) /\ K SUBSET UNIONS (IMAGE cov Fs)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `compact_in top (K:A->bool)` THEN REWRITE_TAC[compact_in] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `IMAGE (cov:A->A->bool) K`)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        EXPAND_TAC "cov" THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
         [ASM_MESON_TAC[];
          MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
          FIRST_ASSUM ACCEPT_TAC];
        REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "cov" THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`cov:A->A->bool`; `K:A->bool`; `V:(A->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `del = inf ((&1) INSERT IMAGE (dd:A->real) Fs)` THEN
  SUBGOAL_THEN `&0 < del /\ !x:A. x IN Fs ==> del <= dd x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "del" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(&1) INSERT IMAGE (dd:A->real) Fs`; `&0`] REAL_LT_INF_FINITE) THEN
      ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      EXPAND_TAC "dd" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
      ASM_MESON_TAC[REAL_LT_01];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`(&1) INSERT IMAGE (dd:A->real) Fs`; `(dd:A->real) x`] REAL_INF_LE_FINITE) THEN
      ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY] THEN
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `(dd:A->real) x` THEN
      REWRITE_TAC[REAL_LE_REFL; IN_INSERT; IN_IMAGE] THEN DISJ2_TAC THEN
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `del:real` o check (fun th ->
    try is_exists(snd(dest_imp(snd(dest_forall(concl th))))) with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `tb:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s < tb /\ tb <= Tm /\ T1 <= tb /\ ?xb:A. xb IN X /\ ~Good tb xb`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(tb:real) IN Bs` THEN EXPAND_TAC "Bs" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xb:A) IN K` ASSUME_TAC THENL
   [USE_THEN "cpt" MATCH_MP_TAC THEN EXISTS_TAC `tb:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?xc:A. xc IN Fs /\ (xb:A) IN (cov:A->A->bool) xc` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:A->bool) SUBSET UNIONS (IMAGE (cov:A->A->bool) Fs)` THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(xc:A) IN X` THENL
   [UNDISCH_TAC `~(Good:real->A->bool) tb xb` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `xc:A` o check (fun th ->
      try is_imp(snd(dest_forall(concl th))) &&
          can (find_term ((=) `N:A->A->bool`)) (concl th) with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    UNDISCH_TAC `(xb:A) IN (cov:A->A->bool) xc` THEN EXPAND_TAC "cov" THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `xc:A` o check (fun th ->
      try fst(dest_binary "real_le" (snd(dest_imp(snd(dest_forall(concl th)))))) = `del:real`
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "dd" THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `(xb:A) IN (cov:A->A->bool) xc` THEN EXPAND_TAC "cov" THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Glue between the manifold and the charts.  Continuity of the              *)
(* barrier in a chart (RFA_PSI_CHART_CONT), restriction of a chart Ricci     *)
(* flow (RFA_LRICCI_FLOW_RESTRICT), and positive definite implies positive   *)
(* semidefinite (RFA_HPD_IMP_HPSD).                                          *)
(* ========================================================================= *)

let RFA_PSI_CHART_CONT = prove
 (`!top atlas (psi:real->A->real) (X:A->bool) (c:(A->bool)#(A->real^3)) t1 t2 a1 b1.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     continuous_map (prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                                   (subtopology top X), euclideanreal)
                    (\z. psi (FST z) (SND z)) /\
     t1 <= a1 /\ b1 <= t2
     ==> (\z. lift(psi (drop(fstcart z)) (chart_inv c (sndcart z)))) continuous_on
         (interval(lift a1,lift b1) PCROSS IMAGE (SND c) (FST c INTER X))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
  SUBGOAL_THEN
   `(\z. lift((psi:real->A->real) (drop(fstcart z)) (chart_inv (c:(A->bool)#(A->real^3)) (sndcart z)))) =
    lift o (\z. psi (FST z) (SND z)) o
    (\z:real^(1,3)finite_sum. (drop(fstcart z), chart_inv c (sndcart z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONTINUOUS_MAP_EQ_LIFT] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                            (subtopology top (X:A->bool))` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; o_DEF; LIFT_DROP; CONTINUOUS_MAP_EUCLIDEAN] THEN
    REWRITE_TAC[ETA_AX] THEN SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN
     `(\z:real^(1,3)finite_sum. chart_inv (c:(A->bool)#(A->real^3)) (sndcart z)) =
      chart_inv c o sndcart` SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
      SET_TAC[];
      MATCH_MP_TAC MFDD_CHART_INV_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]]);;

let RFA_LRICCI_FLOW_RESTRICT = prove
 (`!U V a b a1 b1 (G:real->real^N->real^N^N).
     lricci_flow U a b G /\ open V /\ V SUBSET U /\ a <= a1 /\ a1 < b1 /\ b1 <= b
     ==> lricci_flow V a1 b1 G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]]);;

let RFA_HPD_IMP_HPSD = prove
 (`!U (G:real^3->real^3^3) s t alpha beta y.
     metric_field U G /\ y IN U /\ rfa_hpd_cc G s t alpha beta y
     ==> rfa_hpsd_cc G s t alpha beta y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `alpha:real`; `beta:real`] RFA_HPSD_CC_FT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `s:real`;
                 `t:real`; `alpha:real`; `beta:real`] RFA_HPD_CC_FT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(ASSUME_TAC o EQ_MP th o check (fun th' ->
    try fst(dest_const(fst(strip_comb(concl th')))) = "rfa_hpd_cc" with Failure _ -> false))) THEN
  MAP_EVERY X_GEN_TAC [`u:num->num->real`; `w:num->real`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 < sum(1..3) (\a. sum(1..3) (\b. (u:num->num->real) a b pow 2)) +
                      sum(1..3) (\a. (w:num->real) a pow 2)` THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `!i j. (u:num->num->real) i j = --(u j i)`)) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM RFA_NZ_SUMSQ] o check (fun th -> is_neg(concl th))) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[rfa_hz] THEN
  MATCH_MP_TAC(REAL_ARITH `a = &0 /\ b = &0 /\ c = &0 ==> a + &2 * b + c = &0`) THEN
  REPEAT CONJ_TAC THEN
  REPEAT(MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]);;

(* ========================================================================= *)
(* The manifold setting.  rfa_hframe (frame bounds and                       *)
(* nonnegativity at a point), rfa_hset (the flow and the frame bounds on     *)
(* (s, T2]) and rfa_hgood (positive definiteness in all charts at (t, x)).   *)
(* Positivity at small times (RFA_HGOOD_SMALL) and for a large barrier term  *)
(* (RFA_HGOOD_LARGE), continuity of the coefficients in charts               *)
(* (RFA_AL_CHART_CONT, RFA_BE_CHART_CONT), and openness of the good set      *)
(* (RFA_HGOOD_OPEN).                                                         *)
(* ========================================================================= *)

let rfa_hframe = new_definition
 `rfa_hframe (G:real^3->real^3^3) s t (y:real^3) (S:real^3^3) KR KP KM0 K <=>
    (!a b c d. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
               1 <= d /\ d <= 3 ==> abs(lrm4 G y (rfa_ft S [a; b; d; c])) <= KR) /\
    (!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
             ==> abs(rfa_hP G y (rfa_ft S [a; b; c])) <= KP) /\
    (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
           ==> abs(rfa_hM s t G y (rfa_ft S [a; b]) -
                   inv(&2 * (t - s)) * lric2 G y (rfa_ft S [a; b])) <= KM0) /\
    (!a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
           ==> abs(lric2 G y (rfa_ft S [a; b])) <= K) /\
    (!u. (!i j. u i j = --(u j i))
         ==> &0 <= sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
                      lrm4 G y (rfa_ft S [a; b; d; c]) * u a b * u d c))))) /\
    (!w. &0 <= sum(1..3) (\a. sum(1..3) (\b. lric2 G y (rfa_ft S [a; b]) * w a * w b)))`;;

let rfa_hset = new_definition
 `rfa_hset (top:A topology,atlas) (g:real->A->real^3^3) a b s T2 KR KP KM0 K <=>
    ricci_flow_on (top,atlas) a b g /\ a < s /\ s < T2 /\ T2 < b /\
    &0 <= KR /\ &0 <= KP /\ &0 <= KM0 /\ &0 <= K /\
    !t x c (S:real^3^3).
       s < t /\ t <= T2 /\ x IN topspace top /\ c IN atlas /\ x IN FST c /\
       invertible S /\ matrix_inv(metric_local atlas c (g t) (SND c x)) = transp S ** S
       ==> rfa_hframe (metric_local atlas c (g t)) s t (SND c x) S KR KP KM0 K`;;

let rfa_hgood = new_definition
 `rfa_hgood (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) s
            (al:real->A->real) (be:real->A->real) t x <=>
    !c. c IN atlas /\ x IN FST c
        ==> rfa_hpd_cc (metric_local atlas c (g t)) s t (al t x) (be t x) (SND c x)`;;

(* Chart facts of the setting: the chart flow, the metric fields, frames.     *)

let RFA_HSET_CHART = prove
 (`!top atlas (g:real->A->real^3^3) a b s T2 KR KP KM0 K c.
     rfa_hset (top,atlas) g a b s T2 KR KP KM0 K /\ c IN atlas
     ==> smooth_manifold_atlas top atlas /\
         lricci_flow (IMAGE (SND c) (FST c)) a b (\t. metric_local atlas c (g t)) /\
         (!t. a < t /\ t < b ==> riemannian_metric atlas (g t)) /\
         (!t. a < t /\ t < b
              ==> metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c (g t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_hset] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`] LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[]);;

let RFA_HGOOD_SMALL = prove
 (`!top atlas (g:real->A->real^3^3) a b s T2 KR KP KM0 K (psi:real->A->real)
    dd e eta L B A t x.
     rfa_hset (top,atlas) g a b s T2 KR KP KM0 K /\
     &0 < dd /\ &0 < e /\ &0 <= eta /\ &0 <= B /\ &0 <= A /\
     s < t /\ t <= T2 /\ t - s <= e / (&3 * KM0 + &9 * KP * (&6 * KP + &1) / dd + &1) /\
     x IN topspace top /\ &0 <= psi t x
     ==> rfa_hgood atlas g s
           (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * psi t x)
           (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x) t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rfa_hgood] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `a:real`; `b:real`; `s:real`; `T2:real`; `KR:real`; `KP:real`; `KM0:real`;
                 `K:real`; `c:(A->bool)#(A->real^3)`] RFA_HSET_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfa_hset (top,atlas) (g:real->A->real^3^3) a b s T2 KR KP KM0 K` THEN
  REWRITE_TAC[rfa_hset] THEN STRIP_TAC THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND c) (FST c)) (G:real^3->real^3^3) /\
                SND (c:(A->bool)#(A->real^3)) x IN IMAGE (SND c) (FST c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "G" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
                    ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `G:real^3->real^3^3`;
                 `SND (c:(A->bool)#(A->real^3)) x`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`; `c:(A->bool)#(A->real^3)`; `S:real^3^3`]) THEN
  ASM_REWRITE_TAC[rfa_hframe] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_HPD_SMALL_CC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `S:real^3^3`;
                        `KM0:real`; `KP:real`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the scalar conditions *)
  ABBREV_TAC `D = &3 * KM0 + &9 * KP * (&6 * KP + &1) / dd + &1` THEN
  SUBGOAL_THEN `&0 <= &9 * KP * (&6 * KP + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 < x + y + &1`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= exp(B * (t - s)) /\ &1 <= exp(A * (t - s)) /\ &0 <= exp(L * (t - s))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LE] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `&1 + B * (t - s)`; EXISTS_TAC `&1 + A * (t - s)`] THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eta * exp(L * (t - s)) * (psi:real->A->real) t x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dd <= dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * (psi:real->A->real) t x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `dd <= p /\ &0 <= q ==> dd <= p + q`) THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e / (t - s)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `D:real` THEN CONJ_TAC THENL
     [EXPAND_TAC "D" THEN
      MATCH_MP_TAC(REAL_ARITH `y <= z ==> x + y < x + z + &1`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]];
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= z ==> x <= y + z`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `e * i = (e * &1) * i`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]);;

let RFA_HM_BOUND_FRAME = prove
 (`!(G:real^3->real^3^3) s t y (S:real^3^3) KR KP KM0 K.
     rfa_hframe G s t y S KR KP KM0 K /\ s < t
     ==> !a b. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
               ==> abs(rfa_hM s t G y (rfa_ft S [a; b])) <= KM0 + K / (&2 * (t - s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_hframe] THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `b:num`] o check (fun th ->
    can (find_term ((=) `KM0:real`)) (concl th) && is_forall (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `b:num`] o check (fun th ->
    can (find_term ((=) `K:real`)) (concl th) && is_forall (concl th) &&
    not (can (find_term ((=) `KM0:real`)) (concl th)) &&
    can (find_term ((=) `lric2:(real^3->real^3^3)->real^3->(num->real^3)->real`)) (concl th) &&
    not (can (find_term ((=) `w:num->real`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < inv(&2 * (t - s))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  ABBREV_TAC `iv = inv(&2 * (t - s))` THEN
  ABBREV_TAC `r = lric2 (G:real^3->real^3^3) y (rfa_ft S [a; b])` THEN
  ABBREV_TAC `m = rfa_hM s t (G:real^3->real^3^3) y (rfa_ft S [a; b])` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs(iv * r) <= K * iv` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs iv = iv` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RFA_HGOOD_LARGE = prove
 (`!top atlas (g:real->A->real^3^3) a b s T2 KR KP KM0 K (psi:real->A->real)
    dd e eta L B A tau0 t x.
     rfa_hset (top,atlas) g a b s T2 KR KP KM0 K /\
     &0 <= dd /\ &0 <= e /\ &0 < tau0 /\ s + tau0 <= t /\ t <= T2 /\ x IN topspace top /\
     &3 * (KM0 + K / (&2 * tau0)) + &9 * KP + &9 * KR < eta * exp(L * (t - s)) * psi t x
     ==> rfa_hgood atlas g s
           (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * psi t x)
           (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x) t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rfa_hgood] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `a:real`; `b:real`; `s:real`; `T2:real`; `KR:real`; `KP:real`; `KM0:real`;
                 `K:real`; `c:(A->bool)#(A->real^3)`] RFA_HSET_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfa_hset (top,atlas) (g:real->A->real^3^3) a b s T2 KR KP KM0 K` THEN
  REWRITE_TAC[rfa_hset] THEN STRIP_TAC THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND c) (FST c)) (G:real^3->real^3^3) /\
                SND (c:(A->bool)#(A->real^3)) x IN IMAGE (SND c) (FST c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "G" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
                    ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `G:real^3->real^3^3`;
                 `SND (c:(A->bool)#(A->real^3)) x`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`; `c:(A->bool)#(A->real^3)`; `S:real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real^3->real^3^3`; `s:real`; `t:real`; `SND (c:(A->bool)#(A->real^3)) x`;
                 `S:real^3^3`; `KR:real`; `KP:real`; `KM0:real`; `K:real`] RFA_HM_BOUND_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  UNDISCH_TAC `rfa_hframe (G:real^3->real^3^3) s t (SND (c:(A->bool)#(A->real^3)) x) S KR KP KM0 K` THEN
  REWRITE_TAC[rfa_hframe] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_HPD_LARGE_CC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `S:real^3^3`;
                        `KR:real`; `KP:real`; `KM0 + K / (&2 * (t - s))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_div] THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_INV) THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&3 * (KM0 + K / (&2 * tau0)) + &9 * KP + &9 * KR` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> &3 * (m + x) + p <= &3 * (m + y) + p`) THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]);;

let RFA_TIME_EXP_CONT = prove
 (`!(S:real^(1,3)finite_sum->bool) a1 b1 c B s0.
     S SUBSET interval(lift a1,lift b1) PCROSS (:real^3)
     ==> (\z. lift(c * exp(B * (drop(fstcart z) - s0)))) continuous_on S`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(1,3)finite_sum. lift(c * exp(B * (drop(fstcart z) - s0)))) =
                (\x. lift(c * exp(B * (drop x - s0)))) o fstcart` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
  REWRITE_TAC[SUBSET_UNIV; OPEN_UNIV] THEN
  MATCH_MP_TAC RFA_EXP_TIME_SMOOTH THEN REWRITE_TAC[OPEN_UNIV]);;

let RFA_TIME_EXPDIV_CONT = prove
 (`!(S:real^(1,3)finite_sum->bool) a1 b1 c A s0.
     s0 <= a1 /\ S SUBSET interval(lift a1,lift b1) PCROSS (:real^3)
     ==> (\z. lift(c * exp(A * (drop(fstcart z) - s0)) / (drop(fstcart z) - s0)))
         continuous_on S`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(1,3)finite_sum.
                   lift(c * exp(A * (drop(fstcart z) - s0)) / (drop(fstcart z) - s0))) =
                (\x. lift(c * exp(A * (drop x - s0)) / (drop x - s0))) o fstcart` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval(lift a1,lift b1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC RFA_EXPDIV_TIME_SMOOTH THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^(1,3)finite_sum` THEN
    DISCH_TAC THEN
    UNDISCH_TAC `(S:real^(1,3)finite_sum->bool) SUBSET interval(lift a1,lift b1) PCROSS (:real^3)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:real^(1,3)finite_sum`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ISPEC `z:real^(1,3)finite_sum` PASTECART_FST_SND)) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART] THEN MESON_TAC[]]);;

let RFA_AL_CHART_CONT = prove
 (`!top atlas (psi:real->A->real) (X:A->bool) (c:(A->bool)#(A->real^3)) t1 t2 dd B eta L s0.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     continuous_map (prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                                   (subtopology top X), euclideanreal)
                    (\z. psi (FST z) (SND z))
     ==> (\z. lift(dd * exp(B * (drop(fstcart z) - s0)) +
                   eta * exp(L * (drop(fstcart z) - s0)) *
                   psi (drop(fstcart z)) (chart_inv c (sndcart z))))
         continuous_on (interval(lift t1,lift t2) PCROSS IMAGE (SND c) (FST c INTER X))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. lift(dd * exp(B * (drop(fstcart z) - s0)) +
              eta * exp(L * (drop(fstcart z) - s0)) *
              (psi:real->A->real) (drop(fstcart z)) (chart_inv (c:(A->bool)#(A->real^3)) (sndcart z)))) =
    (\z. lift(dd * exp(B * (drop(fstcart z) - s0))) +
         (eta * exp(L * (drop(fstcart z) - s0))) % lift(psi (drop(fstcart z)) (chart_inv c (sndcart z))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_ADD; LIFT_CMUL; VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_TIME_EXP_CONT THEN MAP_EVERY EXISTS_TAC [`t1:real`; `t2:real`] THEN
    MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET_UNIV];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC RFA_TIME_EXP_CONT THEN
      MAP_EVERY EXISTS_TAC [`t1:real`; `t2:real`] THEN
      MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET_UNIV];
      MATCH_MP_TAC RFA_PSI_CHART_CONT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `t1:real`; `t2:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL]]]);;

let RFA_BE_CHART_CONT = prove
 (`!top atlas (psi:real->A->real) (X:A->bool) (c:(A->bool)#(A->real^3)) t1 t2 e A eta L s0.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ s0 <= t1 /\
     continuous_map (prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                                   (subtopology top X), euclideanreal)
                    (\z. psi (FST z) (SND z))
     ==> (\z. lift(e * exp(A * (drop(fstcart z) - s0)) / (drop(fstcart z) - s0) +
                   eta * exp(L * (drop(fstcart z) - s0)) *
                   psi (drop(fstcart z)) (chart_inv c (sndcart z))))
         continuous_on (interval(lift t1,lift t2) PCROSS IMAGE (SND c) (FST c INTER X))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. lift(e * exp(A * (drop(fstcart z) - s0)) / (drop(fstcart z) - s0) +
              eta * exp(L * (drop(fstcart z) - s0)) *
              (psi:real->A->real) (drop(fstcart z)) (chart_inv (c:(A->bool)#(A->real^3)) (sndcart z)))) =
    (\z. lift(e * exp(A * (drop(fstcart z) - s0)) / (drop(fstcart z) - s0)) +
         (eta * exp(L * (drop(fstcart z) - s0))) % lift(psi (drop(fstcart z)) (chart_inv c (sndcart z))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_ADD; LIFT_CMUL; VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_TIME_EXPDIV_CONT THEN MAP_EVERY EXISTS_TAC [`t1:real`; `t2:real`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET_UNIV];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC RFA_TIME_EXP_CONT THEN
      MAP_EVERY EXISTS_TAC [`t1:real`; `t2:real`] THEN
      MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET_UNIV];
      MATCH_MP_TAC RFA_PSI_CHART_CONT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `t1:real`; `t2:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL]]]);;

let RFA_CHART_NBHD = prove
 (`!top atlas (c:(A->bool)#(A->real^3)) (X:A->bool) x r.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ open_in top X
     ==> open_in top {x' | x' IN FST c /\ x' IN X /\ SND c x' IN ball(SND c x,r)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{x' | x' IN FST c /\ x' IN X /\ SND (c:(A->bool)#(A->real^3)) x' IN ball(SND c x,r)} =
                {x' | x' IN topspace(subtopology top (FST c)) /\ SND c x' IN ball(SND c x,r)} INTER X`
  SUBST1_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `FST(c:(A->bool)#(A->real^3))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
  EXISTS_TAC `euclidean:(real^3)topology` THEN REWRITE_TAC[GSYM OPEN_IN; OPEN_BALL; ETA_AX] THEN
  MATCH_MP_TAC MFDD_CHART_CONTINUOUS THEN EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFA_HGOOD_OPEN = prove
 (`!top atlas (g:real->A->real^3^3) a b s T2 KR KP KM0 K (psi:real->A->real) x0
    dd e eta L B A t x.
     rfa_hset (top,atlas) g a b s T2 KR KP KM0 K /\
     continuous_map (prod_topology (subtopology euclideanreal (real_interval[s,T2]))
                      (subtopology top {x | mfd_joinable (top,atlas) x0 x}), euclideanreal)
                    (\z. psi (FST z) (SND z)) /\
     s < t /\ t < T2 /\ mfd_joinable (top,atlas) x0 x /\
     rfa_hgood atlas g s
       (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * psi t x)
       (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x) t x
     ==> ?N d. open_in top N /\ x IN N /\ &0 < d /\
               !t' x'. s < t' /\ t' < T2 /\ abs(t' - t) < d /\ x' IN N /\
                       mfd_joinable (top,atlas) x0 x'
                       ==> rfa_hgood atlas g s
                             (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * psi t x)
                             (\t x. e * exp(A * (t - s)) / (t - s) +
                                    eta * exp(L * (t - s)) * psi t x) t' x'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                ricci_flow_on (top,atlas) a b (g:real->A->real^3^3) /\ a < s /\ T2 < b`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_hset (top,atlas) (g:real->A->real^3^3) a b s T2 KR KP KM0 K` THEN
    REWRITE_TAC[rfa_hset; ricci_flow_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = {x:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x0 x}` THEN
  SUBGOAL_THEN `open_in top (X:A->bool) /\ (x:A) IN X /\ x IN topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN ASM_SIMP_TAC[MFD_JOINABLE_OPEN; IN_ELIM_THM] THEN
    ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) x` THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^3)) IN atlas /\ (x:A) IN FST c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Uc = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER X)` THEN
  SUBGOAL_THEN `open (Uc:real^3->bool) /\ Uc SUBSET IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c) /\
                SND c (x:A) IN Uc` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Uc" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `a:real`; `b:real`; `s:real`; `T2:real`; `KR:real`; `KP:real`; `KM0:real`;
                 `K:real`; `c:(A->bool)#(A->real^3)`] RFA_HSET_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lricci_flow Uc s T2 (\t. metric_local atlas (c:(A->bool)#(A->real^3))
                                        ((g:real->A->real^3^3) t))` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LRICCI_FLOW_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `alz = \z:real^(1,3)finite_sum.
                 dd * exp(B * (drop(fstcart z) - s)) +
                 eta * exp(L * (drop(fstcart z) - s)) *
                 (psi:real->A->real) (drop(fstcart z)) (chart_inv (c:(A->bool)#(A->real^3)) (sndcart z))` THEN
  ABBREV_TAC `bez = \z:real^(1,3)finite_sum.
                 e * exp(A * (drop(fstcart z) - s)) / (drop(fstcart z) - s) +
                 eta * exp(L * (drop(fstcart z) - s)) *
                 (psi:real->A->real) (drop(fstcart z)) (chart_inv (c:(A->bool)#(A->real^3)) (sndcart z))` THEN
  SUBGOAL_THEN `(\z. lift((alz:real^(1,3)finite_sum->real) z)) continuous_on
                  (interval(lift s,lift T2) PCROSS (Uc:real^3->bool)) /\
                (\z. lift((bez:real^(1,3)finite_sum->real) z)) continuous_on
                  (interval(lift s,lift T2) PCROSS Uc)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["alz"; "bez"; "Uc"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_AL_CHART_CONT; MATCH_MP_TAC RFA_BE_CHART_CONT] THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `z1 = pastecart (lift t) (SND (c:(A->bool)#(A->real^3)) (x:A))` THEN
  SUBGOAL_THEN `(z1:real^(1,3)finite_sum) IN interval(lift s,lift T2) PCROSS (Uc:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "z1" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Uc:real^3->bool`; `s:real`; `T2:real`;
                 `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
                 `s:real`; `alz:real^(1,3)finite_sum->real`; `bez:real^(1,3)finite_sum->real`;
                 `z1:real^(1,3)finite_sum`] RFA_HPD_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]; ALL_TAC] THEN
    EXPAND_TAC "z1" THEN MAP_EVERY EXPAND_TAC ["alz"; "bez"] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> try fst(dest_imp(snd(dest_forall(concl th)))) = `(x:A) IN FST (c:(A->bool)#(A->real^3))` with Failure _ -> false)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `rfa_hgood atlas (g:real->A->real^3^3) s
      (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * (psi:real->A->real) t x)
      (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x) t x` THEN
    REWRITE_TAC[rfa_hgood] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x':A | x' IN FST (c:(A->bool)#(A->real^3)) /\ x' IN X /\
                      SND c x' IN ball(SND c x,d / &2)}` THEN
  EXISTS_TAC `d / &2` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFA_CHART_NBHD THEN EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t':real`; `x':A`] THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL] THEN
  STRIP_TAC THEN REWRITE_TAC[rfa_hgood] THEN
  X_GEN_TAC `c':(A->bool)#(A->real^3)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t'`; `c:(A->bool)#(A->real^3)`;
                 `c':(A->bool)#(A->real^3)`; `x':A`; `s:real`; `t':real`;
                 `dd * exp(B * (t' - s)) + eta * exp(L * (t' - s)) * (psi:real->A->real) t' x'`;
                 `e * exp(A * (t' - s)) / (t' - s) + eta * exp(L * (t' - s)) * (psi:real->A->real) t' x'`]
         RFA_HPSD_CC_CHARTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT2 th)])] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift t') (SND (c:(A->bool)#(A->real^3)) (x':A))` o
    check (fun th -> try is_forall(concl th) &&
                         can (find_term ((=) `z1:real^(1,3)finite_sum`)) (concl th)
                     with Failure _ -> false)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      EXPAND_TAC "z1" THEN REWRITE_TAC[PASTECART_SUB] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(lift t' - lift t) + norm(SND (c:(A->bool)#(A->real^3)) (x':A) - SND c x)` THEN
      REWRITE_TAC[NORM_PASTECART_LE] THEN
      REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
      UNDISCH_TAC `dist(SND (c:(A->bool)#(A->real^3)) (x:A),SND c x') < d / &2` THEN
      REWRITE_TAC[dist] THEN
      SUBGOAL_THEN `norm(SND (c:(A->bool)#(A->real^3)) (x':A) - SND c x) =
                    norm(SND c x - SND c x')` SUBST1_TAC THENL
       [MATCH_ACCEPT_TAC NORM_SUB; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["alz"; "bez"] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x':A` o check (fun th -> try fst(dest_imp(snd(dest_forall(concl th)))) = `(x:A) IN FST (c:(A->bool)#(A->real^3))` with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* The barrier package rfa_hbar (the conclusion of                           *)
(* RFA_HARNACK_BARRIER_STATEMENT on [t1, t2]) and its existence from         *)
(* pc_rfa_hbar (RFA_HBAR_EXISTS); positive semidefiniteness at a time Ts in  *)
(* a chart when the good set contains all earlier times                      *)
(* (RFA_HPSD_LIMIT_CHART).                                                   *)
(* ========================================================================= *)

let rfa_hbar = new_definition
 `rfa_hbar (top:A topology,atlas) (g:real->A->real^3^3) t1 t2 x0 C (psi:real->A->real) <=>
    (!t x. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x ==> &1 <= psi t x) /\
    continuous_map
      (prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                     (subtopology top {x | mfd_joinable (top,atlas) x0 x}),
       euclideanreal)
      (\z. psi (FST z) (SND z)) /\
    (!B. ?S. compact_in top S /\
             !t x. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x /\ psi t x <= B
                   ==> x IN S) /\
    (!t x. t1 < t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x
           ==> ?d. &0 < d /\
                   !s'. t1 <= s' /\ t - d < s' /\ s' <= t
                        ==> psi s' x <= psi t x + C * (t - s') * psi t x) /\
    (!t x c. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x /\
             c IN atlas /\ x IN FST c
             ==> ?W (q:real^3->real).
                   open W /\ SND c x IN W /\ W SUBSET IMAGE (SND c) (FST c) /\
                   smooth_map_on W (\y. lift(q y)) /\
                   (!y. y IN W ==> psi t (chart_inv c y) <= q y) /\
                   q (SND c x) = psi t x /\
                   llap (metric_local atlas c (g t)) q (SND c x) <= C * psi t x /\
                   lgrad2 (metric_local atlas c (g t)) q (SND c x) <= C * psi t x pow 2)`;;

let RFA_HBAR_EXISTS = prove
 (`!top atlas (g:real->A->real^3^3) a b t1 t2 Kric x0.
     hausdorff_space top /\ ricci_flow_on (top,atlas) a b g /\
     a < t1 /\ t1 < t2 /\ t2 < b /\
     (!t. t1 <= t /\ t <= t2 ==> mfd_complete (top,atlas) (g t)) /\
     (!t x v. t1 <= t /\ t <= t2 /\ x IN topspace top
              ==> abs(mfd_ricci atlas (g t) x v v) <= Kric * (v dot (g t x ** v))) /\
     x0 IN topspace top
     ==> ?C psi. rfa_hbar (top,atlas) g t1 t2 x0 C psi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[RFA_HARNACK_BARRIER_STATEMENT] (ISPEC `(:A)` RFA_HARNACK_BARRIER)) THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:real->A->real^3^3`; `a:real`; `b:real`; `t1:real`; `t2:real`;
                            `Kric:real`; `x0:A`]) THEN
  ASM_REWRITE_TAC[rfa_hbar]);;

let RFA_HPSD_LIMIT_CHART = prove
 (`!top atlas (g:real->A->real^3^3) a b s T2 KR KP KM0 K (psi:real->A->real) x0 C
    dd e eta B A L Ts c y.
     rfa_hset (top,atlas) g a b s T2 KR KP KM0 K /\ rfa_hbar (top,atlas) g s T2 x0 C psi /\
     s < Ts /\ Ts < T2 /\ c IN atlas /\
     y IN IMAGE (SND c) (FST c INTER {x | mfd_joinable (top,atlas) x0 x}) /\
     (!t' x'. s < t' /\ t' < Ts /\ mfd_joinable (top,atlas) x0 x'
              ==> rfa_hgood atlas g s
                    (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * psi t x)
                    (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x)
                    t' x')
     ==> rfa_hpsd_cc (metric_local atlas c (g Ts)) s Ts
           (dd * exp(B * (Ts - s)) + eta * exp(L * (Ts - s)) * psi Ts (chart_inv c y))
           (e * exp(A * (Ts - s)) / (Ts - s) + eta * exp(L * (Ts - s)) * psi Ts (chart_inv c y))
           y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                ricci_flow_on (top,atlas) a b (g:real->A->real^3^3) /\ a < s /\ T2 < b`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_hset (top,atlas) (g:real->A->real^3^3) a b s T2 KR KP KM0 K` THEN
    REWRITE_TAC[rfa_hset; ricci_flow_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = {x:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x0 x}` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (X:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN ASM_SIMP_TAC[MFD_JOINABLE_OPEN]; ALL_TAC] THEN
  ABBREV_TAC `Uc = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER X)` THEN
  SUBGOAL_THEN `open (Uc:real^3->bool) /\ Uc SUBSET IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c) /\
                (!y. y IN Uc ==> chart_inv c y IN FST c /\ chart_inv c y IN X /\
                                 SND c (chart_inv c y) = y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Uc" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      SET_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `a:real`; `b:real`; `s:real`; `T2:real`; `KR:real`; `KP:real`; `KM0:real`;
                 `K:real`; `c:(A->bool)#(A->real^3)`] RFA_HSET_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lricci_flow Uc s T2 (\t. metric_local atlas (c:(A->bool)#(A->real^3))
                                        ((g:real->A->real^3^3) t))` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LRICCI_FLOW_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `alz = \z:real^(1,3)finite_sum.
                 dd * exp(B * (drop(fstcart z) - s)) +
                 eta * exp(L * (drop(fstcart z) - s)) *
                 (psi:real->A->real) (drop(fstcart z)) (chart_inv (c:(A->bool)#(A->real^3)) (sndcart z))` THEN
  ABBREV_TAC `bez = \z:real^(1,3)finite_sum.
                 e * exp(A * (drop(fstcart z) - s)) / (drop(fstcart z) - s) +
                 eta * exp(L * (drop(fstcart z) - s)) *
                 (psi:real->A->real) (drop(fstcart z)) (chart_inv (c:(A->bool)#(A->real^3)) (sndcart z))` THEN
  SUBGOAL_THEN `(\z. lift((alz:real^(1,3)finite_sum->real) z)) continuous_on
                  (interval(lift s,lift T2) PCROSS (Uc:real^3->bool)) /\
                (\z. lift((bez:real^(1,3)finite_sum->real) z)) continuous_on
                  (interval(lift s,lift T2) PCROSS Uc)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_hbar (top,atlas) (g:real->A->real^3^3) s T2 x0 C psi` THEN
    REWRITE_TAC[rfa_hbar] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["alz"; "bez"; "Uc"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_AL_CHART_CONT; MATCH_MP_TAC RFA_BE_CHART_CONT] THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    EXPAND_TAC "X" THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN Uc` ASSUME_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`Uc:real^3->bool`; `s:real`; `T2:real`;
                 `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
                 `s:real`; `alz:real^(1,3)finite_sum->real`; `bez:real^(1,3)finite_sum->real`;
                 `pastecart (lift Ts) (y:real^3)`] RFA_HPSD_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN `pastecart (lift Ts) (y:real^3) IN interval(lift s,lift T2) PCROSS Uc`
    ASSUME_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]; ALL_TAC] THEN
    X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
    ABBREV_TAC `h = min (ep / &2) ((Ts - s) / &2)` THEN
    SUBGOAL_THEN `&0 < h /\ h < ep /\ s < Ts - h /\ Ts - h < Ts` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `pastecart (lift(Ts - h)) (y:real^3)` THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART; NORM_0] THEN
      REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_POLY_CONV) THEN
      REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_ADD_RID] THEN
      SUBGOAL_THEN `abs(Ts - h - Ts) = h` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; GSYM REAL_POW_2] THEN
      MP_TAC(SPEC `h:real` POW_2_SQRT) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["alz"; "bez"] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MATCH_MP_TAC RFA_HPD_IMP_HPSD THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      try is_imp(snd(dest_forall(concl th))) &&
          can (find_term ((=) `X:A->bool`)) (concl th) with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`Ts - h:real`; `chart_inv (c:(A->bool)#(A->real^3)) (y:real^3)`] o
      check (fun th -> try can (find_term ((=) `rfa_hgood:((A->bool)#(A->real^3)->bool)->(real->A->real^3^3)->real->(real->A->real)->(real->A->real)->real->A->bool`)) (concl th) && is_forall (concl th) with Failure _ -> false)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `chart_inv (c:(A->bool)#(A->real^3)) (y:real^3) IN X` THEN EXPAND_TAC "X" THEN
      REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    REWRITE_TAC[rfa_hgood] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["alz"; "bez"] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]);;

(* ========================================================================= *)
(* No first touching point on the manifold.  At a first time Ts              *)
(* after s + tau0 where the perturbed form fails to be positive definite at  *)
(* a joinable point xs, the chart-level contradiction RFA_TOUCH_CONTRA       *)
(* applies in the chart at xs (RFA_HGOOD_TOUCH).                             *)
(* ========================================================================= *)

let RFA_HGOOD_TOUCH = prove
 (`!top atlas (g:real->A->real^3^3) a b s T2 KR KP KM0 K (psi:real->A->real) x0 C
    dd e eta tau0 CZ B A L Ts xs.
     rfa_hset (top,atlas) g a b s T2 KR KP KM0 K /\ rfa_hbar (top,atlas) g s T2 x0 C psi /\
     &0 <= C /\ &0 < e /\ &0 < dd /\ &0 < eta /\ &0 < tau0 /\
     B = &12 * KP + &324 * KR + &2 /\ A = &18 * KR + &2 /\
     CZ = &3 * (KM0 + K / (&2 * tau0)) + &9 * KP + &9 * KR /\
     L = &2 * C + &2 * ((C + &1) * (&5 * K + inv tau0)) +
         (&6 * (KM0 + K / (&2 * tau0)) + &36 * KP) + (&12 * KP + &324 * KR) + &2 +
         &2 * (e * exp(A * (T2 - s)) / tau0) + &2 * CZ + &18 * KR +
         &2 * (&18 * K pow 2 + inv(&2 * tau0 pow 2)) + &1 /\
     dd * exp(B * (T2 - s)) <= &1 /\
     dd * exp(B * (T2 - s)) *
       ((T2 - s) pow 2 * (&6 * KM0 + &36 * KP + &36 * K pow 2) + &3 * K * (T2 - s) + &1) < e /\
     s + tau0 <= Ts /\ Ts < T2 /\ mfd_joinable (top,atlas) x0 xs /\
     ~rfa_hgood atlas g s
        (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * psi t x)
        (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x) Ts xs /\
     (!t' x'. s < t' /\ t' < Ts /\ mfd_joinable (top,atlas) x0 x'
              ==> rfa_hgood atlas g s
                    (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * psi t x)
                    (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x)
                    t' x')
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                ricci_flow_on (top,atlas) a b (g:real->A->real^3^3) /\ a < s /\ T2 < b /\ s < T2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_hset (top,atlas) (g:real->A->real^3^3) a b s T2 KR KP KM0 K` THEN
    REWRITE_TAC[rfa_hset; ricci_flow_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = {x:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x0 x}` THEN
  SUBGOAL_THEN `open_in top (X:A->bool) /\ (xs:A) IN X /\ xs IN topspace top`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN ASM_SIMP_TAC[MFD_JOINABLE_OPEN; IN_ELIM_THM] THEN
    ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) xs` THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^3)) IN atlas /\ (xs:A) IN FST c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Uc = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER X)` THEN
  SUBGOAL_THEN `open (Uc:real^3->bool) /\ Uc SUBSET IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c) /\
                SND c (xs:A) IN Uc /\
                (!y. y IN Uc ==> chart_inv c y IN FST c /\ chart_inv c y IN X /\
                                 SND c (chart_inv c y) = y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Uc" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      SET_TAC[];
      ASM SET_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `a:real`; `b:real`; `s:real`; `T2:real`; `KR:real`; `KP:real`; `KM0:real`;
                 `K:real`; `c:(A->bool)#(A->real^3)`] RFA_HSET_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lricci_flow Uc s T2 (\t. metric_local atlas (c:(A->bool)#(A->real^3))
                                        ((g:real->A->real^3^3) t))` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LRICCI_FLOW_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `y0 = SND (c:(A->bool)#(A->real^3)) (xs:A)` THEN
  ABBREV_TAC `psi0 = (psi:real->A->real) Ts xs` THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) y0 = (xs:A)` ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* not positive definite in the chart c *)
  SUBGOAL_THEN
   `~rfa_hpd_cc (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) Ts)) s Ts
       (dd * exp(B * (Ts - s)) + eta * exp(L * (Ts - s)) * psi0)
       (e * exp(A * (Ts - s)) / (Ts - s) + eta * exp(L * (Ts - s)) * psi0) y0`
  ASSUME_TAC THENL
   [UNDISCH_TAC `~rfa_hgood atlas (g:real->A->real^3^3) s
        (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * (psi:real->A->real) t x)
        (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x) Ts xs` THEN
    REWRITE_TAC[rfa_hgood; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `c':(A->bool)#(A->real^3)` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) Ts`; `c:(A->bool)#(A->real^3)`;
                   `c':(A->bool)#(A->real^3)`; `xs:A`; `s:real`; `Ts:real`;
                   `dd * exp(B * (Ts - s)) + eta * exp(L * (Ts - s)) * psi0`;
                   `e * exp(A * (Ts - s)) / (Ts - s) + eta * exp(L * (Ts - s)) * psi0`]
           RFA_HPSD_CC_CHARTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* positive semidefinite at time Ts on the chart image *)
  SUBGOAL_THEN
   `!y. y IN Uc
        ==> rfa_hpsd_cc (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) Ts)) s Ts
              (dd * exp(B * (Ts - s)) + eta * exp(L * (Ts - s)) * (psi:real->A->real) Ts (chart_inv c y))
              (e * exp(A * (Ts - s)) / (Ts - s) + eta * exp(L * (Ts - s)) * psi Ts (chart_inv c y))
              y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC RFA_HPSD_LIMIT_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`; `T2:real`; `KR:real`;
                          `KP:real`; `KM0:real`; `K:real`; `x0:A`; `C:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_REAL_ARITH_TAC THEN
    UNDISCH_TAC `(y:real^3) IN Uc` THEN EXPAND_TAC "Uc" THEN EXPAND_TAC "X" THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  (* a frame and a null vector at y0 *)
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))
                  (metric_local atlas c ((g:real->A->real^3^3) Ts)) /\
                y0 IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) Ts)`;
                 `y0:real^3`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) Ts)`;
                 `y0:real^3`; `S:real^3^3`; `s:real`; `Ts:real`;
                 `dd * exp(B * (Ts - s)) + eta * exp(L * (Ts - s)) * psi0`;
                 `e * exp(A * (Ts - s)) / (Ts - s) + eta * exp(L * (Ts - s)) * psi0`]
         RFA_NULL_EXISTS_CC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y0:real^3` o check (fun th ->
      try can (find_term (fun t -> try fst(dest_const t) = "rfa_hpsd_cc" with Failure _ -> false)) (concl th) && is_forall (concl th) with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u0:num->num->real` (X_CHOOSE_THEN `w0:num->real` STRIP_ASSUME_TAC))] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[REAL_ARITH `x = --y <=> x + y = &0`] o
    check (fun th -> concl th = `!i j. (u0:num->num->real) i j = --(u0 j i)`)) THEN
  (* the barrier at (Ts, xs) *)
  UNDISCH_TAC `rfa_hbar (top,atlas) (g:real->A->real^3^3) s T2 x0 C psi` THEN
  REWRITE_TAC[rfa_hbar] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`Ts:real`; `xs:A`; `c:(A->bool)#(A->real^3)`] o check (fun th ->
    try can (find_term ((=) `lgrad2:(real^3->real^3^3)->(real^3->real)->real^3->real`)) (concl th)
    with Failure _ -> false)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^3->bool` (X_CHOOSE_THEN `q:real^3->real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`Ts:real`; `xs:A`] o check (fun th ->
    try can (find_term ((=) `s':real`)) (concl th) with Failure _ -> false)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dB:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= psi0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(psi:real->A->real) Ts xs = psi0`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `dl = min dB (Ts - s)` THEN
  SUBGOAL_THEN `&0 < dl /\ s <= Ts - dl /\ dl <= dB` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the contradiction at the touching point *)
  MP_TAC(BETA_RULE(ISPECL
   [`Uc:real^3->bool`; `s:real`; `T2:real`;
    `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
    `s:real`; `Ts:real`; `y0:real^3`; `S:real^3^3`; `u0:num->num->real`; `w0:num->real`;
    `\t (y:real^3). (psi:real->A->real) t (chart_inv (c:(A->bool)#(A->real^3)) y)`;
    `W INTER (Uc:real^3->bool)`; `q:real^3->real`; `dl:real`; `C:real`; `psi0:real`;
    `dd:real`; `e:real`; `eta:real`; `tau0:real`; `T2 - s:real`;
    `KR:real`; `KP:real`; `KM0:real`; `K:real`; `CZ:real`; `B:real`; `A:real`; `L:real`]
   RFA_TOUCH_CONTRA)) THEN
  MATCH_MP_TAC(TAUT `p ==> (p ==> F) ==> F`) THEN
  UNDISCH_TAC `rfa_hset (top,atlas) (g:real->A->real^3^3) a b s T2 KR KP KM0 K` THEN
  REWRITE_TAC[rfa_hset] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`Ts:real`; `xs:A`; `c:(A->bool)#(A->real^3)`; `S:real^3^3`] o
    check (fun th -> try can (find_term (fun t -> try fst(dest_const t) = "rfa_hframe" with Failure _ -> false)) (concl th) && is_forall(concl th) with Failure _ -> false)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfa_hframe] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> try fst(dest_const t) = "rfa_ft" with Failure _ -> false)) (concl th)
    then REWRITE_RULE[ASSUME `SND (c:(A->bool)#(A->real^3)) (xs:A) = y0`] th else th) THEN
  let acc = FIRST_ASSUM ACCEPT_TAC in
  REPEAT CONJ_TAC THENL
   [acc; REWRITE_TAC[REAL_LE_REFL];
    UNDISCH_TAC `s + tau0 <= Ts` THEN UNDISCH_TAC `&0 < tau0` THEN REAL_ARITH_TAC;
    acc; acc; acc; acc;
    acc; acc; acc; acc; acc;
    acc; acc; acc; acc;
    UNDISCH_TAC `s + tau0 <= Ts` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `Ts < T2` THEN REAL_ARITH_TAC;
    acc; acc; acc; acc; acc; acc;
    GEN_TAC THEN GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th ->
      concl th = `!i j. (u0:num->num->real) i j + u0 j i = &0`)) THEN
    REAL_ARITH_TAC;
    acc; acc;
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN acc;
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THEN acc;
    REWRITE_TAC[INTER_SUBSET];
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try is_forall(concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "rfa_hpsd_cc" with Failure _ -> false)) (concl th) &&
          can (find_term ((=) `Uc:real^3->bool`)) (concl th) with Failure _ -> false)) THEN
    acc;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^3->bool` THEN
    REWRITE_TAC[INTER_SUBSET] THEN acc;
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try is_forall(concl th) && can (find_term ((=) `q:real^3->real`)) (concl th) &&
          is_imp(snd(dest_forall(concl th))) with Failure _ -> false)) THEN
    acc;
    acc;
    UNDISCH_TAC `chart_inv (c:(A->bool)#(A->real^3)) y0 = (xs:A)` THEN
    DISCH_THEN SUBST1_TAC THEN acc;
    acc; acc; acc; acc; acc;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_HPD_IMP_HPSD THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          try is_forall(concl th) &&
              can (find_term ((=) `metric_field:(real^3->bool)->(real^3->real^3^3)->bool`)) (concl th)
          with Failure _ -> false)) THEN
        UNDISCH_TAC `T2 < b` THEN UNDISCH_TAC `a < s` THEN UNDISCH_TAC `s <= Ts - dl` THEN
        UNDISCH_TAC `Ts - dl < t` THEN UNDISCH_TAC `t < Ts` THEN UNDISCH_TAC `Ts < T2` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL [acc; ALL_TAC] THEN
      UNDISCH_TAC `chart_inv (c:(A->bool)#(A->real^3)) y0 = (xs:A)` THEN
      DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `xs:A`] o check (fun th ->
        try can (find_term (fun t -> try fst(dest_const t) = "rfa_hgood" with Failure _ -> false)) (concl th) && is_forall(concl th) with Failure _ -> false)) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `s <= Ts - dl` THEN UNDISCH_TAC `Ts - dl < t` THEN REAL_ARITH_TAC;
          acc; acc];
        ALL_TAC] THEN
      REWRITE_TAC[rfa_hgood] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
      ANTS_TAC THENL [CONJ_TAC THEN acc; ALL_TAC] THEN
      UNDISCH_TAC `SND (c:(A->bool)#(A->real^3)) (xs:A) = y0` THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[];
      UNDISCH_TAC `chart_inv (c:(A->bool)#(A->real^3)) y0 = (xs:A)` THEN
      DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        try can (find_term ((=) `dB:real`)) (concl th) && is_forall(concl th) with Failure _ -> false)) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `s <= Ts - dl` THEN UNDISCH_TAC `Ts - dl < t` THEN REAL_ARITH_TAC;
          UNDISCH_TAC `dl <= dB` THEN UNDISCH_TAC `Ts - dl < t` THEN REAL_ARITH_TAC;
          UNDISCH_TAC `t < Ts` THEN REAL_ARITH_TAC];
        REAL_ARITH_TAC]];
    acc; acc; acc; acc]);;

(* ========================================================================= *)
(* The perturbed form is positive definite at every joinable                 *)
(* point for s < t <= Tm < T2 (RFA_HARNACK_PD_PERT), by the first-bad-time   *)
(* lemma RFA_FIRST_BAD_TIME on the joinable component X of x0: small times  *)
(* (RFA_HGOOD_SMALL), bad points in a compact set of the barrier             *)
(* (RFA_HGOOD_LARGE), openness (RFA_HGOOD_OPEN), no touching point           *)
(* (RFA_HGOOD_TOUCH).                                                        *)
(* ========================================================================= *)

let RFA_HARNACK_PD_PERT = prove
 (`!top atlas (g:real->A->real^3^3) a b s T2 KR KP KM0 K (psi:real->A->real) x0 C
    dd e eta tau0 CZ B A L Tm.
     rfa_hset (top,atlas) g a b s T2 KR KP KM0 K /\ rfa_hbar (top,atlas) g s T2 x0 C psi /\
     &0 <= C /\ &0 < e /\ &0 < dd /\ &0 < eta /\ Tm < T2 /\
     tau0 = e / (&3 * KM0 + &9 * KP * (&6 * KP + &1) / dd + &1) /\
     B = &12 * KP + &324 * KR + &2 /\ A = &18 * KR + &2 /\
     CZ = &3 * (KM0 + K / (&2 * tau0)) + &9 * KP + &9 * KR /\
     L = &2 * C + &2 * ((C + &1) * (&5 * K + inv tau0)) +
         (&6 * (KM0 + K / (&2 * tau0)) + &36 * KP) + (&12 * KP + &324 * KR) + &2 +
         &2 * (e * exp(A * (T2 - s)) / tau0) + &2 * CZ + &18 * KR +
         &2 * (&18 * K pow 2 + inv(&2 * tau0 pow 2)) + &1 /\
     dd * exp(B * (T2 - s)) <= &1 /\
     dd * exp(B * (T2 - s)) *
       ((T2 - s) pow 2 * (&6 * KM0 + &36 * KP + &36 * K pow 2) + &3 * K * (T2 - s) + &1) < e
     ==> !t x. s < t /\ t <= Tm /\ mfd_joinable (top,atlas) x0 x
               ==> rfa_hgood atlas g s
                     (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * psi t x)
                     (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x)
                     t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if is_eq (concl th) &&
       mem (lhs(concl th)) [`tau0:real`; `CZ:real`; `L:real`; `B:real`; `A:real`]
    then SYM th else th) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                a < s /\ s < T2 /\ T2 < b /\ &0 <= KR /\ &0 <= KP /\ &0 <= KM0 /\ &0 <= K`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_hset (top,atlas) (g:real->A->real^3^3) a b s T2 KR KP KM0 K` THEN
    REWRITE_TAC[rfa_hset; ricci_flow_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau0` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `tau0:real`)) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 < x + y + &1`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= CZ` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `CZ:real`)) THEN
    SUBGOAL_THEN `&0 <= K / (&2 * tau0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `L:real`)) THEN
    SUBGOAL_THEN `&0 <= inv tau0 /\ &0 <= K / (&2 * tau0) /\ &0 <= e * exp(A * (T2 - s)) / tau0 /\
                  &0 <= inv(&2 * tau0 pow 2) /\ &0 <= K pow 2`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div] THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        TRY(MATCH_MP_TAC REAL_LE_INV) THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (C + &1) * (&5 * K + inv tau0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfa_hbar] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfa_hbar" with Failure _ -> false)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CZ / eta` o check (fun th ->
    try can (find_term (fun t -> try fst(dest_const t) = "compact_in" with Failure _ -> false)) (concl th) with Failure _ -> false)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc:A->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `X = {x:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x0 x}` THEN
  SUBGOAL_THEN `(X:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (X:A->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `X = connected_component_of top (x0:A)` SUBST1_TAC THENL
     [EXPAND_TAC "X" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MFD_JOINABLE_CONNECTED_COMPONENT] THEN REWRITE_TAC[IN];
      REWRITE_TAC[CLOSED_IN_CONNECTED_COMPONENT_OF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x0 x <=> x IN X`
  (LABEL_TAC "jx") THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  USE_THEN "jx" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `!t x. s < t /\ t <= Tm /\ t <= s + tau0 /\ (x:A) IN X
                      ==> rfa_hgood atlas (g:real->A->real^3^3) s
                            (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * psi t x)
                            (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x)
                            t x`
  (LABEL_TAC "small") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_HGOOD_SMALL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`; `T2:real`; `KR:real`; `KP:real`;
                          `KM0:real`; `K:real`] THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
        check (fun th -> concl th = `(X:A->bool) SUBSET topspace top`)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [ASM_REAL_ARITH_TAC;
      (MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC THEN NO_TAC)];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`top:A topology`; `X:A->bool`; `Kc:A->bool`;
    `rfa_hgood atlas (g:real->A->real^3^3) s
       (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * (psi:real->A->real) t x)
       (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x)`;
    `s:real`; `Tm:real`; `tau0:real`] RFA_FIRST_BAD_TIME) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
    (* bad points lie in the compact set *)
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `t <= s + tau0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try can (find_term ((=) `Kc:A->bool`)) (concl th) && is_forall(concl th) with Failure _ -> false)) THEN
    EXISTS_TAC `t:real` THEN USE_THEN "jx" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~rfa_hgood atlas (g:real->A->real^3^3) s
       (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * (psi:real->A->real) t x)
       (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x) t x` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RFA_HGOOD_LARGE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`; `T2:real`; `KR:real`; `KP:real`;
                          `KM0:real`; `K:real`; `tau0:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 <= exp(L * (t - s))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + L * (t - s)` THEN
      REWRITE_TAC[REAL_EXP_LE_X] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `CZ < eta * (psi:real->A->real) t x` ASSUME_TAC THENL
     [UNDISCH_TAC `CZ / eta < (psi:real->A->real) t x` THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `eta * (psi:real->A->real) t x <= eta * exp(L * (t - s)) * psi t x` MP_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `eta * x * p = x * (eta * p)`] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    (* openness *)
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                   `a:real`; `b:real`; `s:real`; `T2:real`; `KR:real`; `KP:real`; `KM0:real`;
                   `K:real`; `psi:real->A->real`; `x0:A`; `dd:real`; `e:real`; `eta:real`;
                   `L:real`; `B:real`; `A:real`; `t:real`; `x:A`] RFA_HGOOD_OPEN) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_REAL_ARITH_TAC THEN
      ASM_REWRITE_TAC[];
      USE_THEN "jx" (fun th -> REWRITE_TAC[th])] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:A->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    (* the touching point *)
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                   `a:real`; `b:real`; `s:real`; `T2:real`; `KR:real`; `KP:real`; `KM0:real`;
                   `K:real`; `psi:real->A->real`; `x0:A`; `C:real`; `dd:real`; `e:real`;
                   `eta:real`; `tau0:real`; `CZ:real`; `B:real`; `A:real`; `L:real`;
                   `t:real`; `x:A`] RFA_HGOOD_TOUCH) THEN
    MATCH_MP_TAC(TAUT `p ==> (p ==> F) ==> F`) THEN
    USE_THEN "jx" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~rfa_hgood atlas (g:real->A->real^3^3) s
       (\t x. dd * exp(B * (t - s)) + eta * exp(L * (t - s)) * (psi:real->A->real) t x)
       (\t x. e * exp(A * (t - s)) / (t - s) + eta * exp(L * (t - s)) * psi t x) t x` THEN
    REWRITE_TAC[] THEN USE_THEN "small" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The limits eta -> 0, dd -> 0, e -> 0 (RFA_AFFINE_LIM,                     *)
(* RFA_HARNACK_LIMITS; the form is affine in the perturbation parameters by  *)
(* RFA_ZCC_AFFINE) and the headline RFA_HARNACK_MATRIX: Hamilton's matrix    *)
(* Harnack inequality in dimension 3 in chart form,                          *)
(*   Z(U,W) = M(W,W) + 2 P(U,W) + Rm(U,U) >= 0 at every time s < t < T2,     *)
(* M taken with the 1/(2(t - s)) term, for a complete flow with the frame    *)
(* bounds of rfa_hset and a Ricci bound (the barrier of pc_rfa_hbar).        *)
(* ========================================================================= *)

let RFA_AFFINE_LIM = prove
 (`!a b d. &0 < d /\ (!x. &0 < x /\ x < d ==> &0 <= a + x * b) ==> &0 <= a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `x = min (d / &2) (--a / (abs b + &1))` THEN
  SUBGOAL_THEN `&0 < x /\ x < d /\ x * abs b < --a` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < --a / (abs b + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "x" THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "x" THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(--a / (abs b + &1)) * abs b` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN EXPAND_TAC "x" THEN
        REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 < abs b + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_FIELD `&0 < c ==> (y / c) * z = (y * z) / c`; REAL_LT_LDIV_EQ] THEN
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(REAL_ARITH `x * b <= abs(x * b)`) THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs x = x` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RFA_HBAR_MONO = prove
 (`!top atlas (g:real->A->real^3^3) t1 t2 x0 C C' (psi:real->A->real).
     rfa_hbar (top,atlas) g t1 t2 x0 C psi /\ C <= C'
     ==> rfa_hbar (top,atlas) g t1 t2 x0 C' psi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_hbar] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    LABEL_TAC "one" (el 0 ths) THEN LABEL_TAC "back" (el 3 ths) THEN
    LABEL_TAC "chart" (el 4 ths) THEN REWRITE_TAC[el 0 ths; el 1 ths; el 2 ths]) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 <= (psi:real->A->real) t x` ASSUME_TAC THENL
     [USE_THEN "one" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "back" (MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s':real`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `C * (t - s') * (psi:real->A->real) t x <= C' * (t - s') * psi t x` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `c:(A->bool)#(A->real^3)`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 <= (psi:real->A->real) t x` ASSUME_TAC THENL
     [USE_THEN "one" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "chart" (MP_TAC o SPECL [`t:real`; `x:A`; `c:(A->bool)#(A->real^3)`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `W:real^3->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^3->real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * (psi:real->A->real) t x` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * (psi:real->A->real) t x pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2]]]);;

let RFA_HARNACK_PSD_AT = prove
 (`!top atlas (g:real->A->real^3^3) a b s T2 KR KP KM0 K (psi:real->A->real) C dd e t x c.
     rfa_hset (top,atlas) g a b s T2 KR KP KM0 K /\ rfa_hbar (top,atlas) g s T2 x C psi /\
     &0 <= C /\ &0 < e /\ &0 < dd /\ s < t /\ t < T2 /\ x IN topspace top /\
     c IN atlas /\ x IN FST c /\
     dd * exp((&12 * KP + &324 * KR + &2) * (T2 - s)) <= &1 /\
     dd * exp((&12 * KP + &324 * KR + &2) * (T2 - s)) *
       ((T2 - s) pow 2 * (&6 * KM0 + &36 * KP + &36 * K pow 2) + &3 * K * (T2 - s) + &1) < e
     ==> ?L. !eta. &0 < eta
               ==> rfa_hpsd_cc (metric_local atlas c (g t)) s t
                     (dd * exp((&12 * KP + &324 * KR + &2) * (t - s)) +
                      eta * exp(L * (t - s)) * psi t x)
                     (e * exp((&18 * KR + &2) * (t - s)) / (t - s) +
                      eta * exp(L * (t - s)) * psi t x)
                     (SND c x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a < s /\ T2 < b` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_hset (top,atlas) (g:real->A->real^3^3) a b s T2 KR KP KM0 K` THEN
    REWRITE_TAC[rfa_hset] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `tau0 = e / (&3 * KM0 + &9 * KP * (&6 * KP + &1) / dd + &1)` THEN
  ABBREV_TAC `CZ = &3 * (KM0 + K / (&2 * tau0)) + &9 * KP + &9 * KR` THEN
  EXISTS_TAC `&2 * C + &2 * ((C + &1) * (&5 * K + inv tau0)) +
         (&6 * (KM0 + K / (&2 * tau0)) + &36 * KP) + (&12 * KP + &324 * KR) + &2 +
         &2 * (e * exp((&18 * KR + &2) * (T2 - s)) / tau0) + &2 * CZ + &18 * KR +
         &2 * (&18 * K pow 2 + inv(&2 * tau0 pow 2)) + &1` THEN
  X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `a:real`; `b:real`; `s:real`; `T2:real`; `KR:real`; `KP:real`; `KM0:real`;
                 `K:real`; `psi:real->A->real`; `x:A`; `C:real`; `dd:real`; `e:real`;
                 `eta:real`; `tau0:real`; `CZ:real`; `&12 * KP + &324 * KR + &2`;
                 `&18 * KR + &2`;
                 `&2 * C + &2 * ((C + &1) * (&5 * K + inv tau0)) +
                  (&6 * (KM0 + K / (&2 * tau0)) + &36 * KP) + (&12 * KP + &324 * KR) + &2 +
                  &2 * (e * exp((&18 * KR + &2) * (T2 - s)) / tau0) + &2 * CZ + &18 * KR +
                  &2 * (&18 * K pow 2 + inv(&2 * tau0 pow 2)) + &1`;
                 `t:real`] RFA_HARNACK_PD_PERT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; MFD_JOINABLE_REFL] THEN
  REWRITE_TAC[rfa_hgood] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MATCH_MP_TAC RFA_HPD_IMP_HPSD THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `a:real`; `b:real`; `s:real`; `T2:real`; `KR:real`;
                   `KP:real`; `KM0:real`; `K:real`; `c:(A->bool)#(A->real^3)`] RFA_HSET_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let RFA_HARNACK_LIMITS = prove
 (`!Z D1 D2 EB EA E Q.
     &0 < E /\ &1 <= Q /\
     (!e dd. &0 < e /\ &0 < dd /\ dd * E <= &1 /\ dd * E * Q < e
             ==> ?Lt. !eta. &0 < eta
                       ==> &0 <= Z + (dd * EB + eta * Lt) * D1 + (e * EA + eta * Lt) * D2)
     ==> &0 <= Z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!e dd. &0 < e /\ &0 < dd /\ dd * E <= &1 /\ dd * E * Q < e
                       ==> &0 <= Z + dd * EB * D1 + e * EA * D2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:real`; `dd:real`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `Lt:real`) THEN
    MATCH_MP_TAC RFA_AFFINE_LIM THEN
    MAP_EVERY EXISTS_TAC [`Lt * (D1 + D2)`; `&1`] THEN REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `eta:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `eta:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. &0 < e ==> &0 <= Z + e * EA * D2` ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC RFA_AFFINE_LIM THEN
    MAP_EVERY EXISTS_TAC [`EB * D1`; `e / (E * (Q + e))`] THEN
    SUBGOAL_THEN `&0 < E * (Q + e)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `dd:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `dd * (E * (Q + e)) < e` ASSUME_TAC THENL
     [UNDISCH_TAC `dd < e / (E * (Q + e))` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= dd * E` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (dd * E) * Q /\ &0 <= (dd * E) * e` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(dd * E) * Q + (dd * E) * e < e` ASSUME_TAC THENL
     [UNDISCH_TAC `dd * (E * (Q + e)) < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `dd * E < &1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`dd * E`; `&1`; `e:real`] REAL_LT_RMUL_EQ) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:real`; `dd:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_AFFINE_LIM THEN MAP_EVERY EXISTS_TAC [`EA * D2`; `&1`] THEN
  REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFA_HARNACK_MATRIX = prove
 (`!top atlas (g:real->A->real^3^3) a b s T2 KR KP KM0 K Kric.
     hausdorff_space top /\ rfa_hset (top,atlas) g a b s T2 KR KP KM0 K /\
     (!t. s <= t /\ t <= T2 ==> mfd_complete (top,atlas) (g t)) /\
     (!t x v. s <= t /\ t <= T2 /\ x IN topspace top
              ==> abs(mfd_ricci atlas (g t) x v v) <= Kric * (v dot (g t x ** v)))
     ==> !t x c. s < t /\ t < T2 /\ x IN topspace top /\ c IN atlas /\ x IN FST c
                 ==> rfa_hpsd_cc (metric_local atlas c (g t)) s t (&0) (&0) (SND c x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `c:(A->bool)#(A->real^3)`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3) /\ a < s /\ s < T2 /\
                T2 < b /\ &0 <= KR /\ &0 <= KP /\ &0 <= KM0 /\ &0 <= K`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_hset (top,atlas) (g:real->A->real^3^3) a b s T2 KR KP KM0 K` THEN
    REWRITE_TAC[rfa_hset] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `a:real`; `b:real`; `s:real`; `T2:real`; `Kric:real`; `x:A`] RFA_HBAR_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (X_CHOOSE_TAC `psi:real->A->real`)) THEN
  SUBGOAL_THEN `rfa_hbar (top,atlas) (g:real->A->real^3^3) s T2 x (max C0 (&0)) psi`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_HBAR_MONO THEN EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))
                             (metric_local atlas c ((g:real->A->real^3^3) t)) /\
                SND c x IN IMAGE (SND c) (FST c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:real->A->real^3^3`; `a:real`; `b:real`; `s:real`; `T2:real`; `KR:real`;
                     `KP:real`; `KM0:real`; `K:real`; `c:(A->bool)#(A->real^3)`]
                    RFA_HSET_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_hpsd_cc] THEN
  MAP_EVERY X_GEN_TAC [`Am:real^3^3`; `w:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!alpha beta.
      rfa_zcc (metric_local atlas c ((g:real->A->real^3^3) t)) s t alpha beta
              (SND (c:(A->bool)#(A->real^3)) x) Am w =
      rfa_zcc (metric_local atlas c (g t)) s t (&0) (&0) (SND c x) Am w +
      alpha * (rfa_zcc (metric_local atlas c (g t)) s t (&1) (&0) (SND c x) Am w -
               rfa_zcc (metric_local atlas c (g t)) s t (&0) (&0) (SND c x) Am w) +
      beta * (rfa_zcc (metric_local atlas c (g t)) s t (&0) (&1) (SND c x) Am w -
              rfa_zcc (metric_local atlas c (g t)) s t (&0) (&0) (SND c x) Am w)`
  (LABEL_TAC "aff") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_ZCC_AFFINE THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z00 = rfa_zcc (metric_local atlas c ((g:real->A->real^3^3) t)) s t (&0) (&0)
                            (SND (c:(A->bool)#(A->real^3)) x) Am w` THEN
  ABBREV_TAC `z10 = rfa_zcc (metric_local atlas c ((g:real->A->real^3^3) t)) s t (&1) (&0)
                            (SND (c:(A->bool)#(A->real^3)) x) Am w` THEN
  ABBREV_TAC `z01 = rfa_zcc (metric_local atlas c ((g:real->A->real^3^3) t)) s t (&0) (&1)
                            (SND (c:(A->bool)#(A->real^3)) x) Am w` THEN
  MATCH_MP_TAC RFA_HARNACK_LIMITS THEN
  MAP_EVERY EXISTS_TAC
   [`z10 - z00:real`; `z01 - z00:real`; `exp((&12 * KP + &324 * KR + &2) * (t - s))`;
    `exp((&18 * KR + &2) * (t - s)) / (t - s)`; `exp((&12 * KP + &324 * KR + &2) * (T2 - s))`;
    `(T2 - s) pow 2 * (&6 * KM0 + &36 * KP + &36 * K pow 2) + &3 * K * (T2 - s) + &1`] THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &1 <= x + y + &1`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MP_TAC(SPEC `K:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`e:real`; `dd:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `a:real`; `b:real`; `s:real`; `T2:real`; `KR:real`; `KP:real`; `KM0:real`;
                 `K:real`; `psi:real->A->real`; `max C0 (&0)`; `dd:real`; `e:real`; `t:real`;
                 `x:A`; `c:(A->bool)#(A->real^3)`] RFA_HARNACK_PSD_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  EXISTS_TAC `exp(L * (t - s)) * (psi:real->A->real) t x` THEN
  X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `eta:real`) THEN ASM_REWRITE_TAC[rfa_hpsd_cc] THEN
  DISCH_THEN(MP_TAC o SPECL [`Am:real^3^3`; `w:real^3`]) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

