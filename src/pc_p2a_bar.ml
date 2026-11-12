(* ========================================================================= *)
(* pc_p2a_bar: L13, P2A_BARRIER_FIX (MT Prop 7.8 at a local minimum of l in  *)
(* its slice; MT applies Lemma 6.49, proved for minimizing L-geodesics, to a *)
(* local length function), by slice minimality.                              *)
(* The first part: the minimizer is the L-geodesic of some Z in Smin         *)
(* (P2A_MIN_LGEOD_GEN), with the slice minimality transferred.               *)
(* ========================================================================= *)

needs "src/pc_p2a_lsv.ml";;
needs "src/pc_p2a_defs3.ml";;

prioritize_real();;
type_invention_error := true;;

let P2AL_BAR_SETUP = prove
 (`!(V:p2alv) tt (x:A) b gamma O.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_min V tt x b gamma /\
     open_in (p2a_vtop V (tt - b)) O /\ gamma b IN O /\
     (!g'. p2a_adm V tt x b g' /\ g' b IN O
           ==> p2a_L_length V tt gamma b <= p2a_L_length V tt g' b)
     ==> ?Z. Z IN p2a_Smin V tt x b /\ x IN topspace(p2a_vtop V tt) /\ &0 < b /\
             (!tau. &0 <= tau /\ tau <= b ==> gamma tau = p2a_Lgeo V tt x Z b tau) /\
             p2a_pc1 V tt gamma (&0) b {} /\
             p2a_L_length V tt gamma b = p2a_Ltil V tt x b Z /\
             p2a_Lexp V tt x b Z = gamma b /\
             (!g'. p2a_adm V tt x b g' /\ g' b IN O
                   ==> p2a_Ltil V tt x b Z <= p2a_L_length V tt g' b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`]
                P2A_MIN_LGEOD_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `Z:real^N` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min; p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(p2a_vtop (V:p2alv) tt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2AL_LDOM_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_L_length (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) b = p2a_L_length V tt gamma b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AL_LENGTH_CONG THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_Lexp (V:p2alv) tt (x:A) b Z = gamma b` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_Lexp] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2a_Ltil] THEN
  ASM_REWRITE_TAC[p2a_Smin; IN_ELIM_THM; p2a_min] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AL_LGEO_ADM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `g':real->A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p2a_min (V:p2alv) tt (x:A) b gamma` THEN
  REWRITE_TAC[p2a_min] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(g':real->A) b = p2a_Lgeo (V:p2alv) tt (x:A) Z b b` THEN
  ASM_REWRITE_TAC[GSYM p2a_Lexp]);;

(* ========================================================================= *)
(* First order at a slice minimum.  If gamma_Z is shortest among admissible *)
(* curves ending in an open set O of the slice around its end point, its    *)
(* velocity vanishes there: moving the end point along -m by a chart piece  *)
(* on [s1,sb] changes the length by -kk |m|^2 + O(kk^2) (P2AL_CTL_WIN).     *)
(* ========================================================================= *)

let P2AL_END_VEL0 = prove
 (`!(V:p2alv) tt (x:A) Z O sb sw r W a' b' U (phi:A->real^N) N Phi.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x (sb pow 2) /\ &0 < sb /\
     open_in (p2a_vtop V (tt - sb pow 2)) O /\ p2a_Lexp V tt x (sb pow 2) Z IN O /\
     (!g'. p2a_adm V tt x (sb pow 2) g' /\ g' (sb pow 2) IN O
           ==> p2a_Ltil V tt x (sb pow 2) Z <= p2a_L_length V tt g' (sb pow 2)) /\
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\ sw < sb /\ sb < sw + r /\
     p2al_lin V tt sw r W b' U phi Phi Z sb
     ==> sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb) = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "SLM") STRIP_ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi /\ &0 <= sw`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ p2a_region (V:p2alv) W a' b' /\ (U,phi:A->real^N) IN p2a_vatlas V b'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_lwa]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. sw < s /\ s < sw + r ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'`
  (LABEL_TAC "TIME") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AL_WIN_TIME THEN
    MAP_EVERY EXISTS_TAC [`V:p2alv`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `U:A->bool`;
                          `phi:A->real^N`; `N:real^N->bool`;
                          `Phi:real^N->real^(N,N)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E")) o
             last o CONJUNCTS) THEN
  ABBREV_TAC `s1 = sb - min (e / &2) ((sb - sw) / &2)` THEN
  SUBGOAL_THEN `sw < s1 /\ s1 < sb /\ &0 < s1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sb ==> p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s`
  (LABEL_TAC "LIN") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "E" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s1:real`; `sb:real`] P2AL_WIN_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rz:real` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `K:real^(1,(N,N)finite_sum)finite_sum->bool` (X_CHOOSE_THEN `B:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TUBE") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TAY") (LABEL_TAC "SEG"))))))))))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) (U INTER W)) ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow")) (concl th))) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) = vec 0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN
     `chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) =
      p2a_Lexp V tt x (sb pow 2) Z` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lexp")) (concl th))) THEN
      MATCH_MP_TAC P2A_REGION_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`V:p2alv`; `a':real`; `b':real`] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "TIME" (MP_TAC o SPEC `sb:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                   `phi:A->real^N`; `tt - sb pow 2`; `O:A->bool`; `fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)`]
                  P2A_CHART_INV_NBHD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "TIME" (MP_TAC o SPEC `sb:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `rO:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NB"))) THEN
    SUBGOAL_THEN `&0 < inv(sb - s1) /\ inv(sb - s1) * (sb - s1) = &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `L1 = &1 + inv(sb - s1)` THEN
    SUBGOAL_THEN `&0 < L1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= B * L1 pow 2 * (sb - s1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `kk = min (min (rO / (norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) + &1)) (rho / (norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) * L1 + &1)))
                         (&1 / (B * L1 pow 2 * (sb - s1) + &1)) / &2` THEN
    SUBGOAL_THEN `&0 < kk /\ kk < rO / (norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) + &1) /\
                  kk < rho / (norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) * L1 + &1) /\
                  kk < &1 / (B * L1 pow 2 * (sb - s1) + &1)` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < rO / (norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) + &1) /\ &0 < rho / (norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) * L1 + &1) /\
                    &0 < &1 / (B * L1 pow 2 * (sb - s1) + &1)` MP_TAC THENL
       [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
        EXPAND_TAC "kk" THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `kk * norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) < rO /\ kk * (norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) * L1) <= rho /\
                  kk * (B * L1 pow 2 * (sb - s1)) < &1` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `kk * (norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) + &1)` THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 < n ==> &0 < n + &1`];
        MATCH_MP_TAC P2AL_DIV_BOUND THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `kk * (B * L1 pow 2 * (sb - s1) + &1)` THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= n ==> &0 < n + &1`]];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(kk % ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))) = kk * norm ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < x ==> abs x = x`]; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s1:real`; `sb:real`; `rz:real`; `rho:real`;
                   `K:real^(1,(N,N)finite_sum)finite_sum->bool`; `B:real`; `Z:real^N`;
                   `inv(sb - s1)`; `s1:real`; `kk % ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))`; `s1:real`; `sb:real`;
                   `norm(kk % ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))) * L1`] P2AL_CTL_WIN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_CBALL; REAL_LE_REFL] THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      TRY(REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN NO_TAC) THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`inv(sb - s1)`; `s1:real`; `kk % ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))`; `s1:real`; `sb:real`; `s:real`]
                    P2AL_AFF_NORM) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `inv(sb - s1) * (sb - s1) * norm(kk % ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))) + inv(sb - s1) * norm(kk % ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))) =
                    norm(kk % ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))) * L1` SUBST1_TAC THENL
       [EXPAND_TAC "L1" THEN
        SUBGOAL_THEN `~(sb - s1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c /\ a <= b`) THEN
      UNDISCH_TAC `kk * (norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) * L1) <= rho` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "MEM") (LABEL_TAC "CTL")) THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                   `phi:A->real^N`; `(\v. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (drop v)) + (inv(sb - s1) * (s1 - drop v)) % (kk % ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))))`; `s1:real`; `sb:real`; `sw:real`; `sw + r`]
                  P2A_CHART_CURVE_SEG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "MEM" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "LIN" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      MATCH_MP_TAC P2AL_FLOW_AFF_CURVE THEN
      MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `N:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[LIFT_DROP]) THEN
    SUBGOAL_THEN `&0 < s1 pow 2 /\ s1 pow 2 < sb pow 2 /\ &0 <= sb`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `sb pow 2`; `s1 pow 2`]
                  P2AL_LGEO_AGREE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AGR")) THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s1:real`] P2AL_WOK_LGEO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "LIN" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
    SUBGOAL_THEN `p2a_Lgeo (V:p2alv) tt (x:A) Z (sb pow 2) (s1 pow 2) = (\u. chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (sqrt u)) + (inv(sb - s1) * (s1 - sqrt u)) % (kk % ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))))) (s1 pow 2)`
    ASSUME_TAC THENL
     [REWRITE_TAC[] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_SUB_REFL;
                                      REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      USE_THEN "AGR" (MP_TAC o SPEC `s1 pow 2`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `s1 pow 2`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lexp")) (concl th))) THEN
      MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                     `phi:A->real^N`; `p2a_Lexp (V:p2alv) tt (x:A) (s1 pow 2) Z`]
                    P2A_REGION_CHART_INV) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "TIME" (MP_TAC o SPEC `sb:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p2a_Lexp]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `(\u. chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (sqrt u)) + (inv(sb - s1) * (s1 - sqrt u)) % (kk % ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)))))`;
                   `p2a_Lgeo (V:p2alv) tt (x:A) Z (sb pow 2)`;
                   `\u. if u <= s1 pow 2 then p2a_Lgeo (V:p2alv) tt (x:A) Z (sb pow 2) u
                        else (\u. chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (sqrt u)) + (inv(sb - s1) * (s1 - sqrt u)) % (kk % ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))))) u`;
                   `sb pow 2`; `s1 pow 2`] P2A_SEG_GLUE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2A_ADM_RESTRICT THEN EXISTS_TAC `sb pow 2` THEN
        ASM_SIMP_TAC[P2AL_LGEO_ADM; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[REAL_LE_ANTISYM];
      STRIP_TAC] THEN
    SUBGOAL_THEN `chart_inv (U INTER W,phi:A->real^N)
                    (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb) + (inv(sb - s1) * (s1 - sb)) % (kk % ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)))) IN O`
    ASSUME_TAC THENL
     [USE_THEN "NB" (MP_TAC o SPEC
        `fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb) + (inv(sb - s1) * (s1 - sb)) % (kk % ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)))`) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      REWRITE_TAC[dist; VECTOR_ARITH `(a + b) - a:real^N = b`; NORM_MUL] THEN
      SUBGOAL_THEN `abs(inv(sb - s1) * (s1 - sb)) = &1` SUBST1_TAC THENL
       [SUBGOAL_THEN `inv(sb - s1) * (s1 - sb) = --(&1)` SUBST1_TAC THENL
         [SUBGOAL_THEN `~(sb - s1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
          REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_MUL_LID; GSYM NORM_MUL];
      ALL_TAC] THEN
    USE_THEN "SLM" (MP_TAC o SPEC
      `\u. if u <= s1 pow 2 then p2a_Lgeo (V:p2alv) tt (x:A) Z (sb pow 2) u
           else (\u. chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (sqrt u)) + (inv(sb - s1) * (s1 - sqrt u)) % (kk % ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))))) u`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(sb pow 2 <= s1 pow 2)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[POW_2_SQRT]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p2a_L_length (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z (sb pow 2)) (s1 pow 2) =
                  p2a_Ltil V tt x (s1 pow 2) Z` SUBST1_TAC THENL
     [REWRITE_TAC[p2a_Ltil] THEN MATCH_MP_TAC P2AL_LENGTH_CONG THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "AGR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> SUBST1_TAC(MATCH_MP REAL_INTEGRAL_UNIQUE th)) THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s1:real`; `sb:real`] P2AL_LTIL_ADD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "CTL" MP_TAC THEN
    SUBGOAL_THEN `inv(sb - s1) * (s1 - sb) = --(&1)` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(sb - s1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; DOT_LZERO; DOT_LMUL;
                    REAL_SUB_RZERO; GSYM NORM_POW_2] THEN
    SUBGOAL_THEN `B * (kk * norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) * L1) pow 2 * (sb - s1) <
                  kk * norm ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) pow 2` MP_TAC THENL
     [SUBGOAL_THEN `B * (kk * norm ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) * L1) pow 2 * (sb - s1) =
                    (kk * norm ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) pow 2) * (kk * (B * L1 pow 2 * (sb - s1)))` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `p2a_Ltil (V:p2alv) tt (x:A) (sb pow 2) Z - p2a_Ltil V tt x (s1 pow 2) Z =
                 p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v))) s1 sb` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  UNDISCH_TAC `metric_field (IMAGE (phi:A->real^N) (U INTER W)) ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2))` THEN
  REWRITE_TAC[metric_field] THEN
  DISCH_THEN(MP_TAC o SPEC `fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `sndcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[DOT_RZERO; REAL_LT_REFL]);;

(* ========================================================================= *)
(* The second-order expansion behind the slice minimality: with D F = (D    *)
(* y) . m, the function t |-> F(Z0 + t c) - m(Z0) . (y(Z0 + t               *)
(* c) - y(Z0)) is (t^2/2) (D y c) . (D m c) + o(t^2) (P2AL_CHI2), and a     *)
(* trace lemma: w . (M w) >= 0 for all w gives tr(G^-1 M) >= 0.             *)
(* ========================================================================= *)

let P2AL_CHI2 = prove
 (`!S (Fl:real^N->real^1) (fy:real^N->real^N) (mm:real^N->real^N) Z0 c.
     open S /\ Z0 IN S /\ smooth_map_on S fy /\ smooth_map_on S mm /\
     (!Z. Z IN S
          ==> (Fl has_derivative (\h. lift(frechet_derivative fy (at Z) h dot mm Z))) (at Z))
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !t. &0 < t /\ t < d
                         ==> abs(drop(Fl(Z0 + t % c)) - drop(Fl Z0) -
                                 mm Z0 dot (fy(Z0 + t % c) - fy Z0) -
                                 t pow 2 / &2 *
                                 (frechet_derivative fy (at Z0) c dot
                                  frechet_derivative mm (at Z0) c)) <= e * t pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mm:real^N->real^N`; `S:real^N->bool`; `Z0:real^N`] P2A_SMOOTH_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `Lt:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lip")))))) THEN
  SUBGOAL_THEN `((mm:real^N->real^N) has_derivative frechet_derivative mm (at Z0)) (at Z0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `S:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `y1 = frechet_derivative (fy:real^N->real^N) (at Z0) c` THEN
  ABBREV_TAC `m1 = frechet_derivative (mm:real^N->real^N) (at Z0) c` THEN
  SUBGOAL_THEN `(\Z. frechet_derivative (fy:real^N->real^N) (at Z) c) continuous (at Z0)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`S:real^N->bool`; `fy:real^N->real^N`; `c:real^N`]
                  SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2 / (Lt * norm(c:real^N) + &1)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cont"))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `c:real^N` o MATCH_MP P2AL_LINE_SMALLO o check (fun th ->
    can (find_term ((=) `mm:real^N->real^N`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2 / (norm(y1:real^N) + &1)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `y1:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dm"))) THEN
  SUBGOAL_THEN `&0 < norm(c:real^N) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min d3 (min r1 d2 / (norm(c:real^N) + &1))` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_LT_MIN];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t < min r1 d2 / (norm(c:real^N) + &1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= t
                    ==> s * norm(c:real^N) < r1 /\ s * norm c < d2 /\
                        Z0 + s % c IN cball(Z0,r1) /\ Z0 + s % c IN S /\
                        dist(Z0 + s % c,Z0) = s * norm c`
  (LABEL_TAC "pts") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s * norm(c:real^N) < min r1 d2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s * (norm(c:real^N) + &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `t * (norm(c:real^N) + &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(Z0 + s % c,Z0:real^N) = s * norm c` ASSUME_TAC THENL
     [REWRITE_TAC[dist; VECTOR_ARITH `(a + b) - a:real^N = b`; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`];
      ALL_TAC] THEN
    SUBGOAL_THEN `Z0 + s % c IN cball(Z0:real^N,r1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s * norm(c:real^N) < min r1 d2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `s * norm(c:real^N) < min r1 d2` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `s * norm(c:real^N) < min r1 d2` THEN REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= t
        ==> ((\s. drop((Fl:real^N->real^1)(Z0 + s % c)) -
                  (mm:real^N->real^N) Z0 dot (fy:real^N->real^N)(Z0 + s % c))
             has_real_derivative
             (frechet_derivative fy (at (Z0 + s % c)) c dot (mm(Z0 + s % c) - mm Z0)))
            (atreal s)`
  (LABEL_TAC "der0") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "pts" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `((fy:real^N->real^N) has_derivative frechet_derivative fy (at (Z0 + s % c)))
                  (at (Z0 + s % c))` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\Z:real^N. lift((mm:real^N->real^N) Z0 dot (fy:real^N->real^N) Z)`;
                   `\h:real^N. lift((mm:real^N->real^N) Z0 dot
                                    frechet_derivative (fy:real^N->real^N) (at (Z0 + s % c)) h)`;
                   `Z0:real^N`; `c:real^N`; `s:real`] P2AL_LINE_RDERIV) THEN
    ANTS_TAC THENL
     [MP_TAC(INST [`(mm:real^N->real^N) Z0`,`v:real^N`]
        (MATCH_MP HAS_DERIVATIVE_LIFT_DOT (ASSUME
          `((fy:real^N->real^N) has_derivative frechet_derivative fy (at (Z0 + s % c)))
           (at (Z0 + s % c))`))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Fl:real^N->real^1`;
                   `\h:real^N. lift(frechet_derivative (fy:real^N->real^N) (at (Z0 + s % c)) h dot
                                    (mm:real^N->real^N)(Z0 + s % c))`;
                   `Z0:real^N`; `c:real^N`; `s:real`] P2AL_LINE_RDERIV) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP; IMP_IMP] THEN
    DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP HAS_REAL_DERIVATIVE_SUB) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[DOT_RSUB] THEN REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= t
        ==> ((\s. drop((Fl:real^N->real^1)(Z0 + s % c)) -
                  (mm:real^N->real^N) Z0 dot (fy:real^N->real^N)(Z0 + s % c) -
                  s pow 2 / &2 * ((y1:real^N) dot m1))
             has_real_derivative
             (frechet_derivative fy (at (Z0 + s % c)) c dot (mm(Z0 + s % c) - mm Z0) -
              s * (y1 dot m1)))
            (atreal s)`
  (LABEL_TAC "der") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(REAL_DIFF_CONV
      `((\s. s pow 2 / &2 * ((y1:real^N) dot m1)) has_real_derivative f') (atreal s)`) THEN
    USE_THEN "der0" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP HAS_REAL_DERIVATIVE_SUB) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. drop((Fl:real^N->real^1)(Z0 + s % c)) -
                      (mm:real^N->real^N) Z0 dot (fy:real^N->real^N)(Z0 + s % c) -
                      s pow 2 / &2 * ((y1:real^N) dot m1)`;
                 `\s. frechet_derivative (fy:real^N->real^N) (at (Z0 + s % c)) c dot
                      ((mm:real^N->real^N)(Z0 + s % c) - mm Z0) - s * ((y1:real^N) dot m1)`;
                 `real_interval[&0,t]`; `e * t`] REAL_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      USE_THEN "der" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "pts" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN
     `frechet_derivative (fy:real^N->real^N) (at (Z0 + s % c)) c dot
      ((mm:real^N->real^N)(Z0 + s % c) - mm Z0) - s * ((y1:real^N) dot m1) =
      (frechet_derivative fy (at (Z0 + s % c)) c - y1) dot (mm(Z0 + s % c) - mm Z0) +
      y1 dot (mm(Z0 + s % c) - mm Z0 - s % m1)` SUBST1_TAC THENL
     [REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_RMUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `abs a <= e / &2 * t /\ abs b <= e / &2 * t ==> abs(a + b) <= e * t`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(frechet_derivative (fy:real^N->real^N) (at (Z0 + s % c)) c - y1) *
                  norm((mm:real^N->real^N)(Z0 + s % c) - mm Z0)` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `e / &2 / (Lt * norm(c:real^N) + &1) * (Lt * (t * norm(c:real^N)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[GSYM dist] THEN
          USE_THEN "cont" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Lt * norm((Z0 + s % c) - Z0:real^N)` THEN
          CONJ_TAC THENL
           [USE_THEN "lip" MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN
            ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM dist] THEN
            MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < Lt * norm(c:real^N) + &1` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `e / &2 / (Lt * norm(c:real^N) + &1) * (Lt * (t * norm c)) =
                    (e / &2 * t) * ((Lt * norm c) / (Lt * norm c + &1))` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < Lt * norm(c:real^N) + &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `s = &0` THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_SUB_REFL; DOT_RZERO;
                      REAL_ABS_0] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(y1:real^N) * norm((mm:real^N->real^N)(Z0 + s % c) - mm Z0 - s % m1)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(y1:real^N) * (e / &2 / (norm y1 + &1) * t)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2 / (norm(y1:real^N) + &1) * s` THEN
      CONJ_TAC THENL
       [USE_THEN "dm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN MP_TAC(ISPEC `y1:real^N` NORM_POS_LE) THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(y1:real^N) * (e / &2 / (norm y1 + &1) * t) =
                  (e / &2 * t) * (norm y1 / (norm y1 + &1))` SUBST1_TAC THENL
     [MP_TAC(ISPEC `y1:real^N` NORM_POS_LE) THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(y1:real^N) + &1` ASSUME_TAC THENL
     [MP_TAC(ISPEC `y1:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `&0`]) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_SUB_RZERO; DOT_RSUB] THEN
  REWRITE_TAC[REAL_ARITH `(&0) pow 2 / &2 * x = &0`] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y /\ b = c ==> abs x <= b ==> abs y <= c`) THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
                  REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC]]);;

let P2AL_TRACE_QF_POS = prove
 (`!G M:real^N^N.
     positive_definite G /\ (!w. &0 <= w dot (M ** w))
     ==> &0 <= trace(matrix_inv G ** M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `positive_semidefinite(matrix_inv(G:real^N^N))` MP_TAC THENL
   [MATCH_MP_TAC POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE THEN
    ASM_REWRITE_TAC[POSITIVE_DEFINITE_INV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [POSITIVE_SEMIDEFINITE_SQRT_EQ]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[symmetric_matrix] o
              MATCH_MP POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC_MATRIX) THEN
  SUBGOAL_THEN `trace(((Q:real^N^N) ** Q) ** (M:real^N^N)) = trace(Q ** M ** Q)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `((Q:real^N^N) ** (M:real^N^N) ** Q)$i$i =
                basis i dot ((Q ** M ** Q) ** basis i)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM DOT_LMUL_MATRIX] THEN
  ASM_REWRITE_TAC[VECTOR_MATRIX_MUL_TRANSP]);;

(* ========================================================================= *)
(* Second order at a slice minimum.  The L-geodesics of Z + tc end in O     *)
(* for small t, so Ltil(Z + tc) >= Ltil(Z); with the end velocity zero,     *)
(* P2AL_CHI2 gives (Y c) . (G B c) >= 0 at the end (P2AL_END_K0).           *)
(* ========================================================================= *)

let P2AL_END_K0 = prove
 (`!(V:p2alv) tt (x:A) Z O sb b'' sw r W a' b' U (phi:A->real^N) N Phi c.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b'' /\ &0 < sb /\ sb pow 2 < b'' /\
     open_in (p2a_vtop V (tt - sb pow 2)) O /\ p2a_Lexp V tt x (sb pow 2) Z IN O /\
     (!g'. p2a_adm V tt x (sb pow 2) g' /\ g' (sb pow 2) IN O
           ==> p2a_Ltil V tt x (sb pow 2) Z <= p2a_L_length V tt g' (sb pow 2)) /\
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\ sw < sb /\ sb < sw + r /\
     p2al_lin V tt sw r W b' U phi Phi Z sb /\ sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb) = vec 0
     ==> &0 <= (p2al_jy V tt sw r W b' U phi Phi Z sb ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))) ** (p2al_jb V tt sw r W b' U phi Phi Z sb ** c))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "SLM") STRIP_ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi /\ &0 <= sw`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ p2a_region (V:p2alv) W a' b' /\ (U,phi:A->real^N) IN p2a_vatlas V b'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_lwa]; ALL_TAC] THEN
  SUBGOAL_THEN `a' < tt - sb pow 2 /\ tt - sb pow 2 < b'` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2AL_WIN_TIME THEN
    MAP_EVERY EXISTS_TAC [`V:p2alv`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `U:A->bool`;
                          `phi:A->real^N`; `N:real^N->bool`;
                          `Phi:real^N->real^(N,N)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b'':real`; `sw:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_SLICE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FV")))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) =
    p2a_Lexp V tt x (sb pow 2) Z` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lexp")) (concl th))) THEN
    MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:p2alv`; `a':real`; `b':real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - sb pow 2`; `O:A->bool`; `fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)`]
                P2A_CHART_INV_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rO:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NB"))) THEN
  SUBGOAL_THEN
   `frechet_derivative (\Z. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) (at Z) c = p2al_jy (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb ** c /\
    frechet_derivative (\Z. (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))
      (at Z) c = ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))) ** (p2al_jb V tt sw r W b' U phi Phi Z sb ** c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_LFL_HASDER_YB) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_HASDER_CARTS) THEN
      REWRITE_TAC[FSTCART_PASTECART] THEN
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o BETA_RULE) THEN
      REWRITE_TAC[];
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_M_HASDER) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; VECTOR_ADD_LID]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `K0 = (p2al_jy (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))) ** (p2al_jb V tt sw r W b' U phi Phi Z sb ** c))` THEN
  MP_TAC(ISPECL
   [`{Z' | Z' IN N /\ p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z' sb /\
           Z' IN p2a_Ldom V tt (x:A) b''}`;
    `\Z:real^N. lift(p2a_Ltil (V:p2alv) tt (x:A) (sb pow 2) Z)`;
    `\Z. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)`;
    `\Z. (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)`;
    `Z:real^N`; `c:real^N`] P2AL_CHI2) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `--K0 / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CHI"))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `Z:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "open"))
                         (concl th) &&
                     can (find_term ((=) `b'':real`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(\Z. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) continuous (at Z)` MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{Z' | Z' IN N /\ p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z' sb /\
                      Z' IN p2a_Ldom V tt (x:A) b''}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `rO:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d5:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(c:real^N) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = min d1 (min d4 d5 / (norm(c:real^N) + &1)) / &2` THEN
  SUBGOAL_THEN `&0 < t /\ t < d1 /\ t * (norm(c:real^N) + &1) < min d4 d5` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < min d4 d5 / (norm(c:real^N) + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
    SUBGOAL_THEN `t < min d4 d5 / (norm(c:real^N) + &1)` MP_TAC THENL
     [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(Z + t % c,Z:real^N) < min d4 d5` ASSUME_TAC THENL
   [REWRITE_TAC[dist; VECTOR_ARITH `(a + b) - a:real^N = b`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `t * (norm(c:real^N) + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Z + t % c IN N /\ p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + t % c) sb /\
    Z + t % c IN p2a_Ldom V tt (x:A) b''`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(Z:real^N,d4) SUBSET
                 {Z' | Z' IN N /\ p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z' sb /\
                       Z' IN p2a_Ldom V tt (x:A) b''}` THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z + t % c:real^N`; `sb:real`] P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `p2a_Lexp (V:p2alv) tt (x:A) (sb pow 2) (Z + t % c) IN O` ASSUME_TAC THENL
   [USE_THEN "NB" (MP_TAC o SPEC `fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + t % c) sb)`) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `Z + t % c:real^N` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d5:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + t % c) sb)) =
      p2a_Lexp V tt x (sb pow 2) (Z + t % c)`
     (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `Z + t % c:real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lexp")) (concl th))) THEN
    MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:p2alv`; `a':real`; `b':real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "SLM" (MP_TAC o SPEC `p2a_Lgeo (V:p2alv) tt (x:A) (Z + t % c) (sb pow 2)`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P2AL_LGEO_ADM] THEN ASM_REWRITE_TAC[GSYM p2a_Lexp]; ALL_TAC] THEN
  REWRITE_TAC[GSYM p2a_Ltil] THEN
  USE_THEN "CHI" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t pow 2` MP_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `K0 < &0` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`t pow 2`,`T2:real`) THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < --K0 * T2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* At a slice minimum with invertible Y at the end: the end velocity is 0   *)
(* and H(sb) >= 0, i.e. n sb - sb^3 R - L/2 >= 0 (Riccati comparison of     *)
(* pc_p2a_lmono and the trace of (Y c).(G B c) >= 0).                        *)

let P2AL_END_H = prove
 (`!(V:p2alv) tt (x:A) Z O sb b'' sw r W a' b' U (phi:A->real^N) N Phi.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Smin V tt x (sb pow 2) /\ Z IN p2a_Ldom V tt x b'' /\ &0 < sb /\
     sb pow 2 < b'' /\
     open_in (p2a_vtop V (tt - sb pow 2)) O /\ p2a_Lexp V tt x (sb pow 2) Z IN O /\
     (!g'. p2a_adm V tt x (sb pow 2) g' /\ g' (sb pow 2) IN O
           ==> p2a_Ltil V tt x (sb pow 2) Z <= p2a_L_length V tt g' (sb pow 2)) /\
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\ sw < sb /\ sb < sw + r /\
     p2al_lin V tt sw r W b' U phi Phi Z sb /\ ~(det(p2al_jy V tt sw r W b' U phi Phi Z sb) = &0)
     ==> sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb) = vec 0 /\
         &0 <= &(dimindex(:N)) * sb -
               sb pow 3 * lscalar ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2)) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) -
               p2a_Ltil V tt x (sb pow 2) Z / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) (sb pow 2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_Smin; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `O:A->bool`; `sb:real`; `sw:real`;
                 `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`] P2AL_END_VEL0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) (U INTER W)) ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow")) (concl th))) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. &0 <= w dot ((((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb))) ** p2al_jb V tt sw r W b' U phi Phi Z sb ** matrix_inv(p2al_jy V tt sw r W b' U phi Phi Z sb)) ** w)` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `O:A->bool`; `sb:real`; `b'':real`;
                   `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                   `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`;
                   `matrix_inv(p2al_jy (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb) ** (w:real^N)`] P2AL_END_K0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `p2al_jy (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb ** matrix_inv(p2al_jy V tt sw r W b' U phi Phi Z sb) ** (w:real^N) = w` SUBST1_TAC THENL
     [REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `p2al_jy (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb ** matrix_inv(p2al_jy V tt sw r W b' U phi Phi Z sb) = mat 1` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[MATRIX_INV_RIGHT; INVERTIBLE_DET_NZ]; REWRITE_TAC[MATRIX_VECTOR_MUL_LID]];
      ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)))`; `((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb))) ** p2al_jb V tt sw r W b' U phi Phi Z sb ** matrix_inv(p2al_jy V tt sw r W b' U phi Phi Z sb)`] P2AL_TRACE_QF_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AL_METRIC_PD THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)))` ASSUME_TAC THENL
   [MATCH_MP_TAC POSITIVE_DEFINITE_IMP_INVERTIBLE THEN MATCH_MP_TAC P2AL_METRIC_PD THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_LID] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b'':real`; `Z:real^N`; `sb:real`]
                P2AL_GF_NONPOS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s:real = sb` THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_RVI_POS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC P2AL_NO_CONJ THEN EXISTS_TAC `sb pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `sb:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b'':real`; `sw:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_GF_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[p2al_gw] THEN ASM_REWRITE_TAC[DOT_LZERO; REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `p2al_tg ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2)) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) (vec 0) = &0`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `(p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2)`;
                   `fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)`] P2AL_TG_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN
  MP_TAC(SPEC `sb:real` REAL_LE_POW_2) THEN
  UNDISCH_TAC `&0 <= trace(p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb ** matrix_inv(p2al_jy V tt sw r W b' U phi Phi Z sb))` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`trace(p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb ** matrix_inv(p2al_jy V tt sw r W b' U phi Phi Z sb))`,`T0:real`) THEN
  SPEC_TAC(`sb pow 2`,`S2:real`) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= S2 * T0` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* A slice minimum is not conjugate to x along gamma_Z.  If Y(sb) c = 0     *)
(* with u = B(sb) c <> 0, the curve gamma_{Z + eps c} up to sa^2            *)
(* followed by a chart piece that bends the end point by -t u ends in O and *)
(* is shorter for t = kappa eps (P2AL_CORE_NEG_END, the one-piece version   *)
(* of P2AL_CORE_NEG; the end velocity is zero).                             *)
(* ========================================================================= *)

let P2AL_CORE_NEG_END = prove
 (`!(V:p2alv) tt (x:A) b sw r W a' b' U (phi:A->real^N) N Phi Z c sa sz rO.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\ Z IN p2a_Ldom V tt x b /\
     sw < sa /\ sa < sz /\ sz < sw + r /\ sz pow 2 < b /\
     (!s. sa <= s /\ s <= sz ==> p2al_lin V tt sw r W b' U phi Phi Z s) /\
     p2al_jy V tt sw r W b' U phi Phi Z sz ** c = vec 0 /\
     ~(p2al_jb V tt sw r W b' U phi Phi Z sz ** c = vec 0) /\
     sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz) = vec 0 /\ &0 < rO
     ==> ?eps t.
           &0 < eps /\
           (!s. sa <= s /\ s <= sz
                ==> Z + eps % c IN N /\ p2al_lin V tt sw r W b' U phi Phi (Z + eps % c) s) /\
           (!s. sa <= s /\ s <= sz
                ==> fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) s) + ((t / (sz - sa)) * (sa - s)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)
                    IN IMAGE phi (U INTER W)) /\
           dist(fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) + ((t / (sz - sa)) * (sa - sz)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c),
                fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) < rO /\
           (p2a_Ltil V tt x (sz pow 2) (Z + eps % c) - p2a_Ltil V tt x (sz pow 2) Z) +
           (p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) (drop v)) + ((t / (sz - sa)) * (sa - drop v)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)) sa sz - p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) (drop v))) sa sz) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi /\ &0 < r`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok; p2al_lwa]; ALL_TAC] THEN
  SUBGOAL_THEN `p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `sw:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `c:real^N`; `sz:real`]
                P2AL_CORE_EST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CHI") (CONJUNCTS_THEN2 (LABEL_TAC "MM")
    (LABEL_TAC "DEL"))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_WOK_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) (U INTER W)) ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sz pow 2))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow")) (concl th))) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) ** (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field (IMAGE (phi:A->real^N) (U INTER W)) ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sz pow 2))` THEN
    REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz)` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`;
                 `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sa:real`; `sz:real`]
                P2AL_WIN_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rz:real` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `K:real^(1,(N,N)finite_sum)finite_sum->bool` (X_CHOOSE_THEN `B:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TUBE") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TAY") (LABEL_TAC "SEG"))))))))))) THEN
  MP_TAC(ISPECL [`(p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) ** (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))`;
                 `B * (norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))) pow 2 * (sz - sa)`;
                 `&0`; `norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)`] P2AL_NEG_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LE; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa:real` (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `e2:real`
    (X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NEG"))))))))) THEN
  REMOVE_THEN "CHI" (MP_TAC o SPEC `e1:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CHI1"))) THEN
  REMOVE_THEN "MM" (MP_TAC o SPEC `e2:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MM1"))) THEN
  REMOVE_THEN "DEL" (MP_TAC o SPEC `e3:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DEL1"))) THEN
  SUBGOAL_THEN `&0 < &1 + inv(sz - sa)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < &1 + x`) THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa)) /\
                &0 <= e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `eps = min (min (min d1 d2) (min d3 (rz / (norm(c:real^N) + &1))))
                        (min (rho / (kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa)) + &1))
                             (rO / ((e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) + &1))) / &2` THEN
  SUBGOAL_THEN
   `&0 < eps /\ eps < d1 /\ eps < d2 /\ eps < d3 /\ eps < rz / (norm(c:real^N) + &1) /\
    eps < rho / (kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa)) + &1) /\
    eps < rO / ((e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) + &1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rz / (norm(c:real^N) + &1) /\
                  &0 < rho / (kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa)) + &1) /\
                  &0 < rO / ((e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) + &1)`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `c:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Z + eps % c IN cball(Z:real^N,rz)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL; dist; VECTOR_ARITH `a - (a + b):real^N = --b`; NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `eps * (norm(c:real^N) + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= n ==> &0 < n + &1`; NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps * (kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))) <= rho /\
                eps * ((e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) + &1) < rO`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2AL_DIV_BOUND THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= n ==> &0 < n + &1`]];
    ALL_TAC] THEN
  EXISTS_TAC `eps:real` THEN EXISTS_TAC `kappa * eps` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "TUBE" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= kappa * eps * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sa:real`; `sz:real`;
                 `rz:real`; `rho:real`; `K:real^(1,(N,N)finite_sum)finite_sum->bool`; `B:real`;
                 `Z + eps % c:real^N`; `(kappa * eps) / (sz - sa)`; `sa:real`; `(p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)`;
                 `sa:real`; `sz:real`; `kappa * eps * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))`]
                P2AL_CTL_WIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(kappa * eps) / (sz - sa)`; `sa:real`; `(p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)`; `sa:real`; `sz:real`;
                   `s:real`] P2AL_AFF_NORM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(kappa * eps) / (sz - sa) * (sz - sa) * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) +
                  (kappa * eps) / (sz - sa) * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) =
                  kappa * eps * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(sz - sa = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `eps * kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa)) <= rho` THEN
    UNDISCH_TAC `norm(pastecart (((kappa * eps) / (sz - sa) * (sa - s)) % (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c))
                                (--((kappa * eps) / (sz - sa)) % (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c))) <=
                 kappa * eps * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "MEM1") (LABEL_TAC "CTL1")) THEN
  SUBGOAL_THEN `norm (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) <= e3 * eps` ASSUME_TAC THENL
   [USE_THEN "DEL1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(kappa * eps) / (sz - sa) * (sa - sz) = --(kappa * eps)` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(sz - sa = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[dist] THEN
    REWRITE_TAC[VECTOR_ARITH `(a + b) - c:real^N = (a - c) + b`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) + norm(--(kappa * eps) % (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c))` THEN
    REWRITE_TAC[NORM_TRIANGLE] THEN REWRITE_TAC[NORM_MUL; REAL_ABS_NEG; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `eps * ((e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) + &1) < rO` THEN
    UNDISCH_TAC `norm (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) <= e3 * eps` THEN UNDISCH_TAC `&0 < eps` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(p2a_Ltil (V:p2alv) tt (x:A) (sz pow 2) (Z + eps % c) - p2a_Ltil V tt x (sz pow 2) Z -
        ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) dot (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) <= e1 * eps pow 2`
  ASSUME_TAC THENL [USE_THEN "CHI1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) - ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) - eps * ((p2al_jb V tt sw r W b' U phi Phi Z sz ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) ** (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)))) <= norm (p2al_jb V tt sw r W b' U phi Phi Z sz ** c) * e2 * eps`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DOT_RMUL; GSYM DOT_RSUB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * norm (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) - ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - eps % (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) ** (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)))` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    USE_THEN "MM1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "CTL1" (MP_TAC o ONCE_REWRITE_RULE[REAL_RING
    `B * (kappa * eps * n * l) pow 2 * d = (B * (n * l) pow 2 * d) * (kappa * eps) pow 2`]) THEN
  DISCH_THEN(LABEL_TAC "CTL1B") THEN
  USE_THEN "CTL1B" (fun c1 ->
    let r1 = rand(lhand(concl c1)) in
    USE_THEN "NEG" (MP_TAC o SPECL [`eps:real`;
      `p2a_Ltil (V:p2alv) tt (x:A) (sz pow 2) (Z + eps % c) - p2a_Ltil V tt x (sz pow 2) Z -
       ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) dot (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))`;
      `(p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) - ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)))`; r1; `&0`; `&0`])) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ABS_0; REAL_MUL_LZERO] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> y < &0 ==> x < &0`) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; DOT_LZERO;
                  MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; DOT_LNEG; DOT_LMUL; DOT_RSUB] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* At a slice minimum the end point is not conjugate: det Y(sz) <> 0 at the *)
(* end time sz (P2AL_END_NOCONJ), by the competitor of P2AL_CORE_NEG_END    *)
(* glued to the L-geodesic of Z + eps c.                                    *)
(* ========================================================================= *)

let P2AL_END_NOCONJ = prove
 (`!(V:p2alv) tt (x:A) Z O sz b'' sw r W a' b' U (phi:A->real^N) N Phi.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Smin V tt x (sz pow 2) /\ Z IN p2a_Ldom V tt x b'' /\ &0 < sz /\
     sz pow 2 < b'' /\
     open_in (p2a_vtop V (tt - sz pow 2)) O /\ p2a_Lexp V tt x (sz pow 2) Z IN O /\
     (!g'. p2a_adm V tt x (sz pow 2) g' /\ g' (sz pow 2) IN O
           ==> p2a_Ltil V tt x (sz pow 2) Z <= p2a_L_length V tt g' (sz pow 2)) /\
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\ sw < sz /\ sz < sw + r /\
     p2al_lin V tt sw r W b' U phi Phi Z sz
     ==> ~(det(p2al_jy V tt sw r W b' U phi Phi Z sz) = &0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "SLM") STRIP_ASSUME_TAC)))))))))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) (sz pow 2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_Smin; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `O:A->bool`; `sz:real`; `sw:real`;
                 `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`] P2AL_END_VEL0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi /\ &0 <= sw`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ p2a_region (V:p2alv) W a' b' /\ (U,phi:A->real^N) IN p2a_vatlas V b'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_lwa]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. sw < s /\ s < sw + r ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'`
  (LABEL_TAC "TIME") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AL_WIN_TIME THEN
    MAP_EVERY EXISTS_TAC [`V:p2alv`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `U:A->bool`;
                          `phi:A->real^N`; `N:real^N->bool`;
                          `Phi:real^N->real^(N,N)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p2al_jy (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz`
               HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E")) o
             last o CONJUNCTS) THEN
  SUBGOAL_THEN `~(p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c = vec 0)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`; `c:real^N`]
                  P2AL_JAC_KERNEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ker") THEN
    ABBREV_TAC `sq = max ((sw + sz) / &2) (sz - e / &2)` THEN
    SUBGOAL_THEN `sw < sq /\ sq < sz /\ abs(sq - sz) < e /\ &0 < sq` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "sq" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "E" (MP_TAC o SPEC `sq:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REMOVE_THEN "ker" (MP_TAC o SPEC `sq:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sq:real`] P2AL_WOK_J_ZERO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p /\ q ==> (p <=> q) ==> F`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < j ==> ~(j = &0)`) THEN MATCH_MP_TAC P2AL_NO_CONJ THEN
      EXISTS_TAC `sz pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
      EXISTS_TAC `c:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `sa = sz - min (e / &2) ((sz - sw) / &2)` THEN
  SUBGOAL_THEN `sw < sa /\ sa < sz /\ &0 < sa` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. sa <= s /\ s <= sz ==> p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s`
  (LABEL_TAC "LIN") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "E" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz)) =
    p2a_Lexp V tt x (sz pow 2) Z` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lexp")) (concl th))) THEN
    MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:p2alv`; `a':real`; `b':real`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "TIME" (MP_TAC o SPEC `sz:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - sz pow 2`; `O:A->bool`; `fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz)`]
                P2A_CHART_INV_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "TIME" (MP_TAC o SPEC `sz:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rO:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NB"))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b'':real`; `sw:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `c:real^N`; `sa:real`;
                 `sz:real`; `rO:real`] P2AL_CORE_NEG_END) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` (X_CHOOSE_THEN `t:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "LINE")
    (CONJUNCTS_THEN2 (LABEL_TAC "M1") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NEG"))))))) THEN
  SUBGOAL_THEN `a' < b'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "LINE" (MP_TAC o SPEC `sa:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z + eps % c:real^N`; `sa:real`]
                P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `(\v. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) (drop v)) + ((t / (sz - sa)) * (sa - drop v)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))`; `sa:real`; `sz:real`; `sw:real`; `sw + r`]
                P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "M1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "LINE" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC P2AL_FLOW_AFF_CURVE THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `N:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[LIFT_DROP]) THEN
  SUBGOAL_THEN `&0 <= sz /\ &0 <= sa /\ &0 < sa pow 2 /\ sa pow 2 < sz pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_Lgeo (V:p2alv) tt (x:A) (Z + eps % c) (sa pow 2) (sa pow 2) = (\tau. chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) (sqrt tau)) + ((t / (sz - sa)) * (sa - sqrt tau)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))) (sa pow 2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(sa pow 2) = sa` SUBST1_TAC THENL [ASM_SIMP_TAC[POW_2_SQRT]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `sa pow 2`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lexp")) (concl th))) THEN
    MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                   `phi:A->real^N`;
                   `p2a_Lexp (V:p2alv) tt (x:A) (sa pow 2) (Z + eps % c)`]
                  P2A_REGION_CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p2a_Lexp];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `(\tau. chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) (sqrt tau)) + ((t / (sz - sa)) * (sa - sqrt tau)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)))`;
                 `p2a_Lgeo (V:p2alv) tt (x:A) (Z + eps % c) (sa pow 2)`;
                 `\u. if u <= sa pow 2 then p2a_Lgeo (V:p2alv) tt (x:A) (Z + eps % c) (sa pow 2) u
                      else (\tau. chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) (sqrt tau)) + ((t / (sz - sa)) * (sa - sqrt tau)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))) u`;
                 `sz pow 2`; `sa pow 2`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AL_LGEO_ADM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[REAL_LE_ANTISYM];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `chart_inv (U INTER W,phi:A->real^N)
      (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) + ((t / (sz - sa)) * (sa - sz)) % (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) IN O`
  ASSUME_TAC THENL
   [USE_THEN "NB" (MP_TAC o SPEC
      `fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) + ((t / (sz - sa)) * (sa - sz)) % (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "SLM" (MP_TAC o SPEC
    `\u. if u <= sa pow 2 then p2a_Lgeo (V:p2alv) tt (x:A) (Z + eps % c) (sa pow 2) u
         else (\tau. chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) (sqrt tau)) + ((t / (sz - sa)) * (sa - sqrt tau)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))) u`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(sz pow 2 <= sa pow 2)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(sz pow 2) = sz` SUBST1_TAC THENL [ASM_SIMP_TAC[POW_2_SQRT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p2a_L_length (V:p2alv) tt (p2a_Lgeo V tt (x:A) (Z + eps % c) (sa pow 2))
                  (sa pow 2) = p2a_Ltil V tt x (sa pow 2) (Z + eps % c)` SUBST1_TAC THENL
   [REWRITE_TAC[p2a_Ltil]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> SUBST1_TAC(MATCH_MP REAL_INTEGRAL_UNIQUE th)) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z + eps % c:real^N`; `sa:real`; `sz:real`]
                P2AL_LTIL_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "LINE" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "NEG" MP_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The constant continuation of a chart curve.  If y has a continuous       *)
(* derivative y' near sb and y'(sb) = 0, the curve in tau that follows      *)
(* y(sqrt tau) up to sb^2 and stays at y(sb) afterwards has a two-sided     *)
(* continuous derivative near sb^2.                                         *)
(* ========================================================================= *)

(* One-sided derivatives and continuity glue over a union of sets (vector  *)
(* derivative form of GRGD_HAS_DERIVATIVE_WITHIN_UNION).                    *)

let P2AL_HASVD_UNION = prove
 (`!(f:real^1->real^N) f' x s t.
     (f has_vector_derivative f') (at x within s) /\
     (f has_vector_derivative f') (at x within t)
     ==> (f has_vector_derivative f') (at x within (s UNION t))`,
  SIMP_TAC[has_vector_derivative; GRGD_HAS_DERIVATIVE_WITHIN_UNION]);;

let P2AL_CONT_UNION = prove
 (`!(f:real^1->real^N) x s t.
     f continuous (at x within s) /\ f continuous (at x within t)
     ==> f continuous (at x within (s UNION t))`,
  SIMP_TAC[CONTINUOUS_WITHIN; LIM_WITHIN_UNION]);;

let P2AL_FREEZE_C1 = prove
 (`!(y:real^1->real^N) y' sL sR sb.
     &0 <= sL /\ sL < sb /\ sb < sR /\ y'(lift sb) = vec 0 /\
     (!s. sL < s /\ s < sR
          ==> (y has_vector_derivative y'(lift s)) (at (lift s)) /\
              y' continuous (at (lift s)))
     ==> !tau. sL pow 2 < tau /\ tau < sR pow 2
               ==> ((\v. if drop v <= sb pow 2 then y(lift(sqrt(drop v))) else y(lift sb))
                    has_vector_derivative
                    (if tau <= sb pow 2 then inv(&2 * sqrt tau) % y'(lift(sqrt tau))
                     else vec 0))
                   (at (lift tau)) /\
                   (\v. if drop v <= sb pow 2
                        then inv(&2 * sqrt(drop v)) % y'(lift(sqrt(drop v)))
                        else vec 0) continuous (at (lift tau))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Y"))))) THEN
  SUBGOAL_THEN `&0 < sb /\ sL pow 2 < sb pow 2 /\ sb pow 2 < sR pow 2 /\ sqrt(sb pow 2) = sb`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. sL pow 2 < u /\ u < sR pow 2 ==> &0 < u /\ sL < sqrt u /\ sqrt u < sR`
  (LABEL_TAC "SQ") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= sL pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`sL pow 2`; `u:real`] SQRT_MONO_LT) THEN
      ASM_SIMP_TAC[POW_2_SQRT];
      SUBGOAL_THEN `&0 <= sR` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`u:real`; `sR pow 2`] SQRT_MONO_LT) THEN
      ASM_SIMP_TAC[POW_2_SQRT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. sL pow 2 < u /\ u < sR pow 2
        ==> ((\v. (y:real^1->real^N)(lift(sqrt(drop v)))) has_vector_derivative
             inv(&2 * sqrt u) % (y':real^1->real^N)(lift(sqrt u))) (at (lift u)) /\
            (\v. inv(&2 * sqrt(drop v)) % (y':real^1->real^N)(lift(sqrt(drop v))))
              continuous (at (lift u))`
  (LABEL_TAC "F") THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    USE_THEN "SQ" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "Y" (MP_TAC o SPEC `sqrt u`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`\v:real^1. lift(sqrt(drop v))`; `y:real^1->real^N`;
                     `lift(inv(&2 * sqrt u))`; `(y':real^1->real^N)(lift(sqrt u))`;
                     `lift u`] VECTOR_DIFF_CHAIN_AT) THEN
      REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `u:real` HAS_REAL_DERIVATIVE_SQRT) THEN
      ASM_REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF];
      MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN
        MP_TAC(ISPECL [`atreal u`; `\x. &2 * sqrt x`] REAL_CONTINUOUS_INV) THEN
        REWRITE_TAC[NETLIMIT_ATREAL] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
            REWRITE_TAC[ETA_AX; REAL_CONTINUOUS_AT_SQRT];
            MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&2 * x = &0)`) THEN
            MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]];
          REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL; o_DEF; LIFT_DROP]];
        MP_TAC(ISPECL [`\v:real^1. lift(sqrt(drop v))`; `y':real^1->real^N`; `lift u`]
                      CONTINUOUS_AT_COMPOSE) THEN
        REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `lift u` CONTINUOUS_AT_SQRT) THEN REWRITE_TAC[o_DEF]]];
    ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  USE_THEN "F" (MP_TAC o SPEC `tau:real`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FD") (LABEL_TAC "FC"))] THEN
  ASM_CASES_TAC `tau < sb pow 2` THENL
   [SUBGOAL_THEN `tau <= sb pow 2` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
      EXISTS_TAC `\v. (y:real^1->real^N)(lift(sqrt(drop v)))` THEN
      EXISTS_TAC `sb pow 2 - tau` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
      X_GEN_TAC `w:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN SUBGOAL_THEN `drop w <= sb pow 2` (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
      EXISTS_TAC `\v. inv(&2 * sqrt(drop v)) % (y':real^1->real^N)(lift(sqrt(drop v)))` THEN
      EXISTS_TAC `sb pow 2 - tau` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
      X_GEN_TAC `w:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN SUBGOAL_THEN `drop w <= sb pow 2` (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `sb pow 2 < tau` THENL
   [SUBGOAL_THEN `~(tau <= sb pow 2)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
      EXISTS_TAC `\v:real^1. (y:real^1->real^N)(lift sb)` THEN
      EXISTS_TAC `tau - sb pow 2` THEN
      ASM_REWRITE_TAC[REAL_SUB_LT; HAS_VECTOR_DERIVATIVE_CONST] THEN
      X_GEN_TAC `w:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN SUBGOAL_THEN `~(drop w <= sb pow 2)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
      EXISTS_TAC `\v:real^1. (vec 0:real^N)` THEN
      EXISTS_TAC `tau - sb pow 2` THEN ASM_REWRITE_TAC[REAL_SUB_LT; CONTINUOUS_CONST] THEN
      X_GEN_TAC `w:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN SUBGOAL_THEN `~(drop w <= sb pow 2)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau = sb pow 2` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "FD" (MP_TAC o REWRITE_RULE[ASSUME `sqrt(sb pow 2) = sb`;
    ASSUME `(y':real^1->real^N)(lift sb) = vec 0`; VECTOR_MUL_RZERO]) THEN
  DISCH_TAC THEN
  REWRITE_TAC[REAL_LE_REFL; ASSUME `sqrt(sb pow 2) = sb`;
              ASSUME `(y':real^1->real^N)(lift sb) = vec 0`; VECTOR_MUL_RZERO] THEN
  SUBGOAL_THEN `(:real^1) = {v | drop v <= sb pow 2} UNION {v | sb pow 2 <= drop v}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_UNIV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(:real^1)`)) THEN
    MATCH_MP_TAC P2AL_HASVD_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
      EXISTS_TAC `\v. (y:real^1->real^N)(lift(sqrt(drop v)))` THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; LIFT_DROP; REAL_LE_REFL] THEN CONJ_TAC THENL
       [X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
      EXISTS_TAC `\v:real^1. (y:real^1->real^N)(lift sb)` THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; LIFT_DROP; REAL_LE_REFL;
                  HAS_VECTOR_DERIVATIVE_CONST] THEN
      X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN
      ASM_CASES_TAC `drop w <= sb pow 2` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `drop w = sb pow 2` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(:real^1)`)) THEN
    MATCH_MP_TAC P2AL_CONT_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
      EXISTS_TAC `\v. inv(&2 * sqrt(drop v)) % (y':real^1->real^N)(lift(sqrt(drop v)))` THEN
      EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; LIFT_DROP; REAL_LE_REFL] THEN CONJ_TAC THENL
       [X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
      EXISTS_TAC `\v:real^1. (vec 0:real^N)` THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; LIFT_DROP; REAL_LE_REFL; CONTINUOUS_CONST] THEN
      X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN
      ASM_CASES_TAC `drop w <= sb pow 2` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `drop w = sb pow 2` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[VECTOR_MUL_RZERO]]]]);;

(* ========================================================================= *)
(* A curve that is a C^1 chart curve of a region chart on [b1,b2] is C^1 in *)
(* every chart there (P2AL_CHART_C1S), hence corner-free on [b1,b2] with a  *)
(* C^1 start (P2AL_CHART_PC1).                                              *)
(* ========================================================================= *)

let P2AL_CHART_C1S = prove
 (`!(V:p2alv) tt W a' b'' U (phi:A->real^N) (Zs:real^1->real^N) Zs' (gamma:real->A) b1 b2.
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\ b1 < b2 /\
     (!tau. b1 <= tau /\ tau <= b2 ==> a' < tt - tau /\ tt - tau <= b'') /\
     (!tau. b1 <= tau /\ tau <= b2
            ==> Zs(lift tau) IN IMAGE phi (U INTER W) /\
                (Zs has_vector_derivative Zs'(lift tau)) (at (lift tau)) /\
                Zs' continuous (at (lift tau))) /\
     (!tau. b1 <= tau /\ tau <= b2 ==> gamma tau = chart_inv (U INTER W,phi) (Zs(lift tau)))
     ==> !S c. S SUBSET {s | b1 <= drop s /\ drop s <= b2 /\
                             c IN p2a_vatlas V (tt - drop s) /\ gamma(drop s) IN FST c}
               ==> continuously_differentiable 1 S (\s. SND c (gamma(drop s)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GEQ")))))) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!s. s IN S
        ==> b1 <= drop s /\ drop s <= b2 /\ c IN p2a_vatlas (V:p2alv) (tt - drop s) /\
            chart_inv (U INTER W,phi:A->real^N) ((Zs:real^1->real^N) s) IN FST c /\
            chart_inv (U INTER W,phi) (Zs s) = (gamma:real->A)(drop s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "GEQ" (MP_TAC o SPEC `drop s`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LIFT_DROP]] THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `Zs:real^1->real^N`; `Zs':real^1->real^N`; `b1:real`;
                 `b2:real`] P2A_CHART_CURVE_PC1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^1->bool`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC MFDM_CONTINUOUSLY_DIFFERENTIABLE_EQ THEN
  EXISTS_TAC `\s. SND (c:(A->bool)#(A->real^N))
                    (chart_inv (U INTER W,phi:A->real^N) ((Zs:real^1->real^N) s))` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  AP_TERM_TAC THEN ASM_MESON_TAC[]);;

let P2AL_CHART_PC1 = prove
 (`!(V:p2alv) tt W a' b'' U (phi:A->real^N) (Zs:real^1->real^N) Zs' (gamma:real->A) b1 b2.
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\ b1 < b2 /\
     (!tau. b1 <= tau /\ tau <= b2 ==> a' < tt - tau /\ tt - tau <= b'') /\
     (!tau. b1 <= tau /\ tau <= b2
            ==> Zs(lift tau) IN IMAGE phi (U INTER W) /\
                (Zs has_vector_derivative Zs'(lift tau)) (at (lift tau)) /\
                Zs' continuous (at (lift tau))) /\
     (!tau. b1 <= tau /\ tau <= b2 ==> gamma tau = chart_inv (U INTER W,phi) (Zs(lift tau)))
     ==> p2a_pc1 V tt gamma b1 b2 {} /\
         (!c. c IN p2a_vatlas V (tt - b1) /\ gamma b1 IN FST c
              ==> ?d. &0 < d /\
                      continuously_differentiable 1
                        {s | b1 <= drop s /\ drop s <= b1 + d /\ drop s <= b2 /\
                             p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - b1) /\
                             gamma(drop s) IN FST c}
                        (\s. SND c (gamma(drop s))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "C1" o MATCH_MP P2AL_CHART_C1S) THEN
  REWRITE_TAC[p2a_pc1; FINITE_EMPTY; NOT_IN_EMPTY] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT CONJ_TAC THEN
    USE_THEN "C1" MATCH_MP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN STRIP_TAC THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    USE_THEN "C1" MATCH_MP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The difference quotient arithmetic (P2AL_BAR_ARITH) and the first-order  *)
(* bound on the L-length of a constant chart curve (P2AL_CONST_CL).         *)
(* ========================================================================= *)

(* With l = L / sb: from C <= (2 sb^2 R + e sb^2)(s2 - sb) and the end bound *)
(* n sb - sb^3 R - L/2 >= 0, the quotient of (L + C) / (2 s2) is controlled. *)

let P2AL_BAR_ARITH = prove
 (`!n sb s2 l R C e.
     &0 < sb /\ sb < s2 /\ s2 <= sb + &1 /\ &0 < e /\
     (s2 - sb) * (abs(n - l) * (&3 * sb + &1) + &1) <= &3 * e * sb pow 4 /\
     C <= (&2 * sb pow 2 * R + e * sb pow 2) * (s2 - sb) /\
     &0 <= n * sb - sb pow 3 * R - (sb * l) / &2
     ==> ((sb * l) + C) / (&2 * s2) - (sb * l) / (&2 * sb) <=
         ((n / &2 - (sb * l) / (&2 * sb)) / sb pow 2 + e) * (s2 pow 2 - sb pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s2 /\ &0 < s2 - sb /\ &0 < &2 * s2 * sb pow 2` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((sb * l) + C) / (&2 * s2) - (sb * l) / (&2 * sb) =
    (sb pow 2 * C - sb pow 2 * l * (s2 - sb)) / (&2 * s2 * sb pow 2) /\
    ((n / &2 - (sb * l) / (&2 * sb)) / sb pow 2 + e) * (s2 pow 2 - sb pow 2) =
    (s2 * (s2 + sb) * (n - l + &2 * e * sb pow 2) * (s2 - sb)) / (&2 * s2 * sb pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN `~(sb = &0) /\ ~(s2 = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  SUBGOAL_THEN `sb pow 2 * C <= sb pow 2 * ((&2 * sb pow 2 * R + e * sb pow 2) * (s2 - sb))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 * sb * (s2 - sb)) * (n * sb - sb pow 3 * R - (sb * l) / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (s2 - sb) pow 2 * (s2 + &2 * sb) * ((n - l) + abs(n - l))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s2 - sb) pow 2 * (s2 + &2 * sb) * abs(n - l) <=
                (s2 - sb) pow 2 * (&3 * sb + &1) * abs(n - l)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s2 - sb) * ((s2 - sb) * (abs(n - l) * (&3 * sb + &1) + &1)) <=
                (s2 - sb) * (&3 * e * sb pow 4)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * e * sb pow 2 * (s2 - sb) pow 2 * (s2 + &2 * sb)`
  ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (s2 - sb) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The L-length of the constant chart curve at the end point, from sb to    *)
(* s2, is at most (2 sb^2 R + eta)(s2 - sb) for s2 near sb.                 *)
(* ========================================================================= *)

let P2AL_CONST_CL = prove
 (`!(V:p2alv) tt (x:A) sw r W a' b' U (phi:A->real^N) N Phi Z sb.
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\ sw < sb /\ sb < sw + r /\
     p2al_lin V tt sw r W b' U phi Phi Z sb
     ==> !eta. &0 < eta
               ==> ?d. &0 < d /\
                       !s2. sb < s2 /\ s2 < sb + d
                            ==> p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt (\v. (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))) sb s2 <=
                                (&2 * sb pow 2 * lscalar ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sb pow 2)) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) + eta) * (s2 - sb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok; p2al_lwa]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. sw < s /\ s < sw + r ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'`
  (LABEL_TAC "TIME") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AL_WIN_TIME THEN
    MAP_EVERY EXISTS_TAC [`V:p2alv`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `U:A->bool`;
                          `phi:A->real^N`; `N:real^N->bool`;
                          `Phi:real^N->real^(N,N)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. sw < s /\ s < sw + r
        ==> (\s. &2 * s pow 2 * lscalar ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - s pow 2)) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb))) real_continuous
            atreal s`
  (LABEL_TAC "CONT") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_POW THEN REWRITE_TAC[REAL_CONTINUOUS_AT_ID];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `a':real`; `b':real`; `(p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N))`;
                   `sw - r`; `sw + r`; `tt:real`; `s:real`; `\v:real^1. (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb))`;
                   `vec 0:real^N`] P2AL_SCALAR_CURVE) THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "TIME" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      MESON_TAC[]];
    ALL_TAC] THEN
  USE_THEN "CONT" (MP_TAC o SPEC `sb:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_continuous_atreal] THEN
  DISCH_THEN(MP_TAC o SPEC `eta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  EXISTS_TAC `min d1 ((sw + r) - sb)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s2:real` THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_cL; VECTOR_DERIVATIVE_CONST_AT; p2a_llag; MATRIX_VECTOR_MUL_RZERO;
              DOT_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[sb,s2])
                (\s:real. &2 * sb pow 2 * lscalar ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2)) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) + eta)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      USE_THEN "CONT" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      USE_THEN "D1" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE; REAL_LE_REFL]]);;

(* ========================================================================= *)
(* The constant extension of gamma at its end point q = gamma(sb^2): it     *)
(* is admissible with L-length L + cL(constant) (P2AL_CONST_ADM) and,       *)
(* when the end velocity vanishes, corner-free (P2AL_CONST_PC1).            *)
(* ========================================================================= *)

let P2AL_SQRT_WIN = prove
 (`!a b tau. &0 <= a /\ &0 <= b /\ a pow 2 < tau /\ tau < b pow 2
             ==> &0 < tau /\ a < sqrt tau /\ sqrt tau < b /\ sqrt tau pow 2 = tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
   [MP_TAC(SPEC `a:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`a pow 2`; `tau:real`] SQRT_MONO_LT) THEN ASM_SIMP_TAC[POW_2_SQRT];
    MP_TAC(SPECL [`tau:real`; `b pow 2`] SQRT_MONO_LT) THEN ASM_SIMP_TAC[POW_2_SQRT];
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC]);;

let P2AL_CONST_ADM = prove
 (`!(V:p2alv) tt (x:A) gamma Z sb sw r W a' b' U (phi:A->real^N) N Phi s2.
     p2a_svs V /\ p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\
     sw < sb /\ sb < s2 /\ s2 < sw + r /\ p2al_lin V tt sw r W b' U phi Phi Z sb /\
     p2a_adm V tt x (sb pow 2) gamma /\
     (!tau. &0 <= tau /\ tau <= sb pow 2 ==> gamma tau = p2a_Lgeo V tt x Z (sb pow 2) tau)
     ==> chart_inv (U INTER W,phi) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) = gamma(sb pow 2) /\
         p2a_adm V tt x (s2 pow 2) (\tau. if tau <= sb pow 2 then (gamma:real->A) tau else gamma(sb pow 2)) /\
         (\tau. if tau <= sb pow 2 then (gamma:real->A) tau else gamma(sb pow 2)) (s2 pow 2) = gamma(sb pow 2) /\
         p2a_L_length V tt (\tau. if tau <= sb pow 2 then (gamma:real->A) tau else gamma(sb pow 2)) (s2 pow 2) =
         p2a_L_length V tt gamma (sb pow 2) + p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt (\v. (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))) sb s2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GEQ"))))))))) THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi /\ &0 <= sw`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ p2a_region (V:p2alv) W a' b' /\ (U,phi:A->real^N) IN p2a_vatlas V b'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_lwa]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. sw < s /\ s < sw + r ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'`
  (LABEL_TAC "TIME") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AL_WIN_TIME THEN
    MAP_EVERY EXISTS_TAC [`V:p2alv`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `U:A->bool`;
                          `phi:A->real^N`; `N:real^N->bool`;
                          `Phi:real^N->real^(N,N)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a' < b'` ASSUME_TAC THENL
   [USE_THEN "TIME" (MP_TAC o SPEC `sb:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sb /\ &0 < sb pow 2 /\ sb pow 2 < s2 pow 2 /\ &0 <= sb pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb)) = (gamma:real->A)(sb pow 2)`
  (LABEL_TAC "CQE") THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lexp")) (lhs(concl th)))) THEN
    MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                   `p2a_Lexp (V:p2alv) tt (x:A) (sb pow 2) Z`] P2A_REGION_CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[p2a_Lexp] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "GEQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `\v:real^1. (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb))`; `sb:real`; `s2:real`; `sw:real`;
                 `sw + r`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIFFERENTIABLE_CONST; VECTOR_DERIVATIVE_CONST_AT; CONTINUOUS_CONST] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN USE_THEN "CQE" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `\tau:real. (gamma:real->A)(sb pow 2)`;
                 `gamma:real->A`; `(\tau. if tau <= sb pow 2 then (gamma:real->A) tau else gamma(sb pow 2))`; `s2 pow 2`; `sb pow 2`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `~(s2 pow 2 <= sb pow 2)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]]);;

let P2AL_CONST_PC1 = prove
 (`!(V:p2alv) tt (x:A) gamma Z sb sw r W a' b' U (phi:A->real^N) N Phi s2.
     p2a_svs V /\ p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\
     sw < sb /\ sb < s2 /\ s2 < sw + r /\ p2al_lin V tt sw r W b' U phi Phi Z sb /\
     p2a_pc1 V tt gamma (&0) (sb pow 2) {} /\
     (!tau. &0 <= tau /\ tau <= sb pow 2 ==> gamma tau = p2a_Lgeo V tt x Z (sb pow 2) tau) /\
     chart_inv (U INTER W,phi) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)) = gamma(sb pow 2) /\
     sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sb) = vec 0
     ==> p2a_pc1 V tt (\tau. if tau <= sb pow 2 then (gamma:real->A) tau else gamma(sb pow 2)) (&0) (s2 pow 2) {}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "GEQ") (CONJUNCTS_THEN2 (LABEL_TAC "CQE") ASSUME_TAC)))))))))) THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi /\ &0 <= sw`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ p2a_region (V:p2alv) W a' b' /\ (U,phi:A->real^N) IN p2a_vatlas V b'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_lwa]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. sw < s /\ s < sw + r ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'`
  (LABEL_TAC "TIME") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AL_WIN_TIME THEN
    MAP_EVERY EXISTS_TAC [`V:p2alv`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `U:A->bool`;
                          `phi:A->real^N`; `N:real^N->bool`;
                          `Phi:real^N->real^(N,N)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a' < b'` ASSUME_TAC THENL
   [USE_THEN "TIME" (MP_TAC o SPEC `sb:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sb /\ &0 < sb pow 2 /\ sb pow 2 < s2 pow 2 /\
                sw pow 2 < sb pow 2 /\ s2 pow 2 < (sw + r) pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tau. sw pow 2 < tau /\ tau < (sw + r) pow 2
                      ==> a' < tt - tau /\ tt - tau <= b'`
  (LABEL_TAC "TAUW") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`sw:real`; `sw + r`; `tau:real`] P2AL_SQRT_WIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "TIME" (MP_TAC o SPEC `sqrt tau`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  POP_ASSUM(LABEL_TAC "E") THEN
  (* the constant piece is corner-free and C^1 at its start *)
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `\v:real^1. (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb))`; `\v:real^1. (vec 0:real^N)`;
                 `\tau:real. (gamma:real->A)(sb pow 2)`; `sb pow 2`; `s2 pow 2`]
                P2AL_CHART_PC1) THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; CONTINUOUS_CONST] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    USE_THEN "TAUW" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CPC") (LABEL_TAC "CRT"))] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `\tau:real. (gamma:real->A)(sb pow 2)`;
                 `gamma:real->A`; `(\tau. if tau <= sb pow 2 then (gamma:real->A) tau else gamma(sb pow 2))`; `s2 pow 2`; `sb pow 2`; `{}:real->bool`;
                 `{}:real->bool`] P2A_SEG_GLUE_PC1) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[UNION_EMPTY] THEN DISCH_THEN(LABEL_TAC "BASE")] THEN
  (* a window (sb - e2, sb + e2) of the flow around sb *)
  ABBREV_TAC `e2 = min (e / &2) ((sb - sw) / &2)` THEN
  SUBGOAL_THEN `&0 < e2 /\ e2 < e /\ sw < sb - e2 /\ &0 <= sb - e2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. sb - e2 < s /\ s < sb + e2
        ==> sw < s /\ s < sw + r /\ p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s`
  (LABEL_TAC "WIN") THENL
   [GEN_TAC THEN STRIP_TAC THEN USE_THEN "E" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sb + e2 < sw + r` ASSUME_TAC THENL
   [USE_THEN "E" (MP_TAC o SPEC `sb + e2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sw pow 2 < (sb - e2) pow 2 /\ (sb - e2) pow 2 < sb pow 2 /\
                sb pow 2 < (sb + e2) pow 2 /\ (sb + e2) pow 2 < (sw + r) pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\v. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (drop v))`; `\v. sndcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (drop v))`;
                 `sb - e2`; `sb + e2`; `sb:real`] P2AL_FREEZE_C1) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WIN_GCONT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    DISCH_THEN(LABEL_TAC "FRZ")] THEN
  ABBREV_TAC `k = min ((sb pow 2 - (sb - e2) pow 2) / &3) (((sb + e2) pow 2 - sb pow 2) / &3)` THEN
  SUBGOAL_THEN `&0 < k /\ (sb - e2) pow 2 < sb pow 2 - &2 * k /\
                sb pow 2 + &2 * k < (sb + e2) pow 2 /\ &0 <= sb pow 2 - k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `sb - e2` REAL_LE_POW_2) THEN EXPAND_TAC "k" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* the chart curve sig with its constant continuation is C^1 in every chart near sb^2 *)
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `(\v. if drop v <= sb pow 2 then fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (sqrt(drop v))) else fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))`; `(\v. if drop v <= sb pow 2 then inv(&2 * sqrt(drop v)) % sndcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (sqrt(drop v))) else vec 0)`; `(\tau. chart_inv (U INTER W,phi:A->real^N) (if tau <= sb pow 2 then fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (sqrt tau)) else fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)))`; `sb pow 2 - &2 * k`;
                 `sb pow 2 + &2 * k`] P2AL_CHART_C1S) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN USE_THEN "TAUW" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      USE_THEN "FRZ" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`sb - e2`; `sb + e2`; `tau:real`] P2AL_SQRT_WIN) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "WIN" (MP_TAC o SPEC `sqrt tau`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sqrt tau`] P2AL_WOK_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    DISCH_THEN(LABEL_TAC "SC1")] THEN
  SUBGOAL_THEN `!tau. sb pow 2 - k < tau /\ tau < sb pow 2 + k ==> (\tau. if tau <= sb pow 2 then (gamma:real->A) tau else gamma(sb pow 2)) tau = (\tau. chart_inv (U INTER W,phi:A->real^N) (if tau <= sb pow 2 then fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (sqrt tau)) else fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb))) tau`
  (LABEL_TAC "GSIG") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`sb - e2`; `sb + e2`; `tau:real`] P2AL_SQRT_WIN) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "WIN" (MP_TAC o SPEC `sqrt tau`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sqrt tau`] P2AL_WOK_LGEO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lexp")) (lhs(concl th)) &&
      can (find_term ((=) `tau:real`)) (concl th))) THEN
    MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                   `p2a_Lexp (V:p2alv) tt (x:A) tau Z`] P2A_REGION_CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "GEQ" (MP_TAC o SPEC `tau:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[p2a_Lexp] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `sb pow 2`; `tau:real`]
                  P2AL_LGEO_AGREE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o CONJUNCT2) THEN REWRITE_TAC[REAL_LE_REFL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `(\tau. if tau <= sb pow 2 then (gamma:real->A) tau else gamma(sb pow 2))`; `(\tau. if tau <= sb pow 2 then (gamma:real->A) tau else gamma(sb pow 2))`; `(\tau. chart_inv (U INTER W,phi:A->real^N) (if tau <= sb pow 2 then fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (sqrt tau)) else fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sb)))`; `s2 pow 2`; `sb pow 2`;
                 `sb pow 2`; `sb pow 2 - k`; `sb pow 2 + k`; `{sb pow 2}`;
                 `{}:real->bool`] P2A_PC1_PATCH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_EMPTY; REAL_LE_REFL; NOT_IN_EMPTY; IN_SING] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`tau0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
      EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "SC1" MATCH_MP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* L13, P2A_BARRIER_FIX.  P2AL_BARRIER_N is the dimension-generic form with *)
(* n = dimindex(:N); the main theorem is its instance at N = 3.             *)
(* ========================================================================= *)

let P2AL_BARRIER_N = prove
 (`!(V:p2alv) tt (x:A) b gamma O e.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_min V tt x b gamma /\
     &0 < e /\ open_in (p2a_vtop V (tt - b)) O /\ gamma b IN O /\
     (!g'. p2a_adm V tt x b g' /\ g' b IN O
           ==> p2a_L_length V tt gamma b <= p2a_L_length V tt g' b)
     ==> ?d. &0 < d /\
             !b'. b < b' /\ b' < b + d
                  ==> ?g'. p2a_adm1 V tt x b' g' /\ g' b' = gamma b /\
                           p2a_L_length V tt g' b' / (&2 * sqrt b') -
                           p2a_L_length V tt gamma b / (&2 * sqrt b) <=
                           ((&(dimindex(:N)) / &2 -
                             p2a_L_length V tt gamma b / (&2 * sqrt b)) / b + e) *
                           (b' - b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`; `O:A->bool`]
                P2AL_BAR_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "GEQ") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "LEQ") (CONJUNCTS_THEN2 (LABEL_TAC "XEQ")
    (LABEL_TAC "SLM"))))))))) THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) b` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_Smin; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_adm (V:p2alv) tt (x:A) b gamma` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  USE_THEN "LEQ" (fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC `sb = sqrt b` THEN
  SUBGOAL_THEN `&0 < sb /\ b = sb pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sb" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `b:real`)) THEN
  (* a window at the end point *)
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `sb pow 2`; `sb:real`]
                P2AL_LWIN_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sw:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `N:real^N->bool`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AL_LWIN_WOK) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_WOK_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ew:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E")) o
             last o CONJUNCTS) THEN
  ABBREV_TAC `sq = sb + min (ew / &2) ((sw + r - sb) / &2)` THEN
  SUBGOAL_THEN `sb < sq /\ sq < sw + r /\ abs(sq - sb) < ew` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sq" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "E" (MP_TAC o SPEC `sq:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sq:real`] P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `sb pow 2 < sq pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_Lexp (V:p2alv) tt (x:A) (sb pow 2) Z IN O` ASSUME_TAC THENL
   [USE_THEN "XEQ" SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* first and second order at the end point *)
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `O:A->bool`; `sb:real`;
                 `sq pow 2`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`;
                 `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`] P2AL_END_NOCONJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `O:A->bool`; `sb:real`;
                 `sq pow 2`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`;
                 `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`] P2AL_END_H) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the constant extension *)
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`] P2AL_CONST_CL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e * sb pow 2`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dC:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CL"))) THEN
  ABBREV_TAC `KX = abs(&(dimindex(:N)) - p2a_Ltil (V:p2alv) tt (x:A) (sb pow 2) Z / sb) *
                   (&3 * sb + &1) + &1` THEN
  SUBGOAL_THEN `&0 < KX` ASSUME_TAC THENL
   [EXPAND_TAC "KX" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ds = min (min (sw + r - sb) dC) (min (&1) ((&3 * e * sb pow 4) / KX))` THEN
  SUBGOAL_THEN `&0 < (&3 * e * sb pow 4) / KX` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ds /\ ds <= sw + r - sb /\ ds <= dC /\ ds <= &1 /\
                ds <= (&3 * e * sb pow 4) / KX`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "ds" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `ds pow 2` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `bq:real` THEN STRIP_TAC THEN
  ABBREV_TAC `s2 = sqrt bq` THEN
  SUBGOAL_THEN `sb < s2 /\ s2 < sb + ds /\ s2 pow 2 = bq` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN
    MP_TAC(SPECL [`sb:real`; `sb + ds`; `bq:real`] P2AL_SQRT_WIN) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `&0 <= sb * ds` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `bq < sb pow 2 + ds pow 2` THEN UNDISCH_TAC `sb pow 2 < bq` THEN
      UNDISCH_TAC `&0 < sb` THEN UNDISCH_TAC `&0 < ds` THEN REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 < sw + r /\ s2 < sb + dC /\ s2 <= sb + &1 /\
                (s2 - sb) * KX <= &3 * e * sb pow 4`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ds * KX` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]];
    ALL_TAC] THEN
  USE_THEN "CL" (MP_TAC o SPEC `s2:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `gamma:real->A`; `Z:real^N`; `sb:real`;
                 `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`;
                 `s2:real`] P2AL_CONST_ADM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `gamma:real->A`; `Z:real^N`; `sb:real`;
                 `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`;
                 `s2:real`] P2AL_CONST_PC1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  EXISTS_TAC `(\tau. if tau <= sb pow 2 then (gamma:real->A) tau else gamma(sb pow 2))` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `s2 pow 2 = bq`)) THEN
  REWRITE_TAC[p2a_adm1] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(s2 pow 2 <= sb pow 2)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&(dimindex(:N))`; `sb:real`; `s2:real`;
                `p2a_Ltil (V:p2alv) tt (x:A) (sb pow 2) Z / sb`; `lscalar ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sb pow 2)) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb))`;
                `p2a_cL (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt (\v. (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sb))) sb s2`; `e:real`] P2AL_BAR_ARITH) THEN
  SUBGOAL_THEN `sb * p2a_Ltil (V:p2alv) tt (x:A) (sb pow 2) Z / sb = p2a_Ltil V tt x (sb pow 2) Z`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(s2 - sb) * KX <= &3 * e * sb pow 4` THEN EXPAND_TAC "KX" THEN
  REWRITE_TAC[]);;

(* The main theorem at N = 3 (rfs_vtop is p2a_vtop there, P2A_VIEW_PROJ_3).  *)

let P2A_BARRIER_FIX = prove
 (`!u:A->bool. P2A_BARRIER_FIX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_BARRIER_FIX_STATEMENT; GSYM P2A_VIEW_PROJ_3] THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] P2AL_BARRIER_N) THEN
  REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_ACCEPT_TAC);;

