(* ========================================================================= *)
(* Unit pc_p2b_g3c: chart changes of weighted weak integrands on the limit   *)
(* of G3.  For charts c, c' of the limit and integrands w (q rho +           *)
(* bil(A, U, sigma)) supported in the overlap, the integrals over the two    *)
(* chart boxes agree (P2BX_COV_TRANSFER and P2BX_TRANSFER_POINT of           *)
(* pc_p2b_g1w with lam = 1, chart transitions and METRIC_LOCAL_JAC).         *)
(* ========================================================================= *)

needs "src/pc_p2b_g3b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The abstract weighted transfer (time unscaled, lam = 1).                  *)
(* ========================================================================= *)

let P2BX_WTRANSFER = prove
 (`!(U:real^N->bool) V H H' (om0:real^(N,1)finite_sum->bool) N0 G0 G l0 l s0 s
    w0 w q0 q Zq.
     diffeomorphism_on U V H H' /\ open om0 /\ open N0 /\
     (!y. y IN om0 ==> transp(G0 y) = G0 y /\ !v. ~(v = vec 0) ==> &0 < v dot (G0 y ** v)) /\
     wan_loclip om0 l0 /\ wan_loclip om0 s0 /\
     (!z. z IN N0
          ==> fstcart z IN U /\ pastecart (H(fstcart z)) (sndcart z) IN om0 /\
              G z = transp(matrix(frechet_derivative H (at (fstcart z)))) **
                    G0(pastecart (H(fstcart z)) (sndcart z)) **
                    matrix(frechet_derivative H (at (fstcart z))) /\
              l z = l0(pastecart (H(fstcart z)) (sndcart z)) /\
              s z = s0(pastecart (H(fstcart z)) (sndcart z)) /\
              w z = w0(pastecart (H(fstcart z)) (sndcart z))) /\
     negligible Zq /\
     (!z. z IN N0 /\ ~(z IN Zq) /\
          (\y. lift(l0 y)) differentiable at (pastecart (H(fstcart z)) (sndcart z))
          ==> q z = q0(pastecart (H(fstcart z)) (sndcart z))) /\
     (\y. lift(w0 y * q0 y * sqrt(det(G0 y)) +
               w0 y * p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 s0 y))
       absolutely_integrable_on om0 /\
     (!y. ~(y IN IMAGE (\z. pastecart (H(fstcart z)) (sndcart z)) N0)
          ==> w0 y * q0 y * sqrt(det(G0 y)) +
              w0 y * p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 s0 y = &0)
     ==> (\z. lift(w z * q z * sqrt(det(G z)) +
                   w z * p2bw_bil (\z. sqrt(det(G z)) %% matrix_inv(G z)) l s z))
           integrable_on N0 /\
         integral N0 (\z. lift(w z * q z * sqrt(det(G z)) +
                              w z * p2bw_bil (\z. sqrt(det(G z)) %% matrix_inv(G z)) l s z)) =
         integral om0 (\y. lift(w0 y * q0 y * sqrt(det(G0 y)) +
                               w0 y * p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w))
                                                l0 s0 y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `&1`] P2BX_PHI_DIFFEO) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; LIFT_DROP; real_div; REAL_INV_1; REAL_MUL_RID;
                  VECTOR_MUL_LID] THEN
  STRIP_TAC THEN
  ABBREV_TAC `P = \z:real^(N,1)finite_sum. pastecart ((H:real^N->real^N)(fstcart z)) (sndcart z)` THEN
  ABBREV_TAC `P' = \w:real^(N,1)finite_sum. pastecart ((H':real^N->real^N)(fstcart w)) (sndcart w)` THEN
  SUBGOAL_THEN `!z:real^(N,1)finite_sum.
                 pastecart ((H:real^N->real^N)(fstcart z)) (sndcart z) = P z`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(N0:real^(N,1)finite_sum->bool) SUBSET {z | fstcart z IN U}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 SUBSET om0`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (find_term ((=) `P':real^(N,1)finite_sum->real^(N,1)finite_sum`)) (concl th) &&
    is_comb(concl th) && fst(dest_const(fst(strip_comb(concl th)))) = "diffeomorphism_on")) THEN
  SUBGOAL_THEN `!z:real^(N,1)finite_sum. z IN N0 ==> P'((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z) = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `P':real^(N,1)finite_sum->real^(N,1)finite_sum`)) (concl th) &&
      is_forall(concl th) && can (find_term ((=) `U:real^N->bool`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the bad set: points whose images are not differentiability points *)
  ABBREV_TAC `Zd = {z:real^(N,1)finite_sum | z IN N0 /\
                    ~((\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at
                      ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z) /\
                      (\y. lift((s0:real^(N,1)finite_sum->real) y)) differentiable at (P z))}` THEN
  SUBGOAL_THEN `negligible(Zd:real^(N,1)finite_sum->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `IMAGE (P':real^(N,1)finite_sum->real^(N,1)finite_sum)
                  {y | y IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 /\
                       ~((\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at y /\
                         (\y. lift((s0:real^(N,1)finite_sum->real) y)) differentiable at y)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE THEN
      REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `{y | y IN om0 /\
                         ~((\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at y)} UNION
                    {y | y IN om0 /\
                         ~((\y. lift((s0:real^(N,1)finite_sum->real) y)) differentiable at y)}` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THEN
          MATCH_MP_TAC P2BX_LOCLIP_AE_OPEN THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 SUBSET om0` THEN
          SET_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
      X_GEN_TAC `y:real^(N,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{w:real^(N,1)finite_sum | fstcart w IN V}` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && aconv (rhs(concl th)) `{w:real^(N,1)finite_sum | fstcart w IN V}`)) THEN
      UNDISCH_TAC `(y:real^(N,1)finite_sum) IN IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0` THEN
      UNDISCH_TAC `(N0:real^(N,1)finite_sum->bool) SUBSET {z | fstcart z IN U}` THEN SET_TAC[];
      EXPAND_TAC "Zd" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `z:real^(N,1)finite_sum` THEN STRIP_TAC THEN
      EXISTS_TAC `(P:real^(N,1)finite_sum->real^(N,1)finite_sum) z` THEN
      ASM_SIMP_TAC[] THEN EXISTS_TAC `z:real^(N,1)finite_sum` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the change of variables *)
  MP_TAC(REWRITE_RULE[REAL_MUL_LID; LIFT_DROP; REAL_INV_1; REAL_POW_ONE; SQRT_1; REAL_MUL_RID;
                      VECTOR_MUL_LID; REAL_LT_01]
   (ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`; `&1`;
            `om0:real^(N,1)finite_sum->bool`; `N0:real^(N,1)finite_sum->bool`;
            `\y. (w0:real^(N,1)finite_sum->real) y * q0 y * sqrt(det((G0:real^(N,1)finite_sum->real^N^N) y)) +
                 w0 y * p2bw_bil (\w. sqrt(det(G0 w)) %% matrix_inv(G0 w)) l0 s0 y`;
            `\z. (w:real^(N,1)finite_sum->real) z * q z * sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) +
                 w z * p2bw_bil (\z. sqrt(det(G z)) %% matrix_inv(G z)) l s z`;
            `(Zq:real^(N,1)finite_sum->bool) UNION Zd`] P2BX_COV_TRANSFER)) THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN BETA_TAC THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_SIMP_TAC[] THEN NO_TAC) THEN
  TRY(X_GEN_TAC `y:real^(N,1)finite_sum` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  X_GEN_TAC `z:real^(N,1)finite_sum` THEN REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at
      ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z) /\
    (\y. lift((s0:real^(N,1)finite_sum->real) y)) differentiable at (P z)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~((z:real^(N,1)finite_sum) IN Zd)` THEN EXPAND_TAC "Zd" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[REAL_MUL_LID; LIFT_DROP; REAL_INV_1; REAL_POW_ONE; SQRT_1; MATRIX_CMUL_LID]
   (ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`; `&1`;
            `G0:real^(N,1)finite_sum->real^N^N`; `l0:real^(N,1)finite_sum->real`;
            `s0:real^(N,1)finite_sum->real`; `N0:real^(N,1)finite_sum->bool`;
            `G:real^(N,1)finite_sum->real^N^N`; `l:real^(N,1)finite_sum->real`;
            `s:real^(N,1)finite_sum->real`; `z:real^(N,1)finite_sum`] P2BX_TRANSFER_POINT)) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(w:real^(N,1)finite_sum->real) z = w0((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z) /\
                (q:real^(N,1)finite_sum->real) z = q0(P z)`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The chart data of the limit under a chart transition (functions read in   *)
(* charts, scalar curvature, chart metric).                                  *)
(* ========================================================================= *)

let P2BX_CHART_DATA_TRANS = prove
 (`!(top':B topology) atlas' (g':real->B->real^3^3) U1 phi1 U2 phi2 z.
     smooth_manifold_atlas top' atlas' /\ (U1,phi1) IN atlas' /\ (U2,phi2) IN atlas' /\
     fstcart z IN IMAGE phi1 (U1 INTER U2)
     ==> (!f. p2bw_cfun (U2,phi2) f
                (pastecart (chart_trans (U1,phi1) (U2,phi2) (fstcart z)) (sndcart z)) =
              p2bw_cfun (U1,phi1) f z) /\
         p2bw_cscal atlas' (U2,phi2) (&1) g'
           (pastecart (chart_trans (U1,phi1) (U2,phi2) (fstcart z)) (sndcart z)) =
         p2bw_cscal atlas' (U1,phi1) (&1) g' z /\
         p2bw_cmet atlas' (U1,phi1) (&1) g' z =
         transp(matrix(frechet_derivative (chart_trans (U1,phi1) (U2,phi2)) (at (fstcart z)))) **
         p2bw_cmet atlas' (U2,phi2) (&1) g'
           (pastecart (chart_trans (U1,phi1) (U2,phi2) (fstcart z)) (sndcart z)) **
         matrix(frechet_derivative (chart_trans (U1,phi1) (U2,phi2)) (at (fstcart z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `xx:B` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) o
    REWRITE_RULE[IN_IMAGE]) THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(U1:B->bool,phi1:B->real^3)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(U2:B->bool,phi2:B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `chart_inv (U1:B->bool,phi1:B->real^3) (phi1 xx) = xx /\
                chart_trans (U1,phi1) (U2,phi2) (phi1 xx) = (phi2:B->real^3) xx /\
                chart_inv (U2,phi2) (phi2 xx) = xx`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `phi1:B->real^3`)) (concl th) &&
        can (find_term ((=) `U1:B->bool`)) (concl th) &&
        not(can (find_term ((=) `IMAGE:(B->real^3)->(B->bool)->real^3->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CHART_TRANS_AT THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `phi2:B->real^3`)) (concl th) &&
        can (find_term ((=) `U2:B->bool`)) (concl th) &&
        not(can (find_term ((=) `IMAGE:(B->real^3)->(B->bool)->real^3->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2bw_cfun; p2bw_cscal; p2bw_cmet; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U1:B->bool`; `phi1:B->real^3`; `U2:B->bool`; `phi2:B->real^3`;
                 `(g':real->B->real^3^3)(&1 - drop(sndcart(z:real^(3,1)finite_sum)))`; `xx:B`]
                METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[IN_INTER; chart_jac]);;

(* ========================================================================= *)
(* The weighted transfer between two charts of the limit, for integrands     *)
(* vanishing off the overlap region.                                         *)
(* ========================================================================= *)

let P2BX_CHART_WTRANSFER = prove
 (`!(top':B topology) atlas' (g':real->B->real^3^3) U1 phi1 U2 phi2
    (om1:real^(3,1)finite_sum->bool) om2 ww q1 q2 Zq u s.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     (!a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g') /\
     (U1,phi1) IN atlas' /\ (U2,phi2) IN atlas' /\
     open om1 /\ p2bg_cbox (U2,phi2) om2 /\
     wan_loclip om2 (p2bw_cfun (U2,phi2) u) /\ wan_loclip om2 (p2bw_cfun (U2,phi2) s) /\
     negligible Zq /\
     (!z. z IN om1 /\ fstcart z IN IMAGE phi1 (U1 INTER U2) /\ ~(z IN Zq) /\
          (\y. lift(p2bw_cfun (U2,phi2) u y)) differentiable at
            (pastecart (chart_trans (U1,phi1) (U2,phi2) (fstcart z)) (sndcart z))
          ==> q1 z = q2 (pastecart (chart_trans (U1,phi1) (U2,phi2) (fstcart z)) (sndcart z))) /\
     (!z. z IN om1 /\
          ~(fstcart z IN IMAGE phi1 (U1 INTER U2) /\
            pastecart (chart_trans (U1,phi1) (U2,phi2) (fstcart z)) (sndcart z) IN om2)
          ==> p2bw_cfun (U1,phi1) ww z * q1 z * sqrt(det(p2bw_cmet atlas' (U1,phi1) (&1) g' z)) +
              p2bw_cfun (U1,phi1) ww z *
              p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (U1,phi1) (&1) g' z)) %%
                            matrix_inv(p2bw_cmet atlas' (U1,phi1) (&1) g' z))
                       (p2bw_cfun (U1,phi1) u) (p2bw_cfun (U1,phi1) s) z = &0) /\
     (!y. y IN om2 /\
          ~(y IN IMAGE (\z. pastecart (chart_trans (U1,phi1) (U2,phi2) (fstcart z)) (sndcart z))
                       {z | z IN om1 /\ fstcart z IN IMAGE phi1 (U1 INTER U2) /\
                            pastecart (chart_trans (U1,phi1) (U2,phi2) (fstcart z)) (sndcart z)
                            IN om2})
          ==> p2bw_cfun (U2,phi2) ww y * q2 y * sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) g' y)) +
              p2bw_cfun (U2,phi2) ww y *
              p2bw_bil (\y. sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) g' y)) %%
                            matrix_inv(p2bw_cmet atlas' (U2,phi2) (&1) g' y))
                       (p2bw_cfun (U2,phi2) u) (p2bw_cfun (U2,phi2) s) y = &0) /\
     (\y. lift(p2bw_cfun (U2,phi2) ww y * q2 y * sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) g' y)) +
               p2bw_cfun (U2,phi2) ww y *
               p2bw_bil (\y. sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) g' y)) %%
                             matrix_inv(p2bw_cmet atlas' (U2,phi2) (&1) g' y))
                        (p2bw_cfun (U2,phi2) u) (p2bw_cfun (U2,phi2) s) y))
       absolutely_integrable_on om2
     ==> integral om1
           (\z. lift(p2bw_cfun (U1,phi1) ww z * q1 z *
                     sqrt(det(p2bw_cmet atlas' (U1,phi1) (&1) g' z)) +
                     p2bw_cfun (U1,phi1) ww z *
                     p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (U1,phi1) (&1) g' z)) %%
                                   matrix_inv(p2bw_cmet atlas' (U1,phi1) (&1) g' z))
                              (p2bw_cfun (U1,phi1) u) (p2bw_cfun (U1,phi1) s) z)) =
         integral om2
           (\y. lift(p2bw_cfun (U2,phi2) ww y * q2 y *
                     sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) g' y)) +
                     p2bw_cfun (U2,phi2) ww y *
                     p2bw_bil (\y. sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) g' y)) %%
                                   matrix_inv(p2bw_cmet atlas' (U2,phi2) (&1) g' y))
                              (p2bw_cfun (U2,phi2) u) (p2bw_cfun (U2,phi2) s) y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ricci_flow_on")) (concl th))) THEN
    REWRITE_TAC[REAL_LT_01; ricci_flow_on] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U1:B->bool`; `phi1:B->real^3`; `U2:B->bool`; `phi2:B->real^3`]
                CHART_TRANS_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `H = chart_trans (U1:B->bool,phi1:B->real^3) (U2,phi2)` THEN
  ABBREV_TAC `N0 = {z:real^(3,1)finite_sum | z IN om1 /\ fstcart z IN IMAGE (phi1:B->real^3) (U1 INTER U2) /\
                    pastecart ((H:real^3->real^3)(fstcart z)) (sndcart z) IN om2}` THEN
  SUBGOAL_THEN `(N0:real^(3,1)finite_sum->bool) SUBSET om1` ASSUME_TAC THENL
   [EXPAND_TAC "N0" THEN SET_TAC[]; ALL_TAC] THEN
  (* the box facts of the target chart *)
  SUBGOAL_THEN `open(om2:real^(3,1)finite_sum->bool) /\ bounded om2 /\
                om2 SUBSET {z | fstcart z IN IMAGE (SND (U2:B->bool,phi2:B->real^3)) (FST (U2,phi2)) /\
                                &0 < drop(sndcart z)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox (U2:B->bool,phi2:B->real^3) om2` THEN
    REWRITE_TAC[p2bg_cbox] THEN MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `(U2:B->bool,phi2:B->real^3)`;
                 `om2:real^(3,1)finite_sum->bool`] P2BX_LIMIT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* N0 is open *)
  SUBGOAL_THEN `open(N0:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(N0:real^(3,1)finite_sum->bool) =
                  {z | z IN om1 INTER {z | fstcart z IN IMAGE (phi1:B->real^3) (U1 INTER U2)} /\
                       (\z. pastecart ((H:real^3->real^3)(fstcart z)) (sndcart z)) z IN om2}`
    SUBST1_TAC THENL
     [EXPAND_TAC "N0" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(\z:real^(3,1)finite_sum. (H:real^3->real^3)(fstcart z)) = H o fstcart`
        SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (phi1:B->real^3) (U1 INTER U2)` THEN CONJ_TAC THENL
         [EXPAND_TAC "H" THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
          MATCH_MP_TAC CHART_TRANS_SMOOTH THEN
          MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[]];
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]];
      MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                              `phi2:B->real^3`] THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the integral over om1 is the integral over N0 *)
  SUBGOAL_THEN
   `integral om1
      (\z. lift(p2bw_cfun (U1:B->bool,phi1:B->real^3) ww z * q1 z *
                sqrt(det(p2bw_cmet atlas' (U1,phi1) (&1) (g':real->B->real^3^3) z)) +
                p2bw_cfun (U1,phi1) ww z *
                p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (U1,phi1) (&1) g' z)) %%
                              matrix_inv(p2bw_cmet atlas' (U1,phi1) (&1) g' z))
                         (p2bw_cfun (U1,phi1) u) (p2bw_cfun (U1,phi1) s) z)) =
    integral N0
      (\z. lift(p2bw_cfun (U1,phi1) ww z * q1 z *
                sqrt(det(p2bw_cmet atlas' (U1,phi1) (&1) g' z)) +
                p2bw_cfun (U1,phi1) ww z *
                p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (U1,phi1) (&1) g' z)) %%
                              matrix_inv(p2bw_cmet atlas' (U1,phi1) (&1) g' z))
                         (p2bw_cfun (U1,phi1) u) (p2bw_cfun (U1,phi1) s) z))`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP INTEGRAL_RESTRICT th)]) THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((z:real^(3,1)finite_sum) IN N0)` THEN EXPAND_TAC "N0" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  (* the guarded target weight *)
  ABBREV_TAC `w2 = \y:real^(3,1)finite_sum. if y IN om2 then p2bw_cfun (U2:B->bool,phi2:B->real^3)
                                                (ww:real->B->real) y else &0` THEN
  SUBGOAL_THEN
   `integral om2
      (\y. lift(p2bw_cfun (U2:B->bool,phi2:B->real^3) ww y * q2 y *
                sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) (g':real->B->real^3^3) y)) +
                p2bw_cfun (U2,phi2) ww y *
                p2bw_bil (\y. sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) g' y)) %%
                              matrix_inv(p2bw_cmet atlas' (U2,phi2) (&1) g' y))
                         (p2bw_cfun (U2,phi2) u) (p2bw_cfun (U2,phi2) s) y)) =
    integral om2
      (\y. lift((w2:real^(3,1)finite_sum->real) y * q2 y *
                sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) g' y)) +
                w2 y *
                p2bw_bil (\w. sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) g' w)) %%
                              matrix_inv(p2bw_cmet atlas' (U2,phi2) (&1) g' w))
                         (p2bw_cfun (U2,phi2) u) (p2bw_cfun (U2,phi2) s) y))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    EXPAND_TAC "w2" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the abstract transfer *)
  MP_TAC(ISPECL
   [`IMAGE (phi1:B->real^3) (U1 INTER U2)`; `IMAGE (phi2:B->real^3) (U1 INTER U2)`;
    `H:real^3->real^3`; `chart_trans (U2:B->bool,phi2:B->real^3) (U1,phi1)`;
    `om2:real^(3,1)finite_sum->bool`; `N0:real^(3,1)finite_sum->bool`;
    `p2bw_cmet atlas' (U2:B->bool,phi2:B->real^3) (&1) (g':real->B->real^3^3)`;
    `p2bw_cmet atlas' (U1:B->bool,phi1:B->real^3) (&1) (g':real->B->real^3^3)`;
    `p2bw_cfun (U2:B->bool,phi2:B->real^3) (u:real->B->real)`;
    `p2bw_cfun (U1:B->bool,phi1:B->real^3) (u:real->B->real)`;
    `p2bw_cfun (U2:B->bool,phi2:B->real^3) (s:real->B->real)`;
    `p2bw_cfun (U1:B->bool,phi1:B->real^3) (s:real->B->real)`;
    `w2:real^(3,1)finite_sum->real`;
    `p2bw_cfun (U1:B->bool,phi1:B->real^3) (ww:real->B->real)`;
    `q2:real^(3,1)finite_sum->real`; `q1:real^(3,1)finite_sum->real`;
    `Zq:real^(3,1)finite_sum->bool`] P2BX_WTRANSFER) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^(3,1)finite_sum) IN om1 /\
                  fstcart z IN IMAGE (phi1:B->real^3) (U1 INTER U2) /\
                  pastecart ((H:real^3->real^3)(fstcart z)) (sndcart z) IN om2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN N0` THEN EXPAND_TAC "N0" THEN
      REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':real->B->real^3^3`; `U1:B->bool`; `phi1:B->real^3`;
                   `U2:B->bool`; `phi2:B->real^3`; `z:real^(3,1)finite_sum`]
                  P2BX_CHART_DATA_TRANS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "w2" THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^(3,1)finite_sum) IN om1 /\
                  fstcart z IN IMAGE (phi1:B->real^3) (U1 INTER U2)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN N0` THEN EXPAND_TAC "N0" THEN
      SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Zq:real^(3,1)finite_sum->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC
     `\y. lift(p2bw_cfun (U2:B->bool,phi2:B->real^3) ww y * q2 y *
               sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) (g':real->B->real^3^3) y)) +
               p2bw_cfun (U2,phi2) ww y *
               p2bw_bil (\y. sqrt(det(p2bw_cmet atlas' (U2,phi2) (&1) g' y)) %%
                             matrix_inv(p2bw_cmet atlas' (U2,phi2) (&1) g' y))
                        (p2bw_cfun (U2,phi2) u) (p2bw_cfun (U2,phi2) s) y)` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    EXPAND_TAC "w2" THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^(3,1)finite_sum` THEN DISCH_TAC THEN EXPAND_TAC "w2" THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `IMAGE:(real^(3,1)finite_sum->real^(3,1)finite_sum)->
                                 (real^(3,1)finite_sum->bool)->real^(3,1)finite_sum->bool`))
        (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

