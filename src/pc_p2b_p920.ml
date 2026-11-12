(* ========================================================================= *)
(* Unit pc_p2b_p920 (Part 2B): the route G4 of MT Prop 9.20,                 *)
(* P2B_PROP_9_20_ROUTE |- !u w. P2B_PROP_9_20_ROUTE_STATEMENT u w            *)
(* (statements of pc_p2b_w920g): G1, G3, Cor 9.14 and the chart statement    *)
(* FLOW_CHART give Prop 9.20 with the theorems P2BW_COEFF_BRIDGE, P2BW_LIMIT *)
(* and P2BW_REG of pc_p2b_w920 applied on chart boxes.                       *)
(*                                                                           *)
(* Contents: chart data of the limit on bounded sets (FLOW_CHART), small     *)
(* balls are chart boxes, the local regularity on a chart box, the route.    *)
(* ========================================================================= *)

needs "src/pc_p2b_fchart.ml";;

prioritize_real();;
type_invention_error := true;;

(* The setting gives the smooth manifold and the flow of the limit. *)

let P2BX_SETUP_LIMIT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi.
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi
     ==> smooth_manifold_atlas top' atlas' /\
         (!a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g')`,
  REWRITE_TAC[p2bg_setup; p2c_flow_limit_with] THEN MESON_TAC[]);;

(* Chart data of the limit on a bounded subset of the chart domain at        *)
(* positive backward times: smooth metric and scalar curvature, positive     *)
(* definite metric (FLOW_CHART for the flow on (a,1) with a small).         *)

let P2BX_LIMIT_CHART_DATA = prove
 (`!(top':B topology) atlas' (g':real->B->real^3^3) c om.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     (!a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g') /\ c IN atlas' /\
     bounded om /\
     om SUBSET {z | fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)}
     ==> smooth_map_on om
           ((vectorize:real^3^3->real^(3,3)finite_prod) o p2bw_cmet atlas' c (&1) g') /\
         smooth_map_on om (\z. lift(p2bw_cscal atlas' c (&1) g' z)) /\
         (!z. z IN om
              ==> transp(p2bw_cmet atlas' c (&1) g' z) = p2bw_cmet atlas' c (&1) g' z /\
                  !v. ~(v = vec 0) ==> &0 < v dot (p2bw_cmet atlas' c (&1) g' z ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `om SUBSET p2bw_cdom (c:(B->bool)#(B->real^3)) (&1 - --B)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; p2bw_cdom; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^(3,1)finite_sum) IN
                  {z | fstcart z IN IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))) /\
                       &0 < drop(sndcart z)}` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `norm(z:real^(3,1)finite_sum) <= B` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `z:real^(3,1)finite_sum` NORM_SNDCART) THEN
    MP_TAC(ISPEC `sndcart(z:real^(3,1)finite_sum)` NORM_1) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2B_FLOW_CHART_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                             `--B:real`; `&1`; `g':real->B->real^3^3`;
                             `c:(B->bool)#(B->real^3)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `p2bw_cdom (c:(B->bool)#(B->real^3)) (&1 - --B)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `p2bw_cdom (c:(B->bool)#(B->real^3)) (&1 - --B)` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* Small balls around chart points at positive backward times are chart     *)
(* boxes.                                                                    *)

let P2BX_CBOX_BALL = prove
 (`!(c:(B->bool)#(B->real^3)) z.
     open(IMAGE (SND c) (FST c)) /\ fstcart z IN IMAGE (SND c) (FST c) /\
     &0 < drop(sndcart z)
     ==> ?r. &0 < r /\ p2bg_cbox c (ball(z,r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `open {z:real^(3,1)finite_sum |
          fstcart z IN IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))) /\
          &0 < drop(sndcart z)}`
  MP_TAC THENL
   [SUBGOAL_THEN
     `{z:real^(3,1)finite_sum |
       fstcart z IN IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))) /\
       &0 < drop(sndcart z)} =
      IMAGE (SND c) (FST c) PCROSS {t:real^1 | t$1 > &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                  FSTCART_PASTECART; SNDCART_PASTECART; drop; real_gt];
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_HALFSPACE_COMPONENT_GT]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[p2bg_cbox; OPEN_BALL; BOUNDED_BALL] THEN
  ASM_SIMP_TAC[CLOSURE_BALL]);;

(* On a chart box with the chart data of G1: the coefficient bridge and the *)
(* local limit lemma give the local Lipschitz property of linf and the weak *)
(* identity in the form of P2BW_REG.                                         *)

let P2BX_CDATA_LIMIT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau (top':B topology) atlas' g'
    phi c om ix linf.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     (!a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g') /\ c IN atlas' /\
     p2bg_cbox c om /\
     p2bg_cdata (top,atlas) g p tau atlas' g' phi c om ix linf
     ==> wan_loclip om (p2bw_cfun c linf) /\
         (!psi. wan_test om psi /\ (!z. &0 <= psi z)
                ==> integral om (\z. lift(psi z * wan_tder (p2bw_cfun c linf) z *
                                          sqrt(det(p2bw_cmet atlas' c (&1) g' z)))) =
                    integral om
                      (\z. lift(psi z *
                                ((p2bw_cscal atlas' c (&1) g' z *
                                  sqrt(det(p2bw_cmet atlas' c (&1) g' z)) -
                                  p2bw_bil (\w. sqrt(det(p2bw_cmet atlas' c (&1) g' w)) %%
                                                matrix_inv(p2bw_cmet atlas' c (&1) g' w))
                                           (p2bw_cfun c linf) (p2bw_cfun c linf) z) / &2 -
                                 p2bw_cfun c linf z / (&2 * drop(sndcart z)) *
                                 sqrt(det(p2bw_cmet atlas' c (&1) g' z))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(om:real^(3,1)finite_sum->bool) /\ bounded om /\
                om SUBSET {z | fstcart z IN IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))) /\
                               &0 < drop(sndcart z)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox (c:(B->bool)#(B->real^3)) om` THEN
    REWRITE_TAC[p2bg_cbox] THEN MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^(3,1)finite_sum. z IN om ==> &0 < drop(sndcart z)` ASSUME_TAC THENL
   [UNDISCH_TAC `om SUBSET {z | fstcart z IN IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))) /\
                               &0 < drop(sndcart z)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `c:(B->bool)#(B->real^3)`;
                 `om:real^(3,1)finite_sum->bool`] P2BX_LIMIT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2bg_cdata (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                (g:real->A->real^3^3) (p:A) (tau:num->real)
                (atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
                (phi:num->B->A) (c:(B->bool)#(B->real^3)) (om:real^(3,1)finite_sum->bool)
                (ix:num->num) (linf:real->B->real)` THEN
  REWRITE_TAC[p2bg_cdata; FORALL_AND_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(3,1)finite_sum->bool`;
                 `p2bg_smet (atlas:((A->bool)#(A->real^3))->bool) g tau (phi:num->B->A) c ix`;
                 `p2bw_cmet (atlas':((B->bool)#(B->real^3))->bool) c (&1) g'`]
     (REWRITE_RULE[P2BW_COEFF_BRIDGE_STATEMENT] (ISPEC `(:3)` P2BW_COEFF_BRIDGE))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o
      check (fun th -> can (find_term ((=) `vectorize:real^3^3->real^(3,3)finite_prod`))
                           (concl th) && is_comb(concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "smooth_map_on")) THEN
    REWRITE_TAC[o_DEF];
    STRIP_TAC] THEN
  MP_TAC(ISPECL
    [`om:real^(3,1)finite_sum->bool`;
     `\m z. sqrt(det(p2bg_smet (atlas:((A->bool)#(A->real^3))->bool) g tau
                               (phi:num->B->A) c ix m z)) %%
            matrix_inv(p2bg_smet atlas g tau phi c ix m z)`;
     `\m z. sqrt(det(p2bg_smet (atlas:((A->bool)#(A->real^3))->bool) g tau
                               (phi:num->B->A) c ix m z))`;
     `p2bg_sscal (atlas:((A->bool)#(A->real^3))->bool) g tau (phi:num->B->A) c ix`;
     `p2bg_sfun (top:A topology,atlas:((A->bool)#(A->real^3))->bool) g p tau
                (phi:num->B->A) c ix`;
     `\z. sqrt(det(p2bw_cmet (atlas':((B->bool)#(B->real^3))->bool) c (&1) g' z)) %%
          matrix_inv(p2bw_cmet atlas' c (&1) g' z)`;
     `\z. sqrt(det(p2bw_cmet (atlas':((B->bool)#(B->real^3))->bool) c (&1) g' z))`;
     `p2bw_cscal (atlas':((B->bool)#(B->real^3))->bool) c (&1) g'`;
     `p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real)`]
    (REWRITE_RULE[P2BW_LIMIT_STATEMENT] (ISPEC `(:3)` P2BW_LIMIT))) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `smooth_map_on om (\z. lift(p2bw_cscal atlas' c (&1) (g':real->B->real^3^3) z))` THEN
    SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    SIMP_TAC[]]);;

(* The local regularity on a chart box: P2BW_REG with the weak equation of *)
(* G3 and the outputs of P2BX_CDATA_LIMIT.                                  *)

let P2BX_BOX_REG = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c om.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_g3out (top,atlas) g p (top',atlas') g' linf /\
     c IN atlas' /\ p2bg_cbox c om
     ==> smooth_map_on om (\z. lift(p2bw_cfun c linf z)) /\
         !z. z IN om
             ==> wan_tder (p2bw_cfun c linf) z +
                 lgrad2 (p2bw_slice (p2bw_cmet atlas' c (&1) g') z)
                        (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                 p2bw_cscal atlas' c (&1) g' z + &3 / (&2 * drop(sndcart z)) -
                 llap (p2bw_slice (p2bw_cmet atlas' c (&1) g') z)
                      (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) = &0 /\
                 &2 * llap (p2bw_slice (p2bw_cmet atlas' c (&1) g') z)
                           (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                 lgrad2 (p2bw_slice (p2bw_cmet atlas' c (&1) g') z)
                        (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) +
                 p2bw_cscal atlas' c (&1) g' z +
                 (p2bw_cfun c linf z - &3) / drop(sndcart z) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_LIMIT) THEN
  SUBGOAL_THEN `p2bg_weq atlas' g' (c:(B->bool)#(B->real^3)) om (linf:real->B->real)`
  MP_TAC THENL
   [UNDISCH_TAC `p2bg_g3out (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                   (g:real->A->real^3^3) (p:A)
                   (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                   (g':real->B->real^3^3) (linf:real->B->real)` THEN
    REWRITE_TAC[p2bg_g3out] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[p2bg_weq] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `?m0. p2bg_cdata (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
           (g:real->A->real^3^3) (p:A) (tau:num->real)
           (atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
           (phi:num->B->A) (c:(B->bool)#(B->real^3)) (om:real^(3,1)finite_sum->bool)
           (\j. (sub:num->num)(m0 + j)) (linf:real->B->real)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_g1out (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                   (g:real->A->real^3^3) (p:A) (tau:num->real)
                   (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                   (g':real->B->real^3^3) (W:num->B->bool) (phi:num->B->A)
                   (sub:num->num) (linf:real->B->real)` THEN
    REWRITE_TAC[p2bg_g1out] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                 `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                 `om:real^(3,1)finite_sum->bool`; `\j. (sub:num->num)(m0 + j)`;
                 `linf:real->B->real`] P2BX_CDATA_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(om:real^(3,1)finite_sum->bool) /\ bounded om /\
                om SUBSET {z | fstcart z IN IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))) /\
                               &0 < drop(sndcart z)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox (c:(B->bool)#(B->real^3)) om` THEN
    REWRITE_TAC[p2bg_cbox] THEN MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `c:(B->bool)#(B->real^3)`;
                 `om:real^(3,1)finite_sum->bool`] P2BX_LIMIT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
    [`om:real^(3,1)finite_sum->bool`;
     `p2bw_cmet (atlas':((B->bool)#(B->real^3))->bool) c (&1) g'`;
     `p2bw_cscal (atlas':((B->bool)#(B->real^3))->bool) c (&1) g'`;
     `p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real)`]
    (REWRITE_RULE[P2BW_REG_STATEMENT] (ISPEC `(:3)` P2BW_REG))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `om SUBSET {z | fstcart z IN IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))) /\
                               &0 < drop(sndcart z)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[DIMINDEX_3] THEN SIMP_TAC[]]);;

(* The route G4. *)

let P2B_PROP_9_20_ROUTE = prove
 (`!(u:A->bool) (w:B->bool). P2B_PROP_9_20_ROUTE_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_PROP_9_20_ROUTE_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") (CONJUNCTS_THEN2 (LABEL_TAC "G3")
    (CONJUNCTS_THEN2 (LABEL_TAC "C914") (LABEL_TAC "FC")))) THEN
  REWRITE_TAC[P2B_PROP_9_20_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
    `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
    `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_LIMIT) THEN
  REMOVE_THEN "G1" (MP_TAC o GEN_REWRITE_RULE I [P2B_W920_G1_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
    `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
    `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_TAC `linf:real->B->real`)) THEN
  REMOVE_THEN "G3" (MP_TAC o GEN_REWRITE_RULE I [P2B_W920_G3_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
    `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
    `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?V. ((\t. p2b_kfrv (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                (g:real->A->real^3^3) (p:A) t) ---> V) at_posinfinity /\
        p2bg_rvol (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
          (g':real->B->real^3^3) (linf:real->B->real) V`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_g3out (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                   (g:real->A->real^3^3) (p:A)
                   (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                   (g':real->B->real^3^3) (linf:real->B->real)` THEN
    REWRITE_TAC[p2bg_g3out] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `V < sqrt(&4 * pi) pow 3` ASSUME_TAC THENL
   [REMOVE_THEN "C914" (MP_TAC o GEN_REWRITE_RULE I [P2B_COR_9_14_STATEMENT]) THEN
    UNDISCH_TAC `p2bg_setup (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                   (g:real->A->real^3^3) (p:A) (tau:num->real) (q:num->A)
                   (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                   (g':real->B->real^3^3) (xl:B) (W:num->B->bool) (phi:num->B->A)` THEN
    REWRITE_TAC[p2bg_setup] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `kappa:real`)
                               (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
    DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top:A topology`;
                               `atlas:((A->bool)#(A->real^3))->bool`;
                               `g:real->A->real^3^3`; `p:A`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `V':real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `V:real = V'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(ISPEC `at_posinfinity` REALLIM_UNIQUE) THEN
    EXISTS_TAC `\t. p2b_kfrv (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                      (g:real->A->real^3^3) (p:A) t` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_AT_POSINFINITY];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `linf:real->B->real`; `V:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p3_subseq sub /\
                p2bg_conv (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                  (g:real->A->real^3^3) (p:A) (tau:num->real) (top':B topology)
                  (W:num->B->bool) (phi:num->B->A) (sub:num->num) (linf:real->B->real)`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `p2bg_g1out (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                   (g:real->A->real^3^3) (p:A) (tau:num->real)
                   (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                   (g':real->B->real^3^3) (W:num->B->bool) (phi:num->B->A)
                   (sub:num->num) (linf:real->B->real)` THEN
    SIMP_TAC[p2bg_g1out];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c z. c IN atlas' /\ fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)
          ==> ?r. &0 < r /\ p2bg_cbox (c:(B->bool)#(B->real^3)) (ball(z,r))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_CBOX_BALL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:(B->bool)#(B->real^3)`; `tmax:real`] THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_CDOM_OPEN THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN REWRITE_TAC[p2bw_cdom; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:(B->bool)#(B->real^3)`; `z:real^(3,1)finite_sum`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(z:real^(3,1)finite_sum,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                   `sub:num->num`; `linf:real->B->real`; `c:(B->bool)#(B->real^3)`;
                   `ball(z:real^(3,1)finite_sum,r)`] P2BX_BOX_REG) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:(B->bool)#(B->real^3)`; `z:real^(3,1)finite_sum`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(B->bool)#(B->real^3)`; `z:real^(3,1)finite_sum`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `sub:num->num`; `linf:real->B->real`; `c:(B->bool)#(B->real^3)`;
                 `ball(z:real^(3,1)finite_sum,r)`] P2BX_BOX_REG) THEN
  ASM_SIMP_TAC[CENTRE_IN_BALL]);;

