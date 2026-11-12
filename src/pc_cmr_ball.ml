(* ========================================================================= *)
(* Unit pc_cmr_ball (a unit of the replacement chain of pc_cm_replacement):  *)
(* S^2 G-energies on sets of directions, the transport to planar discs       *)
(* through rotated stereographic charts, additivity, and the splitting of    *)
(* cm_sen into a chart disc and its exterior.                                *)
(*                                                                           *)
(* A G-weighted Parseval identity for the orthogonal frame of the slab chart *)
(* wan_nch of pc_wan_sob2s.                                                  *)
(* ========================================================================= *)

needs "src/pc_cmr_defs.ml";;
needs "src/pc_cm_target.ml";;
needs "src/pc_wan_sob2s.ml";;

prioritize_real();;
type_invention_error := true;;

let CMR_ORTHO3_BILIN = prove
 (`!(a1:real^3) a2 a3 v w.
     a1 dot a2 = &0 /\ a1 dot a3 = &0 /\ a2 dot a3 = &0 /\
     ~(a1 dot a1 = &0) /\ ~(a2 dot a2 = &0) /\ ~(a3 dot a3 = &0)
     ==> (a1 dot v) * (a1 dot w) / (a1 dot a1) + (a2 dot v) * (a2 dot w) / (a2 dot a2) +
         (a3 dot v) * (a3 dot w) / (a3 dot a3) = v dot w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a1:real^3`; `a2:real^3`; `a3:real^3`; `v + w:real^3`]
    WAN_ORTHO3_COMPLETE) THEN
  MP_TAC(ISPECL [`a1:real^3`; `a2:real^3`; `a3:real^3`; `v - w:real^3`]
    WAN_ORTHO3_COMPLETE) THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RSUB; DOT_LADD; DOT_LSUB] THEN
  REWRITE_TAC[ISPECL [`w:real^3`; `v:real^3`] DOT_SYM] THEN
  UNDISCH_TAC `~((a1:real^3) dot a1 = &0)` THEN UNDISCH_TAC `~((a2:real^3) dot a2 = &0)` THEN
  UNDISCH_TAC `~((a3:real^3) dot a3 = &0)` THEN CONV_TAC REAL_FIELD);;

let CMR_DOT_SYM_MAT = prove
 (`!(B:real^K^K) x y. transp B = B ==> x dot (B ** y) = y dot (B ** x)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM(ASSUME `transp(B:real^K^K) = B`)] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN MATCH_ACCEPT_TAC DOT_SYM);;

let CMR_PARSEVAL3_G = prove
 (`!(A:num->real^3) (V:num->real^K) (B:real^K^K).
     transp B = B /\
     A 1 dot A 2 = &0 /\ A 1 dot A 3 = &0 /\ A 2 dot A 3 = &0 /\
     ~(A 1 dot A 1 = &0) /\ ~(A 2 dot A 2 = &0) /\ ~(A 3 dot A 3 = &0)
     ==> sum(1..3) (\i. (vsum(1..3) (\j. A i$j % V j) dot
                         (B ** vsum(1..3) (\j. A i$j % V j))) / (A i dot A i)) =
         sum(1..3) (\j. V j dot (B ** V j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!j k. 1 <= j /\ j <= 3 /\ 1 <= k /\ k <= 3
          ==> (A:num->real^3) 1$j * A 1$k / (A 1 dot A 1) + A 2$j * A 2$k / (A 2 dot A 2) +
              A 3$j * A 3$k / (A 3 dot A 3) = if j = k then &1 else &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(A:num->real^3) 1`; `(A:num->real^3) 2`; `(A:num->real^3) 3`;
                   `basis j:real^3`; `basis k:real^3`] CMR_ORTHO3_BILIN) THEN
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3; DOT_BASIS_BASIS] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_3; VSUM_3; MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
              DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  MP_TAC(ISPECL [`B:real^K^K`; `(V:num->real^K) 1`; `(V:num->real^K) 2`] CMR_DOT_SYM_MAT) THEN
  MP_TAC(ISPECL [`B:real^K^K`; `(V:num->real^K) 1`; `(V:num->real^K) 3`] CMR_DOT_SYM_MAT) THEN
  MP_TAC(ISPECL [`B:real^K^K`; `(V:num->real^K) 2`; `(V:num->real^K) 3`] CMR_DOT_SYM_MAT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`1`; `1`] th) THEN MP_TAC(SPECL [`1`; `2`] th) THEN
    MP_TAC(SPECL [`1`; `3`] th) THEN MP_TAC(SPECL [`2`; `2`] th) THEN
    MP_TAC(SPECL [`2`; `3`] th) THEN MP_TAC(SPECL [`3`; `3`] th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `~((A:num->real^3) 1 dot A 1 = &0)` THEN
  UNDISCH_TAC `~((A:num->real^3) 2 dot A 2 = &0)` THEN
  UNDISCH_TAC `~((A:num->real^3) 3 dot A 3 = &0)` THEN
  CONV_TAC REAL_FIELD);;


(* ========================================================================= *)
(* The G-energy density on the shell (absolutely integrable on measurable    *)
(* subsets), cm_sen as its integral, cones over sets of directions, and the  *)
(* slab chart wan_nch on cones over stereographic images.                    *)
(* ========================================================================= *)

let CMR_GQUAD_MEASURABLE = prove
 (`!(G:real^K->real^K^K) (w:real^N->real^K) (a:real^N->real^K) s.
     lebesgue_measurable s /\ w measurable_on s /\ a measurable_on s /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K)
     ==> (\x. lift(a x dot (G(w x) ** a x))) measurable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\a b:real^K. lift(a dot b)`; `a:real^N->real^K`;
                 `\x. (G:real^K->real^K^K)((w:real^N->real^K) x) ** (a:real^N->real^K) x`;
                 `s:real^N->bool`] MEASURABLE_ON_BILINEAR) THEN
  REWRITE_TAC[BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                 `\x. (vectorize:real^K^K->real^(K,K)finite_prod)((G:real^K->real^K^K)
                                                               ((w:real^N->real^K) x))`;
                 `a:real^N->real^K`; `s:real^N->bool`] MEASURABLE_ON_BILINEAR) THEN
  REWRITE_TAC[GRGE_BILINEAR_MATRIFY_MUL; MATRIFY_VECTORIZE; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. (vectorize:real^K^K->real^(K,K)finite_prod)((G:real^K->real^K^K)
                                                      ((w:real^N->real^K) x))) =
    (\x. (\z. ((vectorize:real^K^K->real^(K,K)finite_prod) o G) z -
              ((vectorize:real^K^K->real^(K,K)finite_prod) o G) (vec 0)) (w x) +
         ((vectorize:real^K^K->real^(K,K)finite_prod) o G) (vec 0))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_ADD THEN REWRITE_TAC[MEASURABLE_ON_CONST_EQ] THEN
  MP_TAC(ISPECL [`w:real^N->real^K`;
                 `\z. ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)) z -
                      ((vectorize:real^K^K->real^(K,K)finite_prod) o G) (vec 0)`;
                 `s:real^N->bool`] MEASURABLE_ON_COMPOSE_CONTINUOUS_0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_REWRITE_TAC[ETA_AX; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let CMR_GQUAD_INTEGRABLE = prove
 (`!(G:real^K->real^K^K) (w:real^N->real^K) (a:real^N->real^K) s Lam.
     lebesgue_measurable s /\ w measurable_on s /\ a IN lspace s (&2) /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2)
     ==> (\x. lift(a x dot (G(w x) ** a x))) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x. lift(Lam * norm((a:real^N->real^K) x) pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMR_GQUAD_MEASURABLE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a:real^N->real^K) IN lspace s (&2)` THEN
    REWRITE_TAC[LSPACE_ALT; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`]]);;

let CMR_DENS_FACTS = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) Lam s.
     wan_s2_w12 u /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2) /\
     lebesgue_measurable s /\ s SUBSET wan_shell
     ==> (\z. lift(cmr_dens G u z)) absolutely_integrable_on s /\
         (!z. &0 <= cmr_dens G u z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. &0 <= cmr_dens (G:real^K->real^K^K) (u:real^3->real^K) z` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[cmr_dens] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `wan_shell` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  ASM_REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`; GSYM drop; LIFT_DROP] THEN
  CONJ_TAC THENL [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[cmr_dens; LIFT_SUM; o_DEF] THEN MATCH_MP_TAC INTEGRABLE_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC CMR_GQUAD_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
  MP_TAC(ISPECL [`wan_shell`; `j:num`; `wan_rext (u:real^3->real^K)`] WAN_WD_WORKS) THEN
  UNDISCH_TAC `wan_s2_w12 (u:real^3->real^K)` THEN
  REWRITE_TAC[wan_s2_w12] THEN DISCH_TAC THEN ASM_REWRITE_TAC[DIMINDEX_3] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMT_SHELL_OPEN] THEN
  UNDISCH_TAC `wan_w12 wan_shell (wan_rext (u:real^3->real^K))` THEN
  REWRITE_TAC[wan_w12; LSPACE_ALT; IN_ELIM_THM] THEN SIMP_TAC[]);;

let CMR_SEN_DENS = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) Lam.
     wan_s2_w12 u /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2)
     ==> cm_sen G u = drop(integral wan_shell (\z. lift(cmr_dens G u z))) / &3 /\
         cm_sen G u = cmr_sen_on G u (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cmr_cone(sphere(vec 0:real^3,&1)) = wan_shell` ASSUME_TAC THENL
   [REWRITE_TAC[cmr_cone; EXTENSION; IN_ELIM_THM; IN_SPHERE_0] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THEN SIMP_TAC[] THEN
    REWRITE_TAC[wan_shell; IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IN_SPHERE_0] P4_RADIAL_SPHERE) THEN
    REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cmr_sen_on] THEN
  REWRITE_TAC[cm_sen; wan_gdir; DIMINDEX_3] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[cmr_dens; LIFT_SUM; o_DEF] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_VSUM o rand o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CMR_GQUAD_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
    MP_TAC(ISPECL [`wan_shell`; `j:num`; `wan_rext (u:real^3->real^K)`] WAN_WD_WORKS) THEN
    UNDISCH_TAC `wan_s2_w12 (u:real^3->real^K)` THEN
    REWRITE_TAC[wan_s2_w12] THEN DISCH_TAC THEN ASM_REWRITE_TAC[DIMINDEX_3] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMT_SHELL_OPEN] THEN
    UNDISCH_TAC `wan_w12 wan_shell (wan_rext (u:real^3->real^K))` THEN
    REWRITE_TAC[wan_w12; LSPACE_ALT; IN_ELIM_THM] THEN SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DROP_VSUM; o_DEF]);;


(* ========================================================================= *)
(* The G-energy on a cone over a stereographic image, pulled back to the     *)
(* slab {1/2 < x3 < 2} by wan_nch.                                           *)
(* ========================================================================= *)

let cmr_pg = new_definition
 `cmr_pg (G:real^K->real^K^K) (u:real^3->real^K) (x:real^3) =
    wan_s2h u 1 x dot (G(u(stereo2_n_inv(vector[x$1; x$2]))) ** wan_s2h u 1 x) +
    wan_s2h u 2 x dot (G(u(stereo2_n_inv(vector[x$1; x$2]))) ** wan_s2h u 2 x) +
    wan_nchj x *
    (wan_s2h u 3 x dot (G(u(stereo2_n_inv(vector[x$1; x$2]))) ** wan_s2h u 3 x))`;;

let CMR_CONE_STEREO = prove
 (`!(D:real^2->bool).
     cmr_cone (IMAGE stereo2_n_inv D) SUBSET
       {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} /\
     (!x:real^3. &1 / &2 < x$3 /\ x$3 < &2
                 ==> (wan_nch x IN cmr_cone (IMAGE stereo2_n_inv D) <=>
                      vector[x$1; x$2] IN D))`,
  GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; cmr_cone; IN_ELIM_THM; IN_IMAGE; wan_shell] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `y:real^2` WAN_STEREO_THIRD_LT1) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3)$3 = norm z * (inv(norm z) * z$3)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (x:real^3)$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(CONJUNCT1 WAN_NCH_INV) THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[cmr_cone; IN_ELIM_THM; wan_shell] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WAN_NCH_NORM; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `stereo2_n`) THEN
    REWRITE_TAC[STEX_STEREO2_N_RIGHT] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN EXISTS_TAC `vector[(x:real^3)$1; x$2]:real^2` THEN ASM_REWRITE_TAC[]]);;

let CMR_NCH_PG = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) x.
     (!z. transp(G z) = G z) /\ &0 < x$3
     ==> wan_nchj x * cmr_dens G u (wan_nch x) = cmr_pg G u x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real^3` WAN_NCH_ORTHO_HYP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real^3` WAN_NCHJ_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`\i. frechet_derivative wan_nch (at (x:real^3)) (basis i)`;
                 `\j. wan_wd wan_shell j (wan_rext (u:real^3->real^K)) (wan_nch x)`;
                 `(G:real^K->real^K^K)(u(stereo2_n_inv(vector[(x:real^3)$1; x$2])))`]
                CMR_PARSEVAL3_G)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    REWRITE_TAC[cmr_pg; cmr_dens] THEN ASM_SIMP_TAC[WAN_REXT_NCH] THEN
    REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[SUM_3; wan_s2h] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < wan_nchj x` THEN CONV_TAC REAL_FIELD);;

let CMR_PULL_G = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) Lam D.
     wan_s2_w12 u /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z. transp(G z) = G z) /\
     (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2) /\
     lebesgue_measurable(cmr_cone (IMAGE stereo2_n_inv D))
     ==> (\x. if vector[x$1; x$2] IN D then lift(cmr_pg G u x) else vec 0)
           absolutely_integrable_on {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
         integral (cmr_cone (IMAGE stereo2_n_inv D)) (\z. lift(cmr_dens G u z)) =
         integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
           (\x. if vector[x$1; x$2] IN D then lift(cmr_pg G u x) else vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Sh = {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}` THEN
  MP_TAC(SPEC `D:real^2->bool` CMR_CONE_STEREO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MEM")) THEN
  SUBGOAL_THEN `cmr_cone (IMAGE stereo2_n_inv (D:real^2->bool)) SUBSET wan_shell`
  ASSUME_TAC THENL [REWRITE_TAC[cmr_cone; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`;
                 `cmr_cone (IMAGE stereo2_n_inv (D:real^2->bool))`] CMR_DENS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `q = \z:real^3. if z IN cmr_cone (IMAGE stereo2_n_inv (D:real^2->bool))
                   then lift(cmr_dens (G:real^K->real^K^K) (u:real^3->real^K) z) else vec 0` THEN
  SUBGOAL_THEN `(q:real^3->real^1) absolutely_integrable_on Sh` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_INTER] THEN
    SUBGOAL_THEN `cmr_cone (IMAGE stereo2_n_inv (D:real^2->bool)) INTER Sh =
                  cmr_cone (IMAGE stereo2_n_inv D)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (cmr_cone (IMAGE stereo2_n_inv (D:real^2->bool)))
             (\z. lift(cmr_dens (G:real^K->real^K^K) (u:real^3->real^K) z)) =
    integral Sh (q:real^3->real^1)`
  SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_RESTRICT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `q:real^3->real^1` WAN_NCH_COV) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^3. x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
               ==> wan_nchj x % (q:real^3->real^1)(wan_nch x) =
                   (if vector[x$1; x$2] IN (D:real^2->bool)
                    then lift(cmr_pg (G:real^K->real^K^K) (u:real^3->real^K) x) else vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    EXPAND_TAC "q" THEN
    USE_THEN "MEM" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ
      (ASSUME `&1 / &2 < (x:real^3)$3`) (ASSUME `(x:real^3)$3 < &2`))]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN MATCH_MP_TAC CMR_NCH_PG THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC `\x:real^3. wan_nchj x % (q:real^3->real^1)(wan_nch x)` THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]]);;


(* ========================================================================= *)
(* The transport lemma in the north chart: the S^2 G-energy on the           *)
(* stereographic image of an open planar set D is half the planar            *)
(* G-Dirichlet integral of u o stereo2_n_inv on D (a G-weighted, localized   *)
(* form of WAN_S2_STEREO's energy clause, with the slab chart wan_nch).      *)
(* ========================================================================= *)

let CMR_WD_D = prove
 (`!(w:real^2->real^K) (v:real^2->real^K) D i.
     open D /\ wan_wpd (:real^2) i w v /\ v IN lspace (:real^2) (&2)
     ==> negligible {y | y IN D /\ ~(wan_wd D i w y = v y)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^2->real^K) IN lspace D (&2) /\ wan_wpd D i (w:real^2->real^K) v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; SUBSET_UNIV];
      MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_wd D i (w:real^2->real^K) IN lspace D (&2) /\
                wan_wpd D i w (wan_wd D i w)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_wd] THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `v:real^2->real^K` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_WPD_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `w:real^2->real^K`] THEN ASM_REWRITE_TAC[ETA_AX]);;

let CMR_CONE_STEREO_OPEN = prove
 (`!D:real^2->bool. open D ==> open(cmr_cone (IMAGE stereo2_n_inv D))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Sh = {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}` THEN
  SUBGOAL_THEN
   `cmr_cone (IMAGE stereo2_n_inv (D:real^2->bool)) =
    {z:real^3 | z IN Sh /\
                (\z. vector[(wan_nchi z)$1; (wan_nchi z)$2]:real^2) z IN D}`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `D:real^2->bool` CMR_CONE_STEREO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MEM")) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    ASM_CASES_TAC `(z:real^3) IN Sh` THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(CONJUNCT2 WAN_NCH_INV) THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
      UNDISCH_TAC `(z:real^3) IN Sh` THEN EXPAND_TAC "Sh" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "MEM" (fun th -> MP_TAC(MATCH_MP th (CONJ
        (ASSUME `&1 / &2 < wan_nchi z$3`) (ASSUME `wan_nchi z$3 < &2`)))) THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "Sh" THEN REWRITE_TAC[WAN_NCH_OPEN]] THEN
  SUBGOAL_THEN `(\z:real^3. vector[(wan_nchi z)$1; (wan_nchi z)$2]:real^2) =
                (\x:real^3. vector[x$1; x$2]:real^2) o wan_nchi` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `1` THEN
    EXPAND_TAC "Sh" THEN REWRITE_TAC[WAN_NCH_FACTS];
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[WAN_PROJ3_LINEAR]]);;


(* ========================================================================= *)
(* Measurability of G-quadratic densities, integrals over the                *)
(* slab of functions of (x1,x2), and the transport lemma CMR_S2_GLOC.       *)
(* ========================================================================= *)

let CMR_SLAB_PROJ = prove
 (`!(Fd:real^2->real^1).
     Fd absolutely_integrable_on (:real^2)
     ==> (\x:real^3. Fd(vector[x$1; x$2])) absolutely_integrable_on
           {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
         integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} (\x. Fd(vector[x$1; x$2])) =
         (&3 / &2) % integral (:real^2) Fd`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Fd:real^2->real^1`;
                 `\r:real^1. if &1 / &2 < drop r /\ drop r < &2 then &1 else &0`]
                WAN_ABS_INT3_PROD) THEN
  MP_TAC(SPECL [`&1 / &2`; `&2`] WAN_INTERVAL1_INDICATOR_ABS) THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 < &2`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^3. (if &1 / &2 < x$3 /\ x$3 < &2 then &1 else &0) %
                (Fd:real^2->real^1)(vector[x$1; x$2])) =
    (\x. if x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} then Fd(vector[x$1; x$2]) else vec 0)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC LAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN ASM_REWRITE_TAC[]]);;

let CMR_S2_GLOC = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) Lam D.
     wan_s2_w12 u /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z. transp(G z) = G z) /\
     (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2) /\
     open D
     ==> cmr_sen_on G u (IMAGE stereo2_n_inv D) =
         wan_gdir D G (\y. u(stereo2_n_inv y)) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&1 / &2`; `&2`] WAN_SLAB_PSI) THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 < &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^1->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `v = \i (y:real^2). integral (:real^1)
          (\r. (psi:real^1->real) r %
               wan_s2h (u:real^3->real^K) i (vector[y$1; y$2; drop r]))` THEN
  SUBGOAL_THEN
   `wan_lloc (:real^2) (\y. (u:real^3->real^K)(stereo2_n_inv y)) /\
    !i. i = 1 \/ i = 2
        ==> wan_wpd (:real^2) i (\y. u(stereo2_n_inv y)) ((v:num->real^2->real^K) i) /\
            wan_lloc (:real^2) (v i) /\
            negligible {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                                   ~(wan_s2h u i x = v i (vector[x$1; x$2]))}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`u:real^3->real^K`; `psi:real^1->real`; `1`] WAN_S2_A_SLICE_I) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`u:real^3->real^K`; `psi:real^1->real`; `i:num`] WAN_S2_A_SLICE_I) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM wan_s2h] THEN
    EXPAND_TAC "v" THEN REWRITE_TAC[VECTOR_2] THEN
    REWRITE_TAC[wan_wpd] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `u:real^3->real^K` WAN_S2_A_VERT) THEN
  ASM_REWRITE_TAC[GSYM wan_s2h] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `v:num->real^2->real^K`] WAN_S2_A_ENERGY) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `w = \y:real^2. (u:real^3->real^K)(stereo2_n_inv y)` THEN
  SUBGOAL_THEN `(w:real^2->real^K) measurable_on (:real^2) /\
                (v:num->real^2->real^K) 1 measurable_on (:real^2) /\
                v 2 measurable_on (:real^2)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC WAN_LLOC_MEASURABLE THEN REWRITE_TAC[OPEN_UNIV] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "w" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the planar density *)
  ABBREV_TAC
   `Fd = \y:real^2. if y IN D
                    then lift((v:num->real^2->real^K) 1 y dot
                              ((G:real^K->real^K^K)((w:real^2->real^K) y) ** v 1 y) +
                              v 2 y dot (G(w y) ** v 2 y))
                    else vec 0` THEN
  SUBGOAL_THEN
   `!i. i = 1 \/ i = 2
        ==> (\y. lift((v:num->real^2->real^K) i y dot
                      ((G:real^K->real^K^K)((w:real^2->real^K) y) ** v i y)))
            absolutely_integrable_on (:real^2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMR_GQUAD_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fd:real^2->real^1) absolutely_integrable_on (:real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "Fd" THEN REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_OPEN] THEN
    REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  (* the S^2 side *)
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`; `D:real^2->bool`]
    CMR_PULL_G) THEN
  ASM_SIMP_TAC[CMR_CONE_STEREO_OPEN; LEBESGUE_MEASURABLE_OPEN] THEN STRIP_TAC THEN
  REWRITE_TAC[cmr_sen_on] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
      (\x. if vector[x$1; x$2] IN (D:real^2->bool)
           then lift(cmr_pg (G:real^K->real^K^K) (u:real^3->real^K) x) else vec 0) =
    integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} (\x. (Fd:real^2->real^1)(vector[x$1; x$2]))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC
     `{x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                  ~(wan_s2h (u:real^3->real^K) 1 x = (v:num->real^2->real^K) 1 (vector[x$1; x$2]))} UNION
      {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                  ~(wan_s2h u 2 x = v 2 (vector[x$1; x$2]))} UNION
      {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\ ~(wan_s2h u 3 x = vec 0)}` THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
    STRIP_TAC THEN EXPAND_TAC "Fd" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[cmr_pg; LIFT_EQ] THEN EXPAND_TAC "w" THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `Fd:real^2->real^1` CMR_SLAB_PROJ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[DROP_CMUL] THEN
  SUBGOAL_THEN
   `drop(integral (:real^2) (Fd:real^2->real^1)) =
    wan_gdir D (G:real^K->real^K^K) (\y. (u:real^3->real^K)(stereo2_n_inv y))`
  SUBST1_TAC THENL
   [ALL_TAC; EXPAND_TAC "w" THEN REAL_ARITH_TAC] THEN
  REWRITE_TAC[wan_gdir; DIMINDEX_2; SUM_2] THEN
  SUBGOAL_THEN
   `!i. i = 1 \/ i = 2
        ==> integral D (\x. lift(wan_wd D i (\y. (u:real^3->real^K)(stereo2_n_inv y)) x dot
                                 ((G:real^K->real^K^K)(u(stereo2_n_inv x)) **
                                  wan_wd D i (\y. u(stereo2_n_inv y)) x))) =
            integral (:real^2)
              (\y. if y IN D then lift((v:num->real^2->real^K) i y dot
                                       (G((w:real^2->real^K) y) ** v i y))
                   else vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{y:real^2 | y IN D /\
                  ~(wan_wd D i (\y. (u:real^3->real^K)(stereo2_n_inv y)) y =
                    (v:num->real^2->real^K) i y)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_WD_D THEN REWRITE_TAC[ETA_AX] THEN
      FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
      EXPAND_TAC "w" THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM DROP_ADD] THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) INTEGRAL_ADD o rand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_OPEN];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN EXPAND_TAC "Fd" THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[LIFT_ADD; VECTOR_ADD_LID]);;


(* ========================================================================= *)
(* Rotation invariance of S^2 W^{1,2}, of the weak partials of               *)
(* radial extensions and of the G-energy on sets of directions.            *)
(* ========================================================================= *)

let CMR_LINEAR_FRECHET = prove
 (`!(Q:real^N^N) x. frechet_derivative (\z. Q ** z) (at x) = (\z. Q ** z)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let CMR_ROT_REXT = prove
 (`!(Q:real^3^3) (u:real^3->real^K) z.
     orthogonal_matrix Q
     ==> wan_rext (\y. u(Q ** y)) z = wan_rext u (Q ** z) /\
         (z IN wan_shell <=> Q ** z IN wan_shell)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[wan_rext; wan_shell; IN_ELIM_THM; ORTHOGONAL_MATRIX_NORM;
               MATRIX_VECTOR_MUL_RMUL]);;

let CMR_ROT_FACTS = prove
 (`!(Q:real^3^3) (u:real^3->real^K).
     orthogonal_matrix Q /\ wan_s2_w12 u
     ==> wan_s2_w12 (\y. u(Q ** y)) /\
         !i. 1 <= i /\ i <= 3
             ==> wan_wpd wan_shell i (wan_rext (\y. u(Q ** y)))
                   (\z. vsum(1..3) (\j. (Q ** basis i)$j %
                                        wan_wd wan_shell j (wan_rext u) (Q ** z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wan_s2_w12] THEN
  SUBGOAL_THEN `wan_rext (\y. (u:real^3->real^K)(Q ** y)) = (\z. wan_rext u ((Q:real^3^3) ** z))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[FUN_EQ_THM; CMR_ROT_REXT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:3)`; `(:K)`] WAN_W12_DIFFEO) THEN REWRITE_TAC[WAN_W12_DIFFEO_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`wan_shell`; `wan_shell`; `\z:real^3. (Q:real^3^3) ** z`;
                             `\z:real^3. transp(Q:real^3^3) ** z`;
                             `wan_rext (u:real^3->real^K)`]) THEN
  REWRITE_TAC[CMR_LINEAR_FRECHET; DIMINDEX_3] THEN ANTS_TAC THENL
   [REWRITE_TAC[CMT_SHELL_OPEN] THEN
    SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; CMT_SHELL_OPEN;
             MATRIX_VECTOR_MUL_LINEAR] THEN
    UNDISCH_TAC `orthogonal_matrix(Q:real^3^3)` THEN
    REWRITE_TAC[orthogonal_matrix] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`Q:real^3^3`; `u:real^3->real^K`; `x:real^3`] CMR_ROT_REXT) THEN
      ASM_REWRITE_TAC[orthogonal_matrix] THEN SIMP_TAC[];
      GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`transp(Q:real^3^3)`; `u:real^3->real^K`; `y:real^3`] CMR_ROT_REXT) THEN
      ASM_REWRITE_TAC[orthogonal_matrix; TRANSP_TRANSP] THEN SIMP_TAC[];
      EXISTS_TAC `norm(vectorize(Q:real^3^3))` THEN
      REWRITE_TAC[ONORM_LE_NORM_VECTORIZE];
      EXISTS_TAC `norm(vectorize(transp(Q:real^3^3)))` THEN
      REWRITE_TAC[ONORM_LE_NORM_VECTORIZE];
      UNDISCH_TAC `wan_s2_w12 (u:real^3->real^K)` THEN REWRITE_TAC[wan_s2_w12]];
    ALL_TAC] THEN
  SIMP_TAC[]);;

let CMR_ROT_SHELL = prove
 (`!(Q:real^3^3) z. orthogonal_matrix Q ==> (Q ** z IN wan_shell <=> z IN wan_shell)`,
  SIMP_TAC[wan_shell; IN_ELIM_THM; ORTHOGONAL_MATRIX_NORM]);;

let CMR_ROT_CONE = prove
 (`!(Q:real^3^3) E.
     orthogonal_matrix Q
     ==> IMAGE (\z. Q ** z) (cmr_cone E) = cmr_cone (IMAGE (\z. Q ** z) E)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [orthogonal_matrix]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; cmr_cone; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[CMR_ROT_SHELL];
      EXISTS_TAC `inv(norm(z:real^3)) % z` THEN
      ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM; MATRIX_VECTOR_MUL_RMUL]];
    STRIP_TAC THEN EXISTS_TAC `transp(Q:real^3^3) ** w` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID] THEN
    SUBGOAL_THEN `orthogonal_matrix(transp(Q:real^3^3))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[orthogonal_matrix; TRANSP_TRANSP]; ALL_TAC] THEN
    ASM_SIMP_TAC[CMR_ROT_SHELL; ORTHOGONAL_MATRIX_NORM; GSYM MATRIX_VECTOR_MUL_RMUL] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]]);;

let CMR_ROT_SEN = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) (Q:real^3^3) Lam E.
     orthogonal_matrix Q /\ wan_s2_w12 u /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z. transp(G z) = G z) /\
     (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2) /\
     lebesgue_measurable(cmr_cone E)
     ==> cmr_sen_on G (\y. u(Q ** y)) E = cmr_sen_on G u (IMAGE (\y. Q ** y) E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Q:real^3^3`; `u:real^3->real^K`] CMR_ROT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "WPD")) THEN
  SUBGOAL_THEN `cmr_cone (E:real^3->bool) SUBSET wan_shell` ASSUME_TAC THENL
   [REWRITE_TAC[cmr_cone; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 3
        ==> negligible {z | z IN wan_shell /\
                            ~(wan_wd wan_shell i (wan_rext (\y. (u:real^3->real^K)(Q ** y))) z =
                              vsum(1..3) (\j. ((Q:real^3^3) ** basis i)$j %
                                              wan_wd wan_shell j (wan_rext u) (Q ** z)))}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WD_UNIQUE THEN
    REWRITE_TAC[CMT_SHELL_OPEN; DIMINDEX_3] THEN ASM_REWRITE_TAC[GSYM wan_s2_w12] THEN
    USE_THEN "WPD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN wan_shell /\
        (!i. 1 <= i /\ i <= 3
             ==> wan_wd wan_shell i (wan_rext (\y. (u:real^3->real^K)(Q ** y))) z =
                 vsum(1..3) (\j. ((Q:real^3^3) ** basis i)$j %
                                 wan_wd wan_shell j (wan_rext u) (Q ** z)))
        ==> cmr_dens (G:real^K->real^K^K) (\y. u(Q ** y)) z = cmr_dens G u (Q ** z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_dens] THEN
    ASM_SIMP_TAC[CMR_ROT_REXT] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum(1..3) (\i. vsum(1..3) (\j. ((Q:real^3^3) ** basis i)$j %
                                      wan_wd wan_shell j (wan_rext (u:real^3->real^K)) (Q ** z)) dot
                     ((G:real^K->real^K^K)(wan_rext u (Q ** z)) **
                      vsum(1..3) (\j. (Q ** basis i)$j % wan_wd wan_shell j (wan_rext u) (Q ** z))))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL [`\i. (Q:real^3^3) ** basis i`;
                             `\j. wan_wd wan_shell j (wan_rext (u:real^3->real^K))
                                    ((Q:real^3^3) ** (z:real^3))`;
                             `(G:real^K->real^K^K)(wan_rext (u:real^3->real^K)
                                                     ((Q:real^3^3) ** (z:real^3)))`]
                            CMR_PARSEVAL3_G)) THEN
    SUBGOAL_THEN `!i k. ((Q:real^3^3) ** basis i) dot (Q ** basis k) = (basis i:real^3) dot (basis k:real^3)`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      UNDISCH_TAC `orthogonal_matrix(Q:real^3^3)` THEN
      REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSFORMATION; orthogonal_transformation] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_3; ARITH; SUM_3; REAL_DIV_1; REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[cmr_sen_on] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`;
                 `cmr_cone (IMAGE (\y. (Q:real^3^3) ** y) E)`] CMR_DENS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lebesgue_measurable (cmr_cone (IMAGE (\y. (Q:real^3^3) ** y) E)) /\
                cmr_cone (IMAGE (\y. Q ** y) E) SUBSET wan_shell`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[GSYM CMR_ROT_CONE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; LE_REFL];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`Q:real^3^3`; `u:real^3->real^K`; `z:real^3`] CMR_ROT_REXT) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    STRIP_TAC] THEN
  ASM_SIMP_TAC[GSYM CMR_ROT_CONE] THEN
  MP_TAC(ISPECL [`\z. lift(cmr_dens (G:real^K->real^K^K) (u:real^3->real^K) z)`;
                 `\z:real^3. (Q:real^3^3) ** z`; `cmr_cone (E:real^3->bool)`;
                 `integral (IMAGE (\z:real^3. (Q:real^3^3) ** z) (cmr_cone E))
                    (\z. lift(cmr_dens (G:real^K->real^K^K) (u:real^3->real^K) z))`]
                HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_LINEAR) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  SUBGOAL_THEN `abs(det(Q:real^3^3)) = &1` SUBST1_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN
  SUBGOAL_THEN
   `(\z. lift(cmr_dens (G:real^K->real^K^K) (u:real^3->real^K) z)) absolutely_integrable_on
    IMAGE (\z:real^3. (Q:real^3^3) ** z) (cmr_cone E)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[CMR_ROT_CONE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC
   `UNIONS {{z | z IN wan_shell /\
                 ~(wan_wd wan_shell i (wan_rext (\y. (u:real^3->real^K)(Q ** y))) z =
                   vsum(1..3) (\j. ((Q:real^3^3) ** basis i)$j %
                                   wan_wd wan_shell j (wan_rext u) (Q ** z)))} | i IN 1..3}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; IN_NUMSEG] THEN
  STRIP_TAC THEN REWRITE_TAC[LIFT_EQ] THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET]]);;


(* ========================================================================= *)
(* Cap energies in rotated charts, additivity, and the total                 *)
(* energy split along one cap.                                              *)
(* ========================================================================= *)

let CMR_GCOND = new_definition
 `CMR_GCOND (G:real^K->real^K^K) Lam <=>
    ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
    (!z. transp(G z) = G z) /\
    (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2)`;;

let CMR_CAP_EN = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) (Q:real^3^3) Lam D.
     orthogonal_matrix Q /\ wan_s2_w12 u /\ CMR_GCOND G Lam /\ open D
     ==> cmr_sen_on G u (IMAGE (cm_capmap Q) D) =
         wan_gdir D G (\y. u(cm_capmap Q y)) / &2`,
  REWRITE_TAC[CMR_GCOND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (cm_capmap Q) D =
                IMAGE (\y. (Q:real^3^3) ** y) (IMAGE stereo2_n_inv (D:real^2->bool))`
  SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_IMAGE; cm_capmap] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Q:real^3^3`; `Lam:real`;
                 `IMAGE stereo2_n_inv (D:real^2->bool)`] CMR_ROT_SEN) THEN
  ASM_SIMP_TAC[CMR_CONE_STEREO_OPEN; LEBESGUE_MEASURABLE_OPEN] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `\y. (u:real^3->real^K)((Q:real^3^3) ** y)`;
                 `Lam:real`; `D:real^2->bool`] CMR_S2_GLOC) THEN
  ASM_SIMP_TAC[CMR_ROT_FACTS] THEN REWRITE_TAC[cm_capmap]);;

let CMR_CONE_UNION = prove
 (`!E1 E2. cmr_cone(E1 UNION E2) = cmr_cone E1 UNION cmr_cone E2 /\
           (DISJOINT E1 E2 ==> DISJOINT (cmr_cone E1) (cmr_cone E2))`,
  REWRITE_TAC[cmr_cone] THEN SET_TAC[]);;

let CMR_SEN_ON_UNION = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) Lam E1 E2.
     wan_s2_w12 u /\ CMR_GCOND G Lam /\
     lebesgue_measurable(cmr_cone E1) /\ lebesgue_measurable(cmr_cone E2) /\ DISJOINT E1 E2
     ==> cmr_sen_on G u (E1 UNION E2) = cmr_sen_on G u E1 + cmr_sen_on G u E2`,
  REWRITE_TAC[CMR_GCOND] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[cmr_sen_on; CMR_CONE_UNION] THEN
  REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB; GSYM DROP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_UNION THEN
  SUBGOAL_THEN `!E. cmr_cone E SUBSET wan_shell` ASSUME_TAC THENL
   [REWRITE_TAC[cmr_cone; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`; `cmr_cone E1`]
      CMR_DENS_FACTS) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`; `cmr_cone E2`]
      CMR_DENS_FACTS) THEN ASM_SIMP_TAC[];
    MP_TAC(SPECL [`E1:real^3->bool`; `E2:real^3->bool`] CMR_CONE_UNION) THEN
    ASM_REWRITE_TAC[DISJOINT] THEN SIMP_TAC[NEGLIGIBLE_EMPTY]]);;

let CMR_CONE_POINT_NEGLIGIBLE = prove
 (`!p:real^3. negligible(cmr_cone {p})`,
  GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `dim(span {p:real^3})` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIM_SUBSET THEN REWRITE_TAC[SUBSET; cmr_cone; IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `z:real^3 = norm z % p` SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      UNDISCH_TAC `(z:real^3) IN wan_shell` THEN REWRITE_TAC[wan_shell; IN_ELIM_THM] THEN
      STRIP_TAC THEN SUBGOAL_THEN `~(norm(z:real^3) = &0)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID]];
      MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_SING]];
    REWRITE_TAC[DIM_SPAN; DIM_SING; DIMINDEX_3] THEN COND_CASES_TAC THEN ARITH_TAC]);;


(* ========================================================================= *)
(* The rotated stereographic charts cm_capmap Q, the total                   *)
(* energy in one chart, and the planar split along a disc.                  *)
(* ========================================================================= *)

let CMR_CAPMAP_FACTS = prove
 (`!(Q:real^3^3).
     orthogonal_matrix Q
     ==> (!y. cm_capmap Q y IN sphere(vec 0,&1) /\ ~(cm_capmap Q y = Q ** basis 3)) /\
         (!y. cmr_chart Q (cm_capmap Q y) = y) /\
         (!x. x IN sphere(vec 0,&1) /\ ~(x = Q ** basis 3)
              ==> cm_capmap Q (cmr_chart Q x) = x) /\
         IMAGE (cm_capmap Q) (:real^2) = sphere(vec 0,&1) DELETE (Q ** basis 3)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [orthogonal_matrix]) THEN
  SUBGOAL_THEN `!y. cm_capmap Q y IN sphere(vec 0:real^3,&1) /\ ~(cm_capmap Q y = Q ** basis 3)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[cm_capmap; IN_SPHERE_0] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM] THEN
    MP_TAC(ISPEC `y:real^2` STEX_STEREO2_N_INV_IN) THEN
    REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. transp(Q:real^3^3) ** v`) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. cmr_chart Q (cm_capmap Q y) = y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[cmr_chart; cm_capmap; MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID;
                    STEX_STEREO2_N_RIGHT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN sphere(vec 0:real^3,&1) /\ ~(x = Q ** basis 3)
                    ==> cm_capmap Q (cmr_chart Q x) = x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_chart; cm_capmap] THEN
    SUBGOAL_THEN `stereo2_n_inv(stereo2_n(transp(Q:real^3^3) ** x)) = transp Q ** x`
    SUBST1_TAC THENL
     [MATCH_MP_TAC STEX_STEREO2_N_LEFT THEN REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `norm(x:real^3)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC ORTHOGONAL_MATRIX_NORM THEN
          ASM_REWRITE_TAC[orthogonal_matrix; TRANSP_TRANSP];
          ASM_MESON_TAC[IN_SPHERE_0]];
        DISCH_TAC THEN UNDISCH_TAC `~(x:real^3 = (Q:real^3^3) ** basis 3)` THEN
        FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. (Q:real^3^3) ** v`) THEN
        ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]];
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_DELETE] THEN X_GEN_TAC `x:real^3` THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC THEN EXISTS_TAC `cmr_chart Q x` THEN
                ASM_SIMP_TAC[]]);;

let CMR_CAPMAP_CONE = prove
 (`!(Q:real^3^3) D.
     orthogonal_matrix Q /\ open D
     ==> lebesgue_measurable(cmr_cone (IMAGE (cm_capmap Q) D))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (cm_capmap Q) D =
                IMAGE (\y. (Q:real^3^3) ** y) (IMAGE stereo2_n_inv (D:real^2->bool))`
  SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_IMAGE; cm_capmap] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CMR_ROT_CONE] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_LINEAR; LE_REFL; CMR_CONE_STEREO_OPEN;
               LEBESGUE_MEASURABLE_OPEN]);;

let CMR_SEN_CHART = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) (Q:real^3^3) Lam.
     orthogonal_matrix Q /\ wan_s2_w12 u /\ CMR_GCOND G Lam
     ==> cm_sen G u = cmr_sen_on G u (IMAGE (cm_capmap Q) (:real^2)) /\
         cm_sen G u = wan_gdir (:real^2) G (\y. u(cm_capmap Q y)) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[] `(a:real) = b /\ b = c ==> a = b /\ a = c`) THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CMR_CAP_EN THEN EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[OPEN_UNIV]] THEN
  UNDISCH_TAC `CMR_GCOND (G:real^K->real^K^K) Lam` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[CMR_GCOND] th)) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_DENS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(SPEC `Q:real^3^3` CMR_CAPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) =
                IMAGE (cm_capmap Q) (:real^2) UNION {Q ** basis 3}` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE `(a:real^3) IN s ==> s = (s DELETE a) UNION {a}`) THEN
    REWRITE_TAC[IN_SPHERE_0] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM; NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`;
                 `IMAGE (cm_capmap Q) (:real^2)`; `{(Q:real^3^3) ** basis 3}`]
    CMR_SEN_ON_UNION) THEN
  ASM_SIMP_TAC[CMR_CAPMAP_CONE; OPEN_UNIV; CMR_CONE_POINT_NEGLIGIBLE;
               NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a + b = a <=> b = &0`; cmr_sen_on] THEN
  SIMP_TAC[INTEGRAL_ON_NEGLIGIBLE; CMR_CONE_POINT_NEGLIGIBLE; DROP_VEC] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The planar G-Dirichlet integral split along a disc, and the               *)
(* S^2 energy split along a cap (inside, outside; the circle and the pole  *)
(* carry no energy).                                                        *)
(* ========================================================================= *)

let CMR_GDIR_SPLIT = prove
 (`!(G:real^K->real^K^K) (v:real^2->real^K) Lam c r.
     CMR_GCOND G Lam /\ wan_lloc (:real^2) v /\
     (!i. 1 <= i /\ i <= 2 ==> ?g. g IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i v g)
     ==> wan_gdir (:real^2) G v =
         wan_gdir (ball(c,r)) G v + wan_gdir ((:real^2) DIFF cball(c,r)) G v`,
  REWRITE_TAC[CMR_GCOND] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^2->real^K) measurable_on (:real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_MEASURABLE THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> wan_wd (:real^2) i (v:real^2->real^K) IN lspace (:real^2) (&2) /\
            wan_wpd (:real^2) i v (wan_wd (:real^2) i v)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wan_wd] THEN CONV_TAC SELECT_CONV THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i D. 1 <= i /\ i <= 2 /\ open D
          ==> integral D (\x. lift(wan_wd D i (v:real^2->real^K) x dot
                                   ((G:real^K->real^K^K)(v x) ** wan_wd D i v x))) =
              integral D (\x. lift(wan_wd (:real^2) i v x dot
                                   (G(v x) ** wan_wd (:real^2) i v x)))`
  (LABEL_TAC "WDD") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN D /\ ~(wan_wd D i (v:real^2->real^K) x = wan_wd (:real^2) i v x)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_WD_D THEN REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(wan_wd (:real^2) i (v:real^2->real^K) x dot
                      ((G:real^K->real^K^K)(v x) ** wan_wd (:real^2) i v x)))
            absolutely_integrable_on (:real^2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMR_GQUAD_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[wan_gdir; DIMINDEX_2; SUM_2] THEN
  USE_THEN "WDD" (fun th ->
    MP_TAC(SPECL [`1`; `ball(c:real^2,r)`] th) THEN MP_TAC(SPECL [`2`; `ball(c:real^2,r)`] th) THEN
    MP_TAC(SPECL [`1`; `(:real^2) DIFF cball(c:real^2,r)`] th) THEN
    MP_TAC(SPECL [`2`; `(:real^2) DIFF cball(c:real^2,r)`] th)) THEN
  SUBGOAL_THEN `open((:real^2) DIFF cball(c:real^2,r))` (fun od ->
    REWRITE_TAC[ARITH; OPEN_BALL; od]) THENL
   [SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL]; ALL_TAC] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `!f:real^2->real^1. f absolutely_integrable_on (:real^2)
         ==> integral (:real^2) f =
             integral (ball(c,r)) f + integral ((:real^2) DIFF cball(c,r)) f`
  (fun th -> FIRST_ASSUM(fun ai ->
     MP_TAC(MATCH_MP th (MP (SPEC `1` ai) (ARITH_RULE `1 <= 1 /\ 1 <= 2`))) THEN
     MP_TAC(MATCH_MP th (MP (SPEC `2` ai) (ARITH_RULE `1 <= 2 /\ 2 <= 2`))))) THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `integral (ball(c:real^2,r)) (f:real^2->real^1) = integral (cball(c,r)) f`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `sphere(c:real^2,r)` THEN REWRITE_TAC[NEGLIGIBLE_SPHERE] THEN
      REWRITE_TAC[GSYM BALL_UNION_SPHERE] THEN SET_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
      [SET_RULE `(:real^2) = cball(c,r) UNION ((:real^2) DIFF cball(c,r))`] THEN
    MATCH_MP_TAC INTEGRAL_UNION THEN
    REWRITE_TAC[SET_RULE `(s:real^2->bool) INTER ((:real^2) DIFF s) = {}`; NEGLIGIBLE_EMPTY] THEN
    CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    SIMP_TAC[LEBESGUE_MEASURABLE_CLOSED; CLOSED_CBALL; LEBESGUE_MEASURABLE_OPEN;
             OPEN_DIFF; OPEN_UNIV];
    REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[DROP_ADD] THEN REAL_ARITH_TAC]);;

let CMR_SEN_SPLIT = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) (Q:real^3^3) Lam c r.
     orthogonal_matrix Q /\ wan_s2_w12 u /\ CMR_GCOND G Lam
     ==> cm_sen G u = wan_gdir (ball(c,r)) G (\y. u(cm_capmap Q y)) / &2 +
                      wan_gdir ((:real^2) DIFF cball(c,r)) G (\y. u(cm_capmap Q y)) / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Q:real^3^3`; `Lam:real`]
    CMR_SEN_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[REAL_ARITH `a / &2 = b / &2 + c / &2 <=> a = b + c`] THEN
  MATCH_MP_TAC CMR_GDIR_SPLIT THEN EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(:K)` WAN_S2_STEREO) THEN REWRITE_TAC[WAN_S2_STEREO_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `\y:real^3. (u:real^3->real^K)((Q:real^3^3) ** y)` o CONJUNCT1) THEN
  ASM_SIMP_TAC[CMR_ROT_FACTS] THEN REWRITE_TAC[cm_capmap; DIMINDEX_2] THEN SIMP_TAC[]);;

