(* ========================================================================= *)
(* pc_sch_surgb: the bottom surgery sphere. Given a collared Morse sphere    *)
(* S = g(S^2) and a pancake chart Theta of an innermost regular level circle *)
(* (pc_sch_vflow), the part of S below the slab closed by Theta(sch_cap1) is *)
(* the central sphere of a neck g1 equal to Theta o sch_cap_collar near the  *)
(* cap. The bottom side of the band on the parameter sphere is a disc by     *)
(* SCH_R2 in a stereographic chart; the sphere parametrization is glued from *)
(* that disc and the model collar, and the neck comes from                   *)
(* SCH5_NECK_FROM_TRANSVERSE.                                                *)
(* ========================================================================= *)

needs "src/pc_sch_capcol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A stereographic chart of the parameter sphere from a point                *)
(* p (an orthogonal map sends p to the north pole).                          *)
(* ------------------------------------------------------------------------- *)

let sch5b_st = new_definition
 `sch5b_st (R:real^3->real^3) (x:real^3) = stereo2_n(R x)`;;

let sch5b_sti = new_definition
 `sch5b_sti (Ri:real^3->real^3) (z:real^2) = Ri(stereo2_n_inv z)`;;

let SCH5B_ROTATION = prove
 (`!p:real^3. norm p = &1
              ==> ?R Ri. orthogonal_transformation R /\ orthogonal_transformation Ri /\
                         (!x. Ri(R x) = x) /\ (!y. R(Ri y) = y) /\ R p = basis 3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^3`; `basis 3:real^3`] ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
  ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `R:real^3->real^3` ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Ri:real^3->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`R:real^3->real^3`; `Ri:real^3->real^3`] THEN ASM_REWRITE_TAC[]);;

let SCH5B_ST_FACTS = prove
 (`!(R:real^3->real^3) Ri p.
     orthogonal_transformation R /\ orthogonal_transformation Ri /\
     (!x. Ri(R x) = x) /\ (!y. R(Ri y) = y) /\ R p = basis 3
     ==> (!x. x IN sphere(vec 0,&1) /\ ~(x = p) ==> sch5b_sti Ri (sch5b_st R x) = x) /\
         (!z. sch5b_st R (sch5b_sti Ri z) = z) /\
         (!z. sch5b_sti Ri z IN sphere(vec 0,&1) /\ ~(sch5b_sti Ri z = p)) /\
         open {x | (R x)$3 < &1} /\
         smooth_map_on {x | (R x)$3 < &1} (sch5b_st R) /\
         (!x. x IN sphere(vec 0,&1) /\ ~(x = p) ==> (R x)$3 < &1) /\
         smooth_map_on (:real^2) (sch5b_sti Ri) /\
         (!x. x IN sphere(vec 0,&1) /\ ~(x = p)
              ==> norm(sch5b_st R x) pow 2 = (&1 + (R x)$3) / (&1 - (R x)$3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(R:real^3->real^3) /\ linear(Ri:real^3->real^3)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1) /\ ~(x = p)
                           ==> (R:real^3->real^3) x IN sphere(vec 0,&1) DELETE basis 3`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; IN_DELETE] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION];
      UNDISCH_TAC `~(x:real^3 = p)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(MATCH_MP ORTHOGONAL_TRANSFORMATION_INJECTIVE
        (ASSUME `orthogonal_transformation (R:real^3->real^3)`)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sphere(vec 0,&1) ==> (Ri:real^3->real^3) y IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0] THEN ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  SUBGOAL_THEN `open {x:real^3 | ((R:real^3->real^3) x)$3 < &1}` ASSUME_TAC THENL
   [SUBGOAL_THEN `{x:real^3 | ((R:real^3->real^3) x)$3 < &1} =
                  {x | x IN (:real^3) /\ R x IN {y:real^3 | y$3 < &1}}`
    SUBST1_TAC THENL [REWRITE_TAC[IN_UNIV; IN_ELIM_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; OPEN_UNIV; OPEN_HALFSPACE_COMPONENT_LT];
    ALL_TAC] THEN
  REWRITE_TAC[sch5b_st; sch5b_sti] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `stereo2_n_inv(stereo2_n((R:real^3->real^3) x)) = R x` SUBST1_TAC THENL
     [MATCH_MP_TAC STEX_STEREO2_N_LEFT THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[STEX_STEREO2_N_RIGHT];
    GEN_TAC THEN MP_TAC(SPEC `z:real^2` STEX_STEREO2_N_INV_IN) THEN
    REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~(stereo2_n_inv z = basis 3:real^3)` THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `stereo2_n_inv z = (R:real^3->real^3)(Ri(stereo2_n_inv z))` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[ASSUME `(Ri:real^3->real^3)(stereo2_n_inv z) = p`;
                    ASSUME `(R:real^3->real^3) p = basis 3`]]];
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `sch5b_st (R:real^3->real^3) = stereo2_n o R` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; sch5b_st]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{y:real^3 | y$3 < &1}` THEN
    REWRITE_TAC[STEX_STEREO2_N_SMOOTH; OPEN_HALFSPACE_COMPONENT_LT] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      ASM_SIMP_TAC[GRGE_SMOOTH_LINEAR; OPEN_UNIV]];
    REPEAT STRIP_TAC THEN MP_TAC STEX_STEREO2_N_DOMAIN THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(R:real^3->real^3) x`) THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN `sch5b_sti (Ri:real^3->real^3) = Ri o stereo2_n_inv` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; sch5b_sti]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    ASM_SIMP_TAC[STEX_STEREO2_N_INV_SMOOTH; OPEN_UNIV; SUBSET_UNIV; GRGE_SMOOTH_LINEAR];
    REPEAT STRIP_TAC THEN MP_TAC(SPEC `(R:real^3->real^3) x` STEX_STEREO2_N_NORM2) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The pancake data, the radial profile hb of the bottom planar              *)
(* neck (hb(1) = -9/8) and the maps ell (annulus to the lateral cylinder)    *)
(* and elli (back).                                                          *)
(* ------------------------------------------------------------------------- *)

let sch5b_pancake = new_definition
 `sch5b_pancake (g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3)
                Theta' <=>
    sch_neck g g' /\ &0 < lam /\ sch_ball c c' /\
    diffeomorphism_on (sch5v_slab(&3 / &2)) (IMAGE Theta (sch5v_slab(&3 / &2))) Theta Theta' /\
    (!y. y IN sch5v_slab(&3 / &2) ==> (Theta y)$3 = a + lam * y$3) /\
    (!y. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 < &1 / &4
         ==> Theta y = sch5v_at (a + lam * y$3) (c(sch5v_pr y))) /\
    (!y. y IN sch5v_slab(&3 / &2)
         ==> (Theta y IN IMAGE g (sphere(vec 0,&1)) <=> y$1 pow 2 + y$2 pow 2 = &1))`;;

let sch5b_hb = new_definition
 `sch5b_hb (rho:real) = -- &1 + (rho pow 2 - &5 / &3) / (&2 * (rho pow 2 + &5 / &3))`;;

let sch5b_hbi = new_definition
 `sch5b_hbi (u:real) = sqrt((&5 / &3) * (&3 + &2 * u) / (-- &1 - &2 * u))`;;

let sch5b_ell = new_definition
 `sch5b_ell (w:real^2) = vector[w$1 / norm w; w$2 / norm w; sch5b_hb(norm w)]:real^3`;;

let sch5b_elli = new_definition
 `sch5b_elli (y:real^3) =
    (sch5b_hbi(y$3) / sqrt(y$1 pow 2 + y$2 pow 2)) % vector[y$1; y$2]:real^2`;;

let SCH5B_HB_FACTS = prove
 (`(!rho. &0 < rho ==> --(&3 / &2) < sch5b_hb rho /\ sch5b_hb rho < --(&1 / &2) /\
                       sch5b_hbi(sch5b_hb rho) = rho) /\
   (!u. --(&3 / &2) < u /\ u < --(&1 / &2)
        ==> &0 < sch5b_hbi u /\ sch5b_hb(sch5b_hbi u) = u) /\
   sch5b_hb(&1) = --(&9 / &8) /\
   (!rho rho'. &0 < rho /\ rho < rho' ==> sch5b_hb rho < sch5b_hb rho') /\
   (!rho. &1 / &2 < rho /\ rho < &2 ==> --(&11 / &8) < sch5b_hb rho /\ sch5b_hb rho < --(&3 / &4))`,
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `rho:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < rho pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    REWRITE_TAC[sch5b_hb] THEN
    SUBGOAL_THEN `&0 < &2 * (rho pow 2 + &5 / &3)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `--(&1 / &2) < x ==> --(&3 / &2) < -- &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x < &1 / &2 ==> -- &1 + x < --(&1 / &2)`) THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[sch5b_hbi] THEN
      SUBGOAL_THEN `(&5 / &3) * (&3 + &2 * (-- &1 + (rho pow 2 - &5 / &3) /
                     (&2 * (rho pow 2 + &5 / &3)))) /
                    (-- &1 - &2 * (-- &1 + (rho pow 2 - &5 / &3) / (&2 * (rho pow 2 + &5 / &3)))) =
                    rho pow 2` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < rho pow 2` THEN CONV_TAC REAL_FIELD;
        ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]]];
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (&5 / &3) * (&3 + &2 * u) / (-- &1 - &2 * u)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[sch5b_hbi; sch5b_hb] THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `--(&3 / &2) < u` THEN UNDISCH_TAC `u < --(&1 / &2)` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[sch5b_hb] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    REPEAT STRIP_TAC THEN REWRITE_TAC[sch5b_hb; REAL_LT_LADD] THEN
    SUBGOAL_THEN `rho pow 2 < rho' pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < rho pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < &2 * (x + &5 / &3)`;
                 REAL_ARITH `&0 < x /\ x < y ==> &0 < &2 * (y + &5 / &3)`] THEN
    REWRITE_TAC[real_div; REAL_ARITH `(a * inv b) * c = (a * c) * inv b`] THEN
    SUBGOAL_THEN `&0 < &2 * (rho' pow 2 + &5 / &3)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ] THEN
    REWRITE_TAC[REAL_ARITH `(a - b) * (&2 * (c + b)) < (c - b) * (&2 * (a + b)) <=>
                            &0 < &4 * b * (c - a)`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 / &4 < rho pow 2 /\ rho pow 2 < &4` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `(&1 / &2) pow 2 < rho pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
        SUBGOAL_THEN `rho pow 2 < &2 pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]];
      ALL_TAC] THEN
    REWRITE_TAC[sch5b_hb] THEN
    SUBGOAL_THEN `&0 < &2 * (rho pow 2 + &5 / &3)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `--(&3 / &8) < x ==> --(&11 / &8) < -- &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x < &1 / &4 ==> -- &1 + x < --(&3 / &4)`) THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]]);;

let SCH5B_ELL_BASIC = prove
 (`!w:real^2. ~(w = vec 0)
              ==> (sch5b_ell w)$1 pow 2 + (sch5b_ell w)$2 pow 2 = &1 /\
                  (sch5b_ell w)$3 = sch5b_hb(norm w) /\ sch5b_elli(sch5b_ell w) = w`,
  X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^2)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^2)$1 pow 2 + w$2 pow 2 = norm w pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[sch5b_ell; VECTOR_3] THEN
  SUBGOAL_THEN `((w:real^2)$1 / norm w) pow 2 + (w$2 / norm w) pow 2 = &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `(w:real^2)$1 pow 2 / norm w pow 2 + w$2 pow 2 / norm w pow 2 =
                  (w$1 pow 2 + w$2 pow 2) / norm w pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_DIV_REFL THEN
    ASM_SIMP_TAC[REAL_POW_NZ; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sch5b_elli; VECTOR_3; SQRT_1; REAL_DIV_1] THEN
  MP_TAC(CONJUNCT1 SCH5B_HB_FACTS) THEN DISCH_THEN(MP_TAC o SPEC `norm(w:real^2)`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  UNDISCH_TAC `&0 < norm(w:real^2)` THEN CONV_TAC REAL_FIELD);;

let SCH5B_ELLI_BASIC = prove
 (`!y:real^3. y$1 pow 2 + y$2 pow 2 = &1 /\ --(&3 / &2) < y$3 /\ y$3 < --(&1 / &2)
              ==> norm(sch5b_elli y) = sch5b_hbi(y$3) /\ ~(sch5b_elli y = vec 0) /\
                  sch5b_ell(sch5b_elli y) = y`,
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  MP_TAC(CONJUNCT1(CONJUNCT2 SCH5B_HB_FACTS)) THEN
  DISCH_THEN(MP_TAC o SPEC `(y:real^3)$3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch5b_elli y = sch5b_hbi((y:real^3)$3) % vector[y$1; y$2]:real^2`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[sch5b_elli; SQRT_1; REAL_DIV_1]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(vector[(y:real^3)$1; y$2]:real^2) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_1; DOT_2; VECTOR_2; GSYM REAL_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(sch5b_hbi((y:real^3)$3) % vector[y$1; y$2]:real^2) = sch5b_hbi(y$3)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `norm:real^2->real`) THEN ASM_REWRITE_TAC[NORM_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sch5b_ell; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_MUL_COMPONENT;
                  VECTOR_2] THEN
  UNDISCH_TAC `&0 < sch5b_hbi((y:real^3)$3)` THEN CONV_TAC REAL_FIELD);;

let SCH5B_ELL_IN_SLAB = prove
 (`!w:real^2. w IN annulus (&1 / &2) (&2)
              ==> ~(w = vec 0) /\ sch5b_ell w IN sch5v_slab(&3 / &2) /\
                  --(&11 / &8) < (sch5b_ell w)$3 /\ (sch5b_ell w)$3 < --(&3 / &4)`,
  X_GEN_TAC `w:real^2` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 SCH5B_HB_FACTS)))) THEN
  DISCH_THEN(MP_TAC o SPEC `norm(w:real^2)`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(w:real^2 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 / &2 < norm(vec 0:real^2)` THEN
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `w:real^2` SCH5B_ELL_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Smoothness of ell and elli; the band map beta = g' o Theta                *)
(* on the lateral cylinder of the pancake.                                   *)
(* ------------------------------------------------------------------------- *)

let SCH5B_ELL_SMOOTH = prove
 (`smooth_map_on {w:real^2 | ~(w = vec 0)} sch5b_ell`,
  SUBGOAL_THEN
   `sch5b_ell =
    (\w:real^2. vector[w$1 / norm w; w$2 / norm w;
                       -- &1 + (norm w pow 2 - &5 / &3) / (&2 * (norm w pow 2 + &5 / &3))]:real^3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; sch5b_ell; sch5b_hb]; ALL_TAC] THEN
  SUBGOAL_THEN `open {w:real^2 | ~(w = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_NONZERO]; ALL_TAC] THEN
  SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; NORM_EQ_0] THEN
  X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
  MP_TAC(SPEC `norm(w:real^2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let SCH5B_ELLI_SMOOTH = prove
 (`open {y:real^3 | &0 < y$1 pow 2 + y$2 pow 2 /\ --(&3 / &2) < y$3 /\ y$3 < --(&1 / &2)} /\
   smooth_map_on {y:real^3 | &0 < y$1 pow 2 + y$2 pow 2 /\ --(&3 / &2) < y$3 /\
                             y$3 < --(&1 / &2)} sch5b_elli`,
  SUBGOAL_THEN
   `open {y:real^3 | &0 < y$1 pow 2 + y$2 pow 2 /\ --(&3 / &2) < y$3 /\ y$3 < --(&1 / &2)}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `{y:real^3 | &0 < y$1 pow 2 + y$2 pow 2 /\ --(&3 / &2) < y$3 /\ y$3 < --(&1 / &2)} =
      {y | y IN {y:real^3 | y$3 > --(&3 / &2)} INTER {y | y$3 < --(&1 / &2)} /\
           &0 < y$1 pow 2 + y$2 pow 2}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; real_gt] THEN MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SCH5C_OPEN_POS THEN
    SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT] THEN
    SCH5C_SMOOTH_TAC THEN
    SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sch5b_elli =
    (\y:real^3. vector[sqrt((&5 / &3) * (&3 + &2 * y$3) / (-- &1 - &2 * y$3)) /
                       sqrt(y$1 pow 2 + y$2 pow 2) * y$1;
                       sqrt((&5 / &3) * (&3 + &2 * y$3) / (-- &1 - &2 * y$3)) /
                       sqrt(y$1 pow 2 + y$2 pow 2) * y$2]:real^2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; sch5b_elli; sch5b_hbi] THEN GEN_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
          [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
         ASM_REAL_ARITH_TAC]);;

(* The open set of the slab where the band map g' o Theta is smooth, and    *)
(* the open cylinder bands.                                                  *)

let sch5b_ub = new_definition
 `sch5b_ub (g:real^3->real^3) (Theta:real^3->real^3) =
    {y | y IN sch5v_slab(&3 / &2) /\ Theta y IN IMAGE g (annulus (&1 / &2) (&2))}`;;

let sch5b_band = new_definition
 `sch5b_band lo hi = {y:real^3 | y$1 pow 2 + y$2 pow 2 = &1 /\ lo < y$3 /\ y$3 < hi}`;;

let SCH5B_BETA_FACTS = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch5b_pancake g g' a lam c c' Theta Theta'
     ==> (!y. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1
              ==> g'(Theta y) IN sphere(vec 0,&1) /\ g(g'(Theta y)) = Theta y /\
                  y IN sch5b_ub g Theta) /\
         (!y y'. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1 /\
                 y' IN sch5v_slab(&3 / &2) /\ y'$1 pow 2 + y'$2 pow 2 = &1 /\
                 g'(Theta y) = g'(Theta y') ==> y = y') /\
         (!t. t IN sphere(vec 0,&1) /\ g t IN IMAGE Theta (sch5v_slab(&3 / &2))
              ==> Theta'(g t) IN sch5v_slab(&3 / &2) /\
                  (Theta'(g t))$1 pow 2 + (Theta'(g t))$2 pow 2 = &1 /\
                  Theta(Theta'(g t)) = g t /\ g'(Theta(Theta'(g t))) = t) /\
         open(sch5b_ub g Theta) /\ sch5b_ub g Theta SUBSET sch5v_slab(&3 / &2) /\
         smooth_map_on (sch5b_ub g Theta) (g' o Theta)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5b_pancake; sch_neck] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "T")
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S"))))))) THEN
  USE_THEN "G" (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) THEN
  USE_THEN "T" (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) THEN
  SUBGOAL_THEN `!y. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1
                    ==> (g':real^3->real^3)((Theta:real^3->real^3) y) IN sphere(vec 0,&1) /\
                        g(g'(Theta y)) = Theta y`
  (LABEL_TAC "B1") THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    USE_THEN "S" (fun th -> MP_TAC(MP (SPEC `y:real^3` th)
      (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`))) THEN
    REWRITE_TAC[ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(g':real^3->real^3)(g(t:real^3)) = t` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match [] `!x. x IN annulus (&1 / &2) (&2) ==> (g':real^3->real^3)(g x) = x`) (concl th))) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(sch5b_ub (g:real^3->real^3) (Theta:real^3->real^3))` ASSUME_TAC THENL
   [REWRITE_TAC[sch5b_ub] THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    USE_THEN "B1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
            (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)))) THEN
    ASM_REWRITE_TAC[sch5b_ub; IN_ELIM_THM; IN_IMAGE] THEN
    EXISTS_TAC `(g':real^3->real^3)((Theta:real^3->real^3) y)` THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
    MAP_EVERY X_GEN_TAC [`y:real^3`; `y':real^3`] THEN STRIP_TAC THEN
    USE_THEN "B1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
            (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)))) THEN
    USE_THEN "B1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `(y':real^3) IN sch5v_slab(&3 / &2)`)
            (ASSUME `(y':real^3)$1 pow 2 + y'$2 pow 2 = &1`)))) THEN
    SUBGOAL_THEN `(Theta:real^3->real^3) y = Theta y'` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `Theta':real^3->real^3`) THEN ASM_SIMP_TAC[];
    X_GEN_TAC `t:real^3` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(g:real^3->real^3) t IN IMAGE g (sphere(vec 0,&1))` ASSUME_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `t:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "S" (fun th -> MP_TAC(MP (SPEC `y:real^3` th)
        (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`))) THEN
      UNDISCH_TAC `(g:real^3->real^3) t = (Theta:real^3->real^3) y` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(g:real^3->real^3) t = (Theta:real^3->real^3) y` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match [] `!x. x IN annulus (&1 / &2) (&2) ==> (g':real^3->real^3)(g x) = x`) (concl th))) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
    REWRITE_TAC[sch5b_ub] THEN SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[sch5b_ub] THEN SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `sch5v_slab(&3 / &2)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[sch5b_ub] THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The bottom planar neck F_b w = st(g'(Theta(ell w))) in the                *)
(* stereographic chart from p_top = g'(Theta(1,0,4/3)), with inverse         *)
(* elli o Theta' o g o st^-1 on the open set sch5b_fbt.                      *)
(* ------------------------------------------------------------------------- *)

let sch5b_rot = new_definition
 `sch5b_rot (R:real^3->real^3) Ri (p:real^3) <=>
    orthogonal_transformation R /\ orthogonal_transformation Ri /\
    (!x. Ri(R x) = x) /\ (!y. R(Ri y) = y) /\ R p = basis 3`;;

let sch5b_eh = new_definition
 `sch5b_eh =
    {y:real^3 | &0 < y$1 pow 2 + y$2 pow 2 /\ --(&3 / &2) < y$3 /\ y$3 < --(&1 / &2)}`;;

let sch5b_fb = new_definition
 `sch5b_fb (R:real^3->real^3) (g':real^3->real^3) (Theta:real^3->real^3) (w:real^2) =
    sch5b_st R (g'(Theta(sch5b_ell w)))`;;

let sch5b_fbi = new_definition
 `sch5b_fbi (Ri:real^3->real^3) (g:real^3->real^3) (Theta':real^3->real^3) (z:real^2) =
    sch5b_elli(Theta'(g(sch5b_sti Ri z)))`;;

let sch5b_fbt = new_definition
 `sch5b_fbt (Ri:real^3->real^3) (g:real^3->real^3) (Theta:real^3->real^3) Theta' =
    {z:real^2 | g(sch5b_sti Ri z) IN IMAGE Theta (sch5v_slab(&3 / &2)) /\
                Theta'(g(sch5b_sti Ri z)) IN sch5b_eh /\
                sch5b_fbi Ri g Theta' z IN annulus (&1 / &2) (&2)}`;;

let SCH5B_PTOP = prove
 (`(vector[&1; &0; &4 / &3]:real^3) IN sch5v_slab(&3 / &2) /\
   (vector[&1; &0; &4 / &3]:real^3)$1 pow 2 + (vector[&1; &0; &4 / &3]:real^3)$2 pow 2 = &1 /\
   (vector[&1; &0; &4 / &3]:real^3)$3 = &4 / &3`,
  REWRITE_TAC[sch5v_slab; IN_ELIM_THM; VECTOR_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let SCH5B_ST_PTOP = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3])))
     ==> (!x. x IN sphere(vec 0,&1) /\ ~(x = g'(Theta(vector[&1; &0; &4 / &3])))
              ==> sch5b_sti Ri (sch5b_st R x) = x /\ (R x)$3 < &1) /\
         (!z. sch5b_st R (sch5b_sti Ri z) = z) /\
         (!z. sch5b_sti Ri z IN sphere(vec 0,&1) /\
              ~(sch5b_sti Ri z = g'(Theta(vector[&1; &0; &4 / &3])))) /\
         open {x | (R x)$3 < &1} /\ smooth_map_on {x | (R x)$3 < &1} (sch5b_st R) /\
         smooth_map_on (:real^2) (sch5b_sti Ri) /\
         (!x. x IN sphere(vec 0,&1) /\ ~(x = g'(Theta(vector[&1; &0; &4 / &3])))
              ==> norm(sch5b_st R x) pow 2 = (&1 + (R x)$3) / (&1 - (R x)$3)) /\
         g'(Theta(vector[&1; &0; &4 / &3])) IN sphere(vec 0,&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5b_rot] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`R:real^3->real^3`; `Ri:real^3->real^3`;
                 `(g':real^3->real^3)((Theta:real^3->real^3)(vector[&1; &0; &4 / &3]))`] SCH5B_ST_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCH5B_BETA_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `vector[&1; &0; &4 / &3]:real^3` o CONJUNCT1) THEN
  REWRITE_TAC[SCH5B_PTOP] THEN SIMP_TAC[]);;

let SCH5B_FB_VALUES = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri w.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3]))) /\
     w IN annulus (&1 / &2) (&2)
     ==> sch5b_ell w IN sch5b_ub g Theta /\
         g'(Theta(sch5b_ell w)) IN sphere(vec 0,&1) /\
         ~(g'(Theta(sch5b_ell w)) = g'(Theta(vector[&1; &0; &4 / &3]))) /\
         (R(g'(Theta(sch5b_ell w))))$3 < &1 /\
         sch5b_sti Ri (sch5b_fb R g' Theta w) = g'(Theta(sch5b_ell w)) /\
         g(sch5b_sti Ri (sch5b_fb R g' Theta w)) = Theta(sch5b_ell w) /\
         sch5b_fb R g' Theta w IN sch5b_fbt Ri g Theta Theta' /\
         sch5b_fbi Ri g Theta' (sch5b_fb R g' Theta w) = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `w:real^2` SCH5B_ELL_IN_SLAB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `w:real^2` SCH5B_ELL_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCH5B_BETA_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "B1") (CONJUNCTS_THEN2 (LABEL_TAC "B2") (LABEL_TAC "B3"))) THEN
  USE_THEN "B1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (CONJ (ASSUME `sch5b_ell w IN sch5v_slab(&3 / &2)`)
          (ASSUME `(sch5b_ell w)$1 pow 2 + (sch5b_ell w)$2 pow 2 = &1`)))) THEN
  SUBGOAL_THEN `~((g':real^3->real^3)((Theta:real^3->real^3)(sch5b_ell w)) =
                  g'(Theta(vector[&1; &0; &4 / &3])))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "B2" (MP_TAC o SPECL [`sch5b_ell w`; `vector[&1; &0; &4 / &3]:real^3`]) THEN
    REWRITE_TAC[SCH5B_PTOP; ASSUME `sch5b_ell w IN sch5v_slab(&3 / &2)`;
                ASSUME `(sch5b_ell w)$1 pow 2 + (sch5b_ell w)$2 pow 2 = &1`;
                ASSUME `(g':real^3->real^3)((Theta:real^3->real^3)(sch5b_ell w)) =
                        g'(Theta(vector[&1; &0; &4 / &3]))`] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\y:real^3. y$3`) THEN
    REWRITE_TAC[SCH5B_PTOP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_ST_PTOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "S1") (K ALL_TAC)) THEN
  USE_THEN "S1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (CONJ (ASSUME `(g':real^3->real^3)((Theta:real^3->real^3)(sch5b_ell w)) IN sphere(vec 0,&1)`)
          (ASSUME `~((g':real^3->real^3)((Theta:real^3->real^3)(sch5b_ell w)) =
                     g'(Theta(vector[&1; &0; &4 / &3])))`)))) THEN
  SUBGOAL_THEN `sch5b_sti Ri (sch5b_fb R g' Theta w) =
                (g':real^3->real^3)((Theta:real^3->real^3)(sch5b_ell w))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[sch5b_fb]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Theta':real^3->real^3)((Theta:real^3->real^3)(sch5b_ell w)) = sch5b_ell w`
  ASSUME_TAC THENL
   [UNDISCH_TAC `sch5b_pancake (g:real^3->real^3) g' a lam c c' Theta Theta'` THEN
    REWRITE_TAC[sch5b_pancake; diffeomorphism_on] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_fbi Ri g Theta' (sch5b_fb R g' Theta w) = w` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[sch5b_fbi]; ALL_TAC] THEN
  ASM_REWRITE_TAC[sch5b_fbt; IN_ELIM_THM; sch5b_eh] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `sch5b_ell w` THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SCH5B_FBT_VALUES = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri z.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3]))) /\
     z IN sch5b_fbt Ri g Theta Theta'
     ==> sch5b_fbi Ri g Theta' z IN annulus (&1 / &2) (&2) /\
         sch5b_fb R g' Theta (sch5b_fbi Ri g Theta' z) = z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5b_fbt; IN_ELIM_THM; sch5b_eh] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_ST_PTOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCH5B_BETA_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `sch5b_sti Ri z` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(Theta':real^3->real^3)(g(sch5b_sti Ri z))` SCH5B_ELLI_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[sch5b_fb; sch5b_fbi] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g':real^3->real^3)((g:real^3->real^3)(sch5b_sti Ri z)) = sch5b_sti Ri z`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let SCH5B_FB_IMAGE = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3])))
     ==> IMAGE (sch5b_fb R g' Theta) (annulus (&1 / &2) (&2)) = sch5b_fbt Ri g Theta Theta'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`;
                   `w:real^2`] SCH5B_FB_VALUES) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`;
                   `z:real^2`] SCH5B_FBT_VALUES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `sch5b_fbi Ri (g:real^3->real^3) Theta' z` THEN ASM_REWRITE_TAC[]]);;

let SCH5B_FBT_SMOOTH = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3])))
     ==> open(sch5b_fbt Ri g Theta Theta') /\
         smooth_map_on (sch5b_fbt Ri g Theta Theta') (sch5b_fbi Ri g Theta')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_ST_PTOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `sch5b_pancake (g:real^3->real^3) g' a lam c c' Theta Theta'` THEN
  REWRITE_TAC[sch5b_pancake; sch_neck; diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) ((g:real^3->real^3) o sch5b_sti Ri)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
    ALL_TAC] THEN
  ABBREV_TAC `T0 = {z:real^2 | z IN (:real^2) /\
                    ((g:real^3->real^3) o sch5b_sti Ri) z IN
                    IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))}` THEN
  SUBGOAL_THEN `open(T0:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on T0 ((Theta':real^3->real^3) o (g:real^3->real^3) o sch5b_sti Ri)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "T0" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  ABBREV_TAC `T1 = {z:real^2 | z IN T0 /\
                    ((Theta':real^3->real^3) o (g:real^3->real^3) o sch5b_sti Ri) z IN sch5b_eh}` THEN
  MP_TAC SCH5B_ELLI_SMOOTH THEN REWRITE_TAC[GSYM sch5b_eh] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(T1:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_fbi Ri g Theta' =
                sch5b_elli o (Theta':real^3->real^3) o (g:real^3->real^3) o sch5b_sti Ri`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; sch5b_fbi; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on T1 (sch5b_elli o (Theta':real^3->real^3) o (g:real^3->real^3) o
                                  sch5b_sti Ri)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `sch5b_eh` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "T1" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `T0:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "T1" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_fbt Ri g Theta Theta' =
                {z | z IN T1 /\ (sch5b_elli o (Theta':real^3->real^3) o (g:real^3->real^3) o
                                 sch5b_sti Ri) z IN annulus (&1 / &2) (&2)}` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["T1"; "T0"] THEN
    REWRITE_TAC[sch5b_fbt; sch5b_fbi; EXTENSION; IN_ELIM_THM; o_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_ANNULUS];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `T1:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]]);;

let SCH5B_FB_SMOOTH = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3])))
     ==> smooth_map_on (annulus (&1 / &2) (&2)) (sch5b_fb R g' Theta)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_ST_PTOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCH5B_BETA_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch5b_fb R g' Theta =
                sch5b_st R o ((g':real^3->real^3) o (Theta:real^3->real^3)) o sch5b_ell`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; sch5b_fb; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{x:real^3 | ((R:real^3->real^3) x)$3 < &1}` THEN
  ASM_REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`;
                   `w:real^2`] SCH5B_FB_VALUES) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `sch5b_ub g Theta` THEN
  ASM_REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`;
                   `w:real^2`] SCH5B_FB_VALUES) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{w:real^2 | ~(w = vec 0)}` THEN
    REWRITE_TAC[SCH5B_ELL_SMOOTH] THEN MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN
    REAL_ARITH_TAC]);;

let SCH5B_FB_NECK = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3])))
     ==> sch_neck (sch5b_fb R g' Theta) (sch5b_fbi Ri g Theta')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[sch_neck] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_FB_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_FBT_SMOOTH) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_FB_SMOOTH) THEN
  ASM_REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`;
                   `x:real^2`] SCH5B_FB_VALUES) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`;
                   `x:real^2`] SCH5B_FB_VALUES) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`;
                   `y:real^2`] SCH5B_FBT_VALUES) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`;
                   `y:real^2`] SCH5B_FBT_VALUES) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The band in the stereographic plane.  The cylinder bands are              *)
(* connected; B y = st(g'(Theta y)) is continuous and injective on the       *)
(* cylinder minus (1,0,4/3); the planar Jordan curve J = F_b(S^1) is the     *)
(* image of the circle at height -9/8; the band above it is unbounded.       *)
(* ------------------------------------------------------------------------- *)

let sch5b_circ = new_definition
 `sch5b_circ h = {y:real^3 | y$1 pow 2 + y$2 pow 2 = &1 /\ y$3 = h}`;;

let SCH5B_BAND_CONNECTED = prove
 (`!lo hi. connected(sch5b_band lo hi)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `sch5b_band lo hi =
    IMAGE (\z:real^(2,1)finite_sum.
             vector[(fstcart z)$1; (fstcart z)$2; drop(sndcart z)]:real^3)
          (sphere(vec 0:real^2,&1) PCROSS interval(lift lo,lift hi))`
  SUBST1_TAC THENL
   [REWRITE_TAC[sch5b_band; EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PASTECART;
                PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                IN_SPHERE_0; IN_INTERVAL_1; LIFT_DROP; NORM_EQ_1; DOT_2] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`vector[(y:real^3)$1; y$2]:real^2`; `lift((y:real^3)$3)`] THEN
      ASM_REWRITE_TAC[VECTOR_2; LIFT_DROP; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 = &1` THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[VECTOR_3] THEN
      UNDISCH_TAC `(x:real^2)$1 * x$1 + x$2 * x$2 = &1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; FSTCART_ADD; SNDCART_ADD;
                FSTCART_CMUL; SNDCART_CMUL; DROP_ADD; DROP_CMUL; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT];
    MATCH_MP_TAC CONNECTED_PCROSS THEN REWRITE_TAC[CONNECTED_INTERVAL] THEN
    MATCH_MP_TAC CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_2; LE_REFL]]);;

let SCH5B_ELL_CIRCLE = prove
 (`IMAGE sch5b_ell (sphere(vec 0:real^2,&1)) = sch5b_circ(--(&9 / &8))`,
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_IMAGE; sch5b_circ; IN_ELIM_THM; IN_SPHERE_0] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `w:real^2` SCH5B_ELL_BASIC) THEN
    SUBGOAL_THEN `~(w:real^2 = vec 0)` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `norm(vec 0:real^2) = &1` THEN
      REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 SCH5B_HB_FACTS))] THEN SIMP_TAC[];
    STRIP_TAC THEN EXISTS_TAC `vector[(y:real^3)$1; y$2]:real^2` THEN
    SUBGOAL_THEN `norm(vector[(y:real^3)$1; y$2]:real^2) = &1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_EQ_1; DOT_2; VECTOR_2; GSYM REAL_POW_2]; ALL_TAC] THEN
    ASM_REWRITE_TAC[sch5b_ell; REAL_DIV_1; VECTOR_2;
                    CONJUNCT1(CONJUNCT2(CONJUNCT2 SCH5B_HB_FACTS))] THEN
    ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3]]);;

let SCH5B_BB_FACTS = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3])))
     ==> (!y. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1 /\
              ~(y = vector[&1; &0; &4 / &3])
              ==> g'(Theta y) IN sphere(vec 0,&1) /\
                  ~(g'(Theta y) = g'(Theta(vector[&1; &0; &4 / &3]))) /\
                  (R(g'(Theta y)))$3 < &1 /\
                  sch5b_sti Ri (sch5b_st R (g'(Theta y))) = g'(Theta y) /\
                  y IN {y | y IN sch5b_ub g Theta /\ (R(g'(Theta y)))$3 < &1}) /\
         open {y | y IN sch5b_ub g Theta /\ (R(g'(Theta y)))$3 < &1} /\
         (\y. sch5b_st R (g'(Theta y))) continuous_on
         {y | y IN sch5b_ub g Theta /\ (R(g'(Theta y)))$3 < &1} /\
         (!y y'. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1 /\
                 ~(y = vector[&1; &0; &4 / &3]) /\
                 y' IN sch5v_slab(&3 / &2) /\ y'$1 pow 2 + y'$2 pow 2 = &1 /\
                 ~(y' = vector[&1; &0; &4 / &3]) /\
                 sch5b_st R (g'(Theta y)) = sch5b_st R (g'(Theta y'))
                 ==> y = y')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_ST_PTOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "S1") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCH5B_BETA_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "B1") (CONJUNCTS_THEN2 (LABEL_TAC "B2")
    (CONJUNCTS_THEN2 (LABEL_TAC "B3") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!y. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1 /\
        ~(y = vector[&1; &0; &4 / &3])
        ==> (g':real^3->real^3)((Theta:real^3->real^3) y) IN sphere(vec 0,&1) /\
            ~(g'(Theta y) = g'(Theta(vector[&1; &0; &4 / &3]))) /\
            ((R:real^3->real^3)(g'(Theta y)))$3 < &1 /\
            sch5b_sti Ri (sch5b_st R (g'(Theta y))) = g'(Theta y) /\
            y IN {y | y IN sch5b_ub g Theta /\ (R(g'(Theta y)))$3 < &1}`
  (LABEL_TAC "A") THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    USE_THEN "B1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
            (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)))) THEN
    SUBGOAL_THEN `~((g':real^3->real^3)((Theta:real^3->real^3) y) =
                    g'(Theta(vector[&1; &0; &4 / &3])))` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(y = vector[&1; &0; &4 / &3]:real^3)` THEN
      REWRITE_TAC[] THEN USE_THEN "B2" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SCH5B_PTOP];
      ALL_TAC] THEN
    USE_THEN "S1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `(g':real^3->real^3)((Theta:real^3->real^3) y) IN sphere(vec 0,&1)`)
            (ASSUME `~((g':real^3->real^3)((Theta:real^3->real^3) y) =
                       g'(Theta(vector[&1; &0; &4 / &3])))`)))) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {y | y IN sch5b_ub g Theta /\
                          ((R:real^3->real^3)((g':real^3->real^3)((Theta:real^3->real^3) y)))$3
                          < &1}` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `{y | y IN sch5b_ub g Theta /\
           ((R:real^3->real^3)((g':real^3->real^3)((Theta:real^3->real^3) y)))$3 < &1} =
      {y | y IN sch5b_ub g Theta /\ (R o g' o Theta) y IN {x:real^3 | x$3 < &1}}`
    SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      ASM_MESON_TAC[sch5b_rot; ORTHOGONAL_TRANSFORMATION_LINEAR]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\y. sch5b_st R ((g':real^3->real^3)((Theta:real^3->real^3) y))) =
                  sch5b_st R o (g' o Theta)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sch5b_ub g Theta` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ((R:real^3->real^3) x)$3 < &1}` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `y':real^3`] THEN STRIP_TAC THEN
  USE_THEN "A" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
          (CONJ (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)
                (ASSUME `~(y = vector[&1; &0; &4 / &3]:real^3)`))))) THEN
  USE_THEN "A" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `(y':real^3) IN sch5v_slab(&3 / &2)`)
          (CONJ (ASSUME `(y':real^3)$1 pow 2 + y'$2 pow 2 = &1`)
                (ASSUME `~(y' = vector[&1; &0; &4 / &3]:real^3)`))))) THEN
  REPEAT STRIP_TAC THEN USE_THEN "B2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let SCH5B_J_FACTS = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3])))
     ==> IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)) =
         IMAGE (\y. sch5b_st R (g'(Theta y))) (sch5b_circ(--(&9 / &8))) /\
         compact(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1))) /\
         (!lo hi. --(&3 / &2) <= lo /\ hi <= &4 / &3 /\ (hi <= --(&9 / &8) \/ --(&9 / &8) <= lo)
                  ==> IMAGE (\y. sch5b_st R (g'(Theta y))) (sch5b_band lo hi) SUBSET
                      inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1))) \/
                      IMAGE (\y. sch5b_st R (g'(Theta y))) (sch5b_band lo hi) SUBSET
                      outside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)) =
                IMAGE (\y. sch5b_st R ((g':real^3->real^3)((Theta:real^3->real^3) y)))
                      (sch5b_circ(--(&9 / &8)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `sch5b_fb R g' Theta =
                  (\w. sch5b_st R ((g':real^3->real^3)((Theta:real^3->real^3)(sch5b_ell w))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; sch5b_fb]; ALL_TAC] THEN
    REWRITE_TAC[GSYM SCH5B_ELL_CIRCLE; GSYM IMAGE_o] THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_BB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "INJ")))) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)) =
                 IMAGE (\y. sch5b_st R ((g':real^3->real^3)((Theta:real^3->real^3) y)))
                       (sch5b_circ(--(&9 / &8)))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_SPHERE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^2->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SCH5B_FB_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `a:real`; `lam:real`; `c:real^2->real^2`;
                            `c':real^2->real^2`; `Theta':real^3->real^3`; `Ri:real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MATCH_MP_TAC SCH5V_CONNECTED_SIDE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[SCH5B_BAND_CONNECTED] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{y | y IN sch5b_ub g Theta /\
                     ((R:real^3->real^3)((g':real^3->real^3)((Theta:real^3->real^3) y)))$3
                     < &1}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; sch5b_band; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    USE_THEN "A" (MP_TAC o SPEC `y:real^3`) THEN
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\y:real^3. y$3`) THEN REWRITE_TAC[VECTOR_3] THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_IMAGE] THEN
  X_GEN_TAC `z:real^2` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(y:real^3) IN sch5b_band lo hi` THEN
  UNDISCH_TAC `(y':real^3) IN sch5b_circ(--(&9 / &8))` THEN
  REWRITE_TAC[sch5b_band; sch5b_circ; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&3 / &2) /\ (y':real^3) IN sch5v_slab(&3 / &2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(y = vector[&1; &0; &4 / &3]:real^3) /\ ~(y' = vector[&1; &0; &4 / &3]:real^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `\y:real^3. y$3`) THEN REWRITE_TAC[VECTOR_3] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_st R ((g':real^3->real^3)((Theta:real^3->real^3) y)) =
                sch5b_st R (g'(Theta y'))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `y:real^3 = y'` MP_TAC THENL
   [USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\y:real^3. y$3`) THEN REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let SCH5B_BAND_UNBOUNDED = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri M.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3])))
     ==> ?u. --(&9 / &8) < u /\ u < &4 / &3 /\
             M < norm(sch5b_st R (g'(Theta(vector[&1; &0; u]))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_ST_PTOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_BB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A") (K ALL_TAC)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCH5B_BETA_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(vector[&1; &0; &4 / &3]:real^3) IN sch5b_ub g Theta` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vector[&1; &0; &4 / &3]:real^3` o
      check (fun th -> can (term_match [] `!y:real^3. P y ==> Q y /\ R y /\ y IN sch5b_ub g Theta`) (concl th))) THEN
    REWRITE_TAC[SCH5B_PTOP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift(((R:real^3->real^3)((g':real^3->real^3)((Theta:real^3->real^3) y)))$3))
                continuous (at (vector[&1; &0; &4 / &3]))` MP_TAC THENL
   [SUBGOAL_THEN `(\y. lift(((R:real^3->real^3)((g':real^3->real^3)((Theta:real^3->real^3) y)))$3))
                  continuous_on sch5b_ub g Theta` MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      SUBGOAL_THEN `(\y. (R:real^3->real^3)((g':real^3->real^3)((Theta:real^3->real^3) y))) =
                    R o (g' o Theta)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      ASM_MESON_TAC[sch5b_rot; ORTHOGONAL_TRANSFORMATION_LINEAR];
      ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((R:real^3->real^3)((g':real^3->real^3)
                   ((Theta:real^3->real^3)(vector[&1; &0; &4 / &3]))))$3 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `sch5b_rot R Ri ((g':real^3->real^3)((Theta:real^3->real^3)
                   (vector[&1; &0; &4 / &3])))` THEN
    SIMP_TAC[sch5b_rot; BASIS_COMPONENT; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `e = inv(M pow 2 + &2)` THEN
  SUBGOAL_THEN `&0 < e /\ e <= &1 /\ &1 / e = M pow 2 + &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MP_TAC(SPEC `M:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; REAL_INV_INV; REAL_MUL_LID]];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[DIST_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  EXISTS_TAC `&4 / &3 - min d (&1) / &2` THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `u = &4 / &3 - min d (&1) / &2` THEN
  SUBGOAL_THEN `--(&9 / &8) < u /\ u < &4 / &3 /\ &4 / &3 - u < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(vector[&1; &0; u]:real^3) IN sch5v_slab(&3 / &2) /\
                (vector[&1; &0; u]:real^3)$1 pow 2 + (vector[&1; &0; u]:real^3)$2 pow 2 = &1 /\
                ~(vector[&1; &0; u]:real^3 = vector[&1; &0; &4 / &3])` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sch5v_slab; IN_ELIM_THM; VECTOR_3] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\y:real^3. y$3`) THEN REWRITE_TAC[VECTOR_3] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "A" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (CONJ (ASSUME `(vector[&1; &0; u]:real^3) IN sch5v_slab(&3 / &2)`)
       (CONJ (ASSUME `(vector[&1; &0; u]:real^3)$1 pow 2 + (vector[&1; &0; u]:real^3)$2 pow 2 = &1`)
             (ASSUME `~(vector[&1; &0; u]:real^3 = vector[&1; &0; &4 / &3])`))))) THEN
  USE_THEN "D" (MP_TAC o SPEC `vector[&1; &0; u]:real^3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[dist] THEN
    SUBGOAL_THEN `vector[&1; &0; u] - vector[&1; &0; &4 / &3]:real^3 =
                  (u - &4 / &3) % basis 3` SUBST1_TAC THENL
     [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_SUB_COMPONENT;
               VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `q = ((R:real^3->real^3)((g':real^3->real^3)
                    ((Theta:real^3->real^3)(vector[&1; &0; u]))))$3` THEN
  SUBGOAL_THEN `&1 - e < q /\ q < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(sch5b_st R ((g':real^3->real^3)((Theta:real^3->real^3)
                  (vector[&1; &0; u])))) pow 2 = (&1 + q) / (&1 - q)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `M pow 2 < (&1 + q) / (&1 - q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_SUB_LT] THEN
    SUBGOAL_THEN `(M pow 2 + &2) * e = &1` ASSUME_TAC THENL
     [EXPAND_TAC "e" THEN MATCH_MP_TAC REAL_MUL_RINV THEN
      MP_TAC(SPEC `M:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `M pow 2 * (&1 - q) < M pow 2 * e + e` MP_TAC THENL
     [MP_TAC(SPEC `M:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
      SUBGOAL_THEN `M pow 2 * (&1 - q) <= M pow 2 * e` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `(M pow 2 + &2) * e = &1` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs m < abs n /\ &0 <= n ==> m < n`) THEN
  REWRITE_TAC[NORM_POS_LE; REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC);;

let SCH5B_UPPER_OUTSIDE = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3])))
     ==> IMAGE (\y. sch5b_st R (g'(Theta y))) (sch5b_band (--(&9 / &8)) (&4 / &3)) SUBSET
         outside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_J_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPECL [`--(&9 / &8)`; `&4 / &3`]))) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `bounded(inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0:real^2,&1))))`
  MP_TAC THENL [ASM_SIMP_TAC[BOUNDED_INSIDE; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B"))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`; `B:real`]
    SCH5B_BAND_UNBOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "B" (MP_TAC o SPEC `sch5b_st R ((g':real^3->real^3)
                                 ((Theta:real^3->real^3)(vector[&1; &0; u])))`) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vector[&1; &0; u]:real^3` THEN
  REWRITE_TAC[sch5b_band; IN_ELIM_THM; VECTOR_3] THEN ASM_REAL_ARITH_TAC);;

let SCH5B_HB_SAMPLES = prove
 (`--(&9 / &8) < sch5b_hb(&7 / &6) /\ sch5b_hb(&7 / &6) < --(&3 / &4) /\
   --(&3 / &2) < sch5b_hb(&7 / &8) /\ sch5b_hb(&7 / &8) < --(&9 / &8)`,
  REWRITE_TAC[sch5b_hb] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let SCH5B_ELL_AXIS = prove
 (`!r. &0 < r ==> sch5b_ell(r % basis 1) = vector[&1; &0; sch5b_hb r] /\
                  norm(r % basis 1:real^2) = r`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(r % basis 1:real^2) = r` ASSUME_TAC THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[sch5b_ell] THEN
  SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; real_div; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ]);;

let SCH5B_CB_ORIENT = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb'.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3]))) /\
     sch_ball cb cb' /\
     IMAGE cb (cball(vec 0,&1)) =
     IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)) UNION
     inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1))) /\
     ((!x. x IN annulus (&3 / &4) (&2) ==> cb x = sch5b_fb R g' Theta x) \/
      (!x. x IN annulus (&3 / &4) (&2) ==> cb x = sch5b_fb R g' Theta (inv(norm x pow 2) % x)))
     ==> !x. x IN annulus (&3 / &4) (&2) ==> cb x = sch5b_fb R g' Theta x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `((&6 / &7) % basis 1:real^2) IN annulus (&3 / &4) (&2) /\
                ((&6 / &7) % basis 1:real^2) IN cball(vec 0:real^2,&1) /\
                inv(norm((&6 / &7) % basis 1:real^2) pow 2) % (&6 / &7) % basis 1 =
                (&7 / &6) % basis 1:real^2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&6 / &7` SCH5B_ELL_AXIS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; IN_CBALL_0; VECTOR_MUL_ASSOC] THEN
    MP_TAC(SPEC `&6 / &7` SCH5B_ELL_AXIS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(cb:real^2->real^2)((&6 / &7) % basis 1) =
                sch5b_fb R g' Theta ((&7 / &6) % basis 1)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(&6 / &7) % basis 1:real^2`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_fb R g' Theta ((&7 / &6) % basis 1) IN
                outside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)))` MP_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                   `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                   `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
      SCH5B_UPPER_OUTSIDE) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_IMAGE; sch5b_fb] THEN EXISTS_TAC `vector[&1; &0; sch5b_hb(&7 / &6)]:real^3` THEN
    MP_TAC(SPEC `&7 / &6` SCH5B_ELL_AXIS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    REWRITE_TAC[sch5b_band; IN_ELIM_THM; VECTOR_3] THEN
    MP_TAC SCH5B_HB_SAMPLES THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `sch5b_fb R g' Theta ((&7 / &6) % basis 1)`)) THEN
  SUBGOAL_THEN `(cb:real^2->real^2)((&6 / &7) % basis 1) IN
                IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)) UNION
                inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)))` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhand(concl th) = `IMAGE (cb:real^2->real^2) (cball(vec 0,&1))`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(&6 / &7) % basis 1:real^2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_WITH_INSIDE; IN_DIFF] THEN MESON_TAC[]);;

let SCH5B_CB_SIDES = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb'.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3]))) /\
     sch_ball cb cb' /\
     IMAGE cb (cball(vec 0,&1)) =
     IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)) UNION
     inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1))) /\
     (!x. x IN annulus (&3 / &4) (&2) ==> cb x = sch5b_fb R g' Theta x)
     ==> IMAGE cb (sphere(vec 0,&1)) = IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)) /\
         IMAGE cb (ball(vec 0,&1)) = inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1))) /\
         IMAGE (\y. sch5b_st R (g'(Theta y))) (sch5b_band (--(&3 / &2)) (--(&9 / &8))) SUBSET
         inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "IM") (LABEL_TAC "EQ"))))) THEN
  ABBREV_TAC `J = IMAGE (sch5b_fb R g' Theta) (sphere(vec 0:real^2,&1))` THEN
  SUBGOAL_THEN `!x y:real^2. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\
                             (cb:real^2->real^2) x = cb y ==> x = y` (LABEL_TAC "INJ") THENL
   [UNDISCH_TAC `sch_ball (cb:real^2->real^2) cb'` THEN
    REWRITE_TAC[sch_ball; diffeomorphism_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (cb:real^2->real^2) (sphere(vec 0,&1)) = J` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE] THEN
    X_GEN_TAC `z:real^2` THEN EQ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "EQ" (MP_TAC o SPEC `x:real^2`) THEN
    UNDISCH_TAC `(x:real^2) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (cb:real^2->real^2) (ball(vec 0,&1)) = inside J` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:real^2) IN J UNION inside J` MP_TAC THENL
       [USE_THEN "IM" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(x:real^2) IN ball(vec 0,&1)` THEN
        REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
      UNDISCH_TAC `IMAGE (cb:real^2->real^2) (sphere(vec 0,&1)) = J` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x:real^2 = y` MP_TAC THENL
       [USE_THEN "INJ" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `(x:real^2) IN ball(vec 0,&1)` THEN REWRITE_TAC[IN_BALL_0] THEN
          REAL_ARITH_TAC;
          UNDISCH_TAC `(y:real^2) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_BALL_0; IN_SPHERE_0] THEN
          REAL_ARITH_TAC;
          ASM_MESON_TAC[]];
        DISCH_THEN SUBST_ALL_TAC THEN
        MAP_EVERY UNDISCH_TAC [`(y:real^2) IN ball(vec 0,&1)`; `(y:real^2) IN sphere(vec 0,&1)`] THEN
        REWRITE_TAC[IN_BALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC];
      DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^2) IN IMAGE (cb:real^2->real^2) (cball(vec 0,&1))` MP_TAC THENL
       [USE_THEN "IM" SUBST1_TAC THEN ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
      ASM_CASES_TAC `norm(x:real^2) = &1` THENL
       [SUBGOAL_THEN `(z:real^2) IN J` MP_TAC THENL
         [UNDISCH_TAC `IMAGE (cb:real^2->real^2) (sphere(vec 0,&1)) = J` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
          EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[];
          MP_TAC(ISPEC `J:real^2->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[]];
        UNDISCH_TAC `(x:real^2) IN cball(vec 0,&1)` THEN REWRITE_TAC[IN_CBALL_0] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`; `R:real^3->real^3`; `Ri:real^3->real^3`]
    SCH5B_J_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`--(&3 / &2)`; `--(&9 / &8)`] o CONJUNCT2 o CONJUNCT2) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `sch5b_fb R g' Theta ((&7 / &8) % basis 1) IN inside J` MP_TAC THENL
   [UNDISCH_TAC `IMAGE (cb:real^2->real^2) (ball(vec 0,&1)) = inside J` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(&7 / &8) % basis 1:real^2` THEN
    MP_TAC(SPEC `&7 / &8` SCH5B_ELL_AXIS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    CONV_TAC SYM_CONV THEN USE_THEN "EQ" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_fb R g' Theta ((&7 / &8) % basis 1) IN outside J` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_IMAGE; sch5b_fb] THEN
    EXISTS_TAC `vector[&1; &0; sch5b_hb(&7 / &8)]:real^3` THEN
    MP_TAC(SPEC `&7 / &8` SCH5B_ELL_AXIS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    REWRITE_TAC[sch5b_band; IN_ELIM_THM; VECTOR_3] THEN
    MP_TAC SCH5B_HB_SAMPLES THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `J:real^2->bool` INSIDE_INTER_OUTSIDE) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The bottom data bundle (pancake, rotation, oriented SCH_R2                *)
(* chart cb of F_b), the scaled stereographic map Phi of the parameter       *)
(* sphere (|Phi t| <= 1 iff t3 <= -1/4, ell o Phi = collar on the cylinder   *)
(* part), and immersions from left inverses on the sphere.                   *)
(* ------------------------------------------------------------------------- *)

let sch5b_bvars8 = [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                    `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                    `Theta':real^3->real^3`];;

let sch5b_bvars10 = sch5b_bvars8 @ [`R:real^3->real^3`; `Ri:real^3->real^3`];;

let sch5b_bvars12 = sch5b_bvars10 @ [`cb:real^2->real^2`; `cb':real^2->real^2`];;

let sch5b_bot = new_definition
 `sch5b_bot (g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'
            (R:real^3->real^3) Ri (cb:real^2->real^2) cb' <=>
    sch5b_pancake g g' a lam c c' Theta Theta' /\
    sch5b_rot R Ri (g'(Theta(vector[&1; &0; &4 / &3]))) /\
    sch_ball cb cb' /\
    IMAGE cb (cball(vec 0,&1)) =
    IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)) UNION
    inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1))) /\
    (!x. x IN annulus (&3 / &4) (&2) ==> cb x = sch5b_fb R g' Theta x)`;;

let SCH5B_BOT_EXISTS = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch5b_pancake g g' a lam c c' Theta Theta'
     ==> ?R Ri cb cb'. sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5B_BETA_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `vector[&1; &0; &4 / &3]:real^3` o CONJUNCT1) THEN
  REWRITE_TAC[SCH5B_PTOP] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(g':real^3->real^3)((Theta:real^3->real^3)(vector[&1; &0; &4 / &3]))`
    SCH5B_ROTATION) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` (X_CHOOSE_THEN `Ri:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `sch5b_rot R Ri ((g':real^3->real^3)((Theta:real^3->real^3)
                  (vector[&1; &0; &4 / &3])))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[sch5b_rot]; ALL_TAC] THEN
  MP_TAC(ISPECL sch5b_bvars10 SCH5B_FB_NECK) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(REWRITE_RULE[SCH_R2_STATEMENT] SCH_R2) THEN
  DISCH_THEN(MP_TAC o SPECL [`sch5b_fb R g' Theta`; `sch5b_fbi Ri g Theta'`]) THEN
  ASM_REWRITE_TAC[sch_fills] THEN
  DISCH_THEN(X_CHOOSE_THEN `cb:real^2->real^2` (X_CHOOSE_THEN `cb':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`R:real^3->real^3`; `Ri:real^3->real^3`; `cb:real^2->real^2`;
                        `cb':real^2->real^2`] THEN
  ASM_REWRITE_TAC[sch5b_bot] THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_CB_ORIENT) THEN ASM_REWRITE_TAC[]);;

let sch5b_phi = new_definition
 `sch5b_phi (x:real^3) = sqrt(&5 / &3) % stereo2_n(inv(norm x) % x)`;;

let sch5b_phii = new_definition
 `sch5b_phii (z:real^2) = stereo2_n_inv(inv(sqrt(&5 / &3)) % z)`;;

let SCH5B_SQRT53 = prove
 (`&0 < sqrt(&5 / &3) /\ sqrt(&5 / &3) pow 2 = &5 / &3 /\ ~(sqrt(&5 / &3) = &0)`,
  SUBGOAL_THEN `&0 < sqrt(&5 / &3)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_ARITH `&0 <= &5 / &3`; REAL_LT_IMP_NZ]);;

let SCH5B_PHI_FACTS = prove
 (`(!t. t IN sphere(vec 0,&1) /\ t$3 < &1
        ==> sch5b_phii(sch5b_phi t) = t /\
            norm(sch5b_phi t) pow 2 = (&5 / &3) * (&1 + t$3) / (&1 - t$3)) /\
   (!z. sch5b_phi(sch5b_phii z) = z /\ sch5b_phii z IN sphere(vec 0,&1) /\
        (sch5b_phii z)$3 < &1) /\
   (!x. ~(x = vec 0) ==> sch5b_phi(inv(norm x) % x) = sch5b_phi x)`,
  MP_TAC SCH5B_SQRT53 THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t:real^3. t IN sphere(vec 0,&1) ==> inv(norm t) % t = t` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t:real^3) IN sphere(vec 0,&1) DELETE basis 3` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_DELETE] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(basis 3:real^3)$3 < &1` THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[sch5b_phi; sch5b_phii; VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID;
                 STEX_STEREO2_N_LEFT; NORM_MUL; REAL_POW_MUL; STEX_STEREO2_N_NORM2] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`];
    X_GEN_TAC `z:real^2` THEN
    MP_TAC(ISPEC `inv(sqrt(&5 / &3)) % z:real^2` STEX_STEREO2_N_INV_IN) THEN
    REWRITE_TAC[GSYM sch5b_phii] THEN DISCH_TAC THEN
    MP_TAC STEX_STEREO2_N_DOMAIN THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `sch5b_phii z`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `sch5b_phii z IN sphere(vec 0,&1) DELETE basis 3` THEN
    REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[sch5b_phi] THEN REWRITE_TAC[sch5b_phii; STEX_STEREO2_N_RIGHT] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[sch5b_phi] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `norm(inv(norm x) % x:real^3) = &1` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
      REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID]]]);;

let SCH5B_PHI_ELL = prove
 (`!t. t IN sphere(vec 0,&1) /\ --(&1) < t$3 /\ t$3 < &1
       ==> sch5b_ell(sch5b_phi t) =
           vector[t$1 / sqrt(&1 - t$3 pow 2); t$2 / sqrt(&1 - t$3 pow 2); -- &1 + t$3 / &2]`,
  X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN MP_TAC SCH5B_SQRT53 THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^3)$1 pow 2 + t$2 pow 2 = &1 - t$3 pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - (t:real^3)$3 pow 2 /\ &0 < &1 - t$3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&0 < &1 - x pow 2 <=> x pow 2 < &1 pow 2`] THEN
    REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 - (t:real^3)$3 pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_phi t = (sqrt(&5 / &3) / (&1 - (t:real^3)$3)) % vector[t$1; t$2]:real^2`
  ASSUME_TAC THENL
   [REWRITE_TAC[sch5b_phi] THEN
    SUBGOAL_THEN `inv(norm t) % t = t:real^3` SUBST1_TAC THENL
     [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID];
      ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT; VECTOR_2;
                STEX_STEREO2_N_COMPONENTS] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(sch5b_phi t) = sqrt(&5 / &3) / (&1 - (t:real^3)$3) *
                                    sqrt(&1 - t$3 pow 2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs(sqrt(&5 / &3) / (&1 - (t:real^3)$3)) = sqrt(&5 / &3) / (&1 - t$3)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[vector_norm; DOT_2; VECTOR_2] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `(t:real^3)$1 pow 2 + t$2 pow 2 = &1 - t$3 pow 2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(sch5b_phi t) pow 2 = (&5 / &3) * (&1 + (t:real^3)$3) / (&1 - t$3)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `&0 < &1 - (t:real^3)$3` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[sch5b_ell; sch5b_hb] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < &1 - (t:real^3)$3`; `&0 < sqrt(&1 - (t:real^3)$3 pow 2)`;
                           `&0 < sqrt(&5 / &3)`] THEN CONV_TAC REAL_FIELD;
    MAP_EVERY UNDISCH_TAC [`&0 < &1 - (t:real^3)$3`; `&0 < sqrt(&1 - (t:real^3)$3 pow 2)`;
                           `&0 < sqrt(&5 / &3)`] THEN CONV_TAC REAL_FIELD;
    UNDISCH_TAC `&0 < &1 - (t:real^3)$3` THEN CONV_TAC REAL_FIELD]);;

let SCH5B_PHI_SMOOTH = prove
 (`open {x:real^3 | ~(x = vec 0) /\ x$3 < norm x} /\
   smooth_map_on {x:real^3 | ~(x = vec 0) /\ x$3 < norm x} sch5b_phi /\
   smooth_map_on (:real^2) sch5b_phii`,
  SUBGOAL_THEN `open {x:real^3 | ~(x = vec 0) /\ x$3 < norm x}` ASSUME_TAC THENL
   [SUBGOAL_THEN `{x:real^3 | ~(x = vec 0) /\ x$3 < norm x} =
                  {x | x IN {x:real^3 | ~(x = vec 0)} /\ &0 < norm x - x$3}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SCH5C_OPEN_POS THEN REWRITE_TAC[OPEN_NONZERO] THEN
    SCH5C_SMOOTH_TAC THEN REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `sch5b_phi = (\x:real^3. vector[sqrt(&5 / &3) * ((x$1 / norm x) / (&1 - x$3 / norm x));
                                     sqrt(&5 / &3) * ((x$2 / norm x) / (&1 - x$3 / norm x))]:real^2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; sch5b_phi] THEN GEN_TAC THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT; VECTOR_2;
                  STEX_STEREO2_N_COMPONENTS] THEN
      REWRITE_TAC[real_div; REAL_MUL_AC];
      ALL_TAC] THEN
    SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; NORM_EQ_0] THEN
    SIMP_TAC[] THEN
    (X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
     SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
     SUBGOAL_THEN `(x:real^3)$3 / norm x < &1` MP_TAC THENL
      [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);
    SUBGOAL_THEN `sch5b_phii = stereo2_n_inv o (\z:real^2. inv(sqrt(&5 / &3)) % z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; sch5b_phii; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; STEX_STEREO2_N_INV_SMOOTH] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]]);;

(* A map with a left inverse on the sphere near t is an immersion there. *)

let SCH5B_LINV_IMMERSION = prove
 (`!(f:real^3->real^3) (L:real^3->real^3) t r.
     t IN sphere(vec 0,&1) /\ &0 < r /\ f differentiable (at t) /\
     L differentiable (at (f t)) /\
     (!x. x IN sphere(vec 0,&1) /\ dist(x,t) < r ==> L(f x) = x)
     ==> !v. orthogonal t v /\ frechet_derivative f (at t) v = vec 0 ==> v = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `((L:real^3->real^3) o (f:real^3->real^3) has_derivative
                 (frechet_derivative L (at (f t)) o frechet_derivative f (at t))) (at t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(L:real^3->real^3) o (f:real^3->real^3)`; `\x:real^3. x`; `t:real^3`;
                 `r:real`] SCH5_SPHERE_TANGENT_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM; DIFFERENTIABLE_ID] THEN REWRITE_TAC[differentiable] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  MP_TAC(ISPEC `at(t:real^3)` HAS_DERIVATIVE_ID) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `linear(frechet_derivative (L:real^3->real^3) (at (f(t:real^3))))` MP_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The bottom disc on the parameter sphere, D = st^-1(cb(cball               *)
(* 1)) with interior st^-1(cb(ball 1)), and its parametrisation P = st^-1 o  *)
(* cb o Phi by the polar cap t3 <= -1/4 of the sphere.                       *)
(* ------------------------------------------------------------------------- *)

let sch5b_pp = new_definition
 `sch5b_pp (Ri:real^3->real^3) (cb:real^2->real^2) (x:real^3) =
    sch5b_sti Ri (cb(sch5b_phi x))`;;

let sch5b_disc = new_definition
 `sch5b_disc (Ri:real^3->real^3) (cb:real^2->real^2) =
    IMAGE (sch5b_sti Ri) (IMAGE cb (cball(vec 0,&1)))`;;

let sch5b_odisc = new_definition
 `sch5b_odisc (Ri:real^3->real^3) (cb:real^2->real^2) =
    IMAGE (sch5b_sti Ri) (IMAGE cb (ball(vec 0,&1)))`;;

let SCH5B_PHI_NORM = prove
 (`!t. t IN sphere(vec 0,&1) /\ t$3 < &1
       ==> (t$3 < &1 / &4 ==> norm(sch5b_phi t) < &2) /\
           (norm(sch5b_phi t) <= &1 <=> t$3 <= --(&1 / &4)) /\
           (norm(sch5b_phi t) < &1 <=> t$3 < --(&1 / &4)) /\
           (--(&9 / &20) < t$3 ==> &3 / &4 < norm(sch5b_phi t))`,
  X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
  MP_TAC(CONJUNCT1 SCH5B_PHI_FACTS) THEN DISCH_THEN(MP_TAC o SPEC `t:real^3`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `n = norm(sch5b_phi t)` THEN
  SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL [EXPAND_TAC "n" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - (t:real^3)$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k. &0 <= k ==> (n < k <=> n pow 2 < k pow 2) /\ (n <= k <=> n pow 2 <= k pow 2) /\
                                (k < n <=> k pow 2 < n pow 2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS; GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= &2 /\ &0 <= &1 /\ &0 <= &3 / &4`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ;
               REAL_ARITH `(&5 / &3) * x / y = (&5 / &3 * x) / y`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let SCH5B_PP_FACTS = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb'.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb'
     ==> (!t. t IN sphere(vec 0,&1) /\ t$3 < &1 / &4
              ==> sch5b_phi t IN ball(vec 0,&2) /\ sch5b_pp Ri cb t IN sphere(vec 0,&1) /\
                  ~(sch5b_pp Ri cb t = g'(Theta(vector[&1; &0; &4 / &3]))) /\
                  sch5b_st R (sch5b_pp Ri cb t) = cb(sch5b_phi t)) /\
         (!t. t IN sphere(vec 0,&1) /\ t$3 <= --(&1 / &4)
              ==> sch5b_phi t IN cball(vec 0,&1) /\ sch5b_pp Ri cb t IN sch5b_disc Ri cb) /\
         (!t. t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4)
              ==> sch5b_phi t IN ball(vec 0,&1) /\ sch5b_pp Ri cb t IN sch5b_odisc Ri cb) /\
         (!t t'. t IN sphere(vec 0,&1) /\ t$3 < &1 / &4 /\
                 t' IN sphere(vec 0,&1) /\ t'$3 < &1 / &4 /\
                 sch5b_pp Ri cb t = sch5b_pp Ri cb t' ==> t = t') /\
         IMAGE (sch5b_pp Ri cb) {t | t IN sphere(vec 0,&1) /\ t$3 <= --(&1 / &4)} =
         sch5b_disc Ri cb /\
         IMAGE (sch5b_pp Ri cb) {t | t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4)} =
         sch5b_odisc Ri cb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5b_bot] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)))) THEN
  MP_TAC(ISPECL sch5b_bvars10 SCH5B_ST_PTOP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y:real^2. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\
                             (cb:real^2->real^2) x = cb y ==> x = y` (LABEL_TAC "INJ") THENL
   [UNDISCH_TAC `sch_ball (cb:real^2->real^2) cb'` THEN
    REWRITE_TAC[sch_ball; diffeomorphism_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC SCH5B_PHI_FACTS THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P1") (CONJUNCTS_THEN2 (LABEL_TAC "P2") (K ALL_TAC))) THEN
  SUBGOAL_THEN `!t:real^3. t IN sphere(vec 0,&1) /\ t$3 < &1 / &4
                           ==> sch5b_phi t IN ball(vec 0,&2)` (LABEL_TAC "B2") THENL
   [X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPEC `t:real^3` SCH5B_PHI_NORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[IN_BALL_0];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN ASM_SIMP_TAC[sch5b_pp];
    X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPEC `t:real^3` SCH5B_PHI_NORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `sch5b_phi t IN cball(vec 0,&1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_CBALL_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[sch5b_pp; sch5b_disc] THEN
    REPEAT(MATCH_MP_TAC FUN_IN_IMAGE) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPEC `t:real^3` SCH5B_PHI_NORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `sch5b_phi t IN ball(vec 0,&1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[sch5b_pp; sch5b_odisc] THEN
    REPEAT(MATCH_MP_TAC FUN_IN_IMAGE) THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real^3`; `t':real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `sch5b_phi t = sch5b_phi t'` MP_TAC THENL
     [USE_THEN "INJ" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `sch5b_st R` o
        check (fun th -> concl th = `sch5b_pp Ri cb t = sch5b_pp Ri cb t'`)) THEN
      ASM_REWRITE_TAC[sch5b_pp];
      DISCH_THEN(MP_TAC o AP_TERM `sch5b_phii`) THEN
      USE_THEN "P1" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `(t:real^3) IN sphere(vec 0,&1)`)
        (REWRITE_RULE[] (MP (REAL_ARITH `(t:real^3)$3 < &1 / &4 ==> t$3 < &1`)
           (ASSUME `(t:real^3)$3 < &1 / &4`))))]) THEN
      USE_THEN "P1" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `(t':real^3) IN sphere(vec 0,&1)`)
        (REWRITE_RULE[] (MP (REAL_ARITH `(t':real^3)$3 < &1 / &4 ==> t'$3 < &1`)
           (ASSUME `(t':real^3)$3 < &1 / &4`))))])];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; sch5b_disc] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `t:real^3` SCH5B_PHI_NORM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
      EXISTS_TAC `(cb:real^2->real^2)(sch5b_phi t)` THEN ASM_REWRITE_TAC[GSYM sch5b_pp] THEN
      EXISTS_TAC `sch5b_phi t` THEN ASM_REWRITE_TAC[IN_CBALL_0];
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `sch5b_phii w` THEN
      USE_THEN "P2" (STRIP_ASSUME_TAC o SPEC `w:real^2`) THEN
      ASM_REWRITE_TAC[sch5b_pp] THEN
      MP_TAC(SPEC `sch5b_phii w` SCH5B_PHI_NORM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w:real^2) IN cball(vec 0,&1)` THEN REWRITE_TAC[IN_CBALL_0] THEN
      SIMP_TAC[]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; sch5b_odisc] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `t:real^3` SCH5B_PHI_NORM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
      EXISTS_TAC `(cb:real^2->real^2)(sch5b_phi t)` THEN ASM_REWRITE_TAC[GSYM sch5b_pp] THEN
      EXISTS_TAC `sch5b_phi t` THEN ASM_REWRITE_TAC[IN_BALL_0];
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `sch5b_phii w` THEN
      USE_THEN "P2" (STRIP_ASSUME_TAC o SPEC `w:real^2`) THEN
      ASM_REWRITE_TAC[sch5b_pp] THEN
      MP_TAC(SPEC `sch5b_phii w` SCH5B_PHI_NORM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w:real^2) IN ball(vec 0,&1)` THEN REWRITE_TAC[IN_BALL_0] THEN
      SIMP_TAC[]]]);;

let SCH5B_DISC_ST = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb'.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb'
     ==> sch5b_disc Ri cb SUBSET sphere(vec 0,&1) /\
         (!x. x IN sch5b_disc Ri cb ==> ~(x = g'(Theta(vector[&1; &0; &4 / &3])))) /\
         sch5b_odisc Ri cb SUBSET sch5b_disc Ri cb /\
         (!x. x IN sphere(vec 0,&1) /\ ~(x = g'(Theta(vector[&1; &0; &4 / &3])))
              ==> (x IN sch5b_disc Ri cb <=>
                   sch5b_st R x IN IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)) UNION
                                  inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)))) /\
                  (x IN sch5b_odisc Ri cb <=>
                   sch5b_st R x IN inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot]) THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_CB_SIDES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "CBB") (K ALL_TAC))) THEN
  MP_TAC(ISPECL sch5b_bvars10 SCH5B_ST_PTOP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "S1") (CONJUNCTS_THEN2 (LABEL_TAC "S2")
    (CONJUNCTS_THEN2 (LABEL_TAC "S3") (K ALL_TAC)))) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[sch5b_disc; SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[sch5b_disc; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[sch5b_disc; sch5b_odisc] THEN REPEAT(MATCH_MP_TAC IMAGE_SUBSET) THEN
    REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  USE_THEN "S1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (CONJ (ASSUME `(x:real^3) IN sphere(vec 0,&1)`)
          (ASSUME `~(x = (g':real^3->real^3)((Theta:real^3->real^3)
                     (vector[&1; &0; &4 / &3])))`)))) THEN
  REWRITE_TAC[sch5b_disc; sch5b_odisc] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhand(concl th) = `IMAGE (cb:real^2->real^2) (cball(vec 0,&1))`)) THEN
  USE_THEN "CBB" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sch5b_st R x` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `w:real^2` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sch5b_st R x` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `w:real^2` THEN ASM_REWRITE_TAC[]]);;

let SCH5B_BOT_SIDES = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb'.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb'
     ==> IMAGE cb (sphere(vec 0,&1)) = IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)) /\
         IMAGE cb (ball(vec 0,&1)) = inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1))) /\
         IMAGE (\y. sch5b_st R (g'(Theta y))) (sch5b_band (--(&3 / &2)) (--(&9 / &8))) SUBSET
         inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5b_bot] THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_CB_SIDES) THEN ASM_REWRITE_TAC[]);;

let SCH5B_BOT_J = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb'.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb'
     ==> IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)) =
         IMAGE (\y. sch5b_st R (g'(Theta y))) (sch5b_circ(--(&9 / &8))) /\
         compact(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5b_bot] THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars10 SCH5B_J_FACTS) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let SCH5B_DISC_SETUP_TAC : tactic =
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)))) THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_DISC_ST) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DST")))) THEN
  MP_TAC(ISPECL sch5b_bvars10 SCH5B_ST_PTOP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "S1") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL sch5b_bvars10 SCH5B_BB_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "BB") (K ALL_TAC)) THEN
  MP_TAC(ISPECL sch5b_bvars10 SCH5B_J_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)));;

let SCH5B_DISC_COMPACT = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb'.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb'
     ==> compact(sch5b_disc Ri cb) /\ connected(sch5b_disc Ri cb)`,
  REPEAT GEN_TAC THEN SCH5B_DISC_SETUP_TAC THEN
  SUBGOAL_THEN `(sch5b_sti Ri o (cb:real^2->real^2)) continuous_on cball(vec 0,&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&2)` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `sch_ball (cb:real^2->real^2) cb'` THEN
        SIMP_TAC[sch_ball; diffeomorphism_on; SMOOTH_MAP_ON_CONTINUOUS_ON];
        REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV]];
    ALL_TAC] THEN
  REWRITE_TAC[sch5b_disc; GSYM IMAGE_o] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[CONNECTED_CBALL]]);;

let SCH5B_ODISC_OPEN = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb'.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb'
     ==> ?U. open U /\ sch5b_odisc Ri cb = sphere(vec 0,&1) INTER U`,
  REPEAT GEN_TAC THEN SCH5B_DISC_SETUP_TAC THEN
  EXISTS_TAC `{x:real^3 | x IN {x | ((R:real^3->real^3) x)$3 < &1} /\
                          sch5b_st R x IN inside(IMAGE (sch5b_fb R g' Theta)
                                                  (sphere(vec 0,&1)))}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[ETA_AX] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC OPEN_INSIDE THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  ASM_CASES_TAC `(x:real^3) IN sphere(vec 0,&1)` THENL
   [ALL_TAC; ASM SET_TAC[]] THEN
  ASM_CASES_TAC `x = (g':real^3->real^3)((Theta:real^3->real^3)(vector[&1; &0; &4 / &3]))` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `((R:real^3->real^3)((g':real^3->real^3)((Theta:real^3->real^3)
                    (vector[&1; &0; &4 / &3]))))$3 = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `sch5b_rot R Ri ((g':real^3->real^3)((Theta:real^3->real^3)
                     (vector[&1; &0; &4 / &3])))` THEN
      SIMP_TAC[sch5b_rot; BASIS_COMPONENT; DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_REFL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "DST" (fun th -> REWRITE_TAC[CONJUNCT2(MATCH_MP th
    (CONJ (ASSUME `(x:real^3) IN sphere(vec 0,&1)`)
          (ASSUME `~(x = (g':real^3->real^3)((Theta:real^3->real^3)
                     (vector[&1; &0; &4 / &3])))`)))]) THEN
  USE_THEN "S1" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `(x:real^3) IN sphere(vec 0,&1)`)
          (ASSUME `~(x = (g':real^3->real^3)((Theta:real^3->real^3)
                     (vector[&1; &0; &4 / &3])))`)))) THEN
  ASM_SIMP_TAC[]);;

let SCH5B_DISC_BAND = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb'.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb'
     ==> !y. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1 /\ y$3 < &4 / &3
             ==> (g'(Theta y) IN sch5b_disc Ri cb <=> y$3 <= --(&9 / &8)) /\
                 (g'(Theta y) IN sch5b_odisc Ri cb <=> y$3 < --(&9 / &8))`,
  REPEAT GEN_TAC THEN SCH5B_DISC_SETUP_TAC THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y = vector[&1; &0; &4 / &3]:real^3)` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `\y:real^3. y$3`) THEN REWRITE_TAC[VECTOR_3] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "BB" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
      (CONJ (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)
            (ASSUME `~(y = vector[&1; &0; &4 / &3]:real^3)`))))) THEN
  USE_THEN "DST" (fun th -> REWRITE_TAC[MATCH_MP th
    (CONJ (ASSUME `(g':real^3->real^3)((Theta:real^3->real^3) y) IN sphere(vec 0,&1)`)
          (ASSUME `~((g':real^3->real^3)((Theta:real^3->real^3) y) =
                     g'(Theta(vector[&1; &0; &4 / &3])))`))]) THEN
  SUBGOAL_THEN `--(&3 / &2) < (y:real^3)$3` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN sch5v_slab(&3 / &2)` THEN
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (sch5b_fb R g' Theta) (sphere(vec 0:real^2,&1))` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `IMAGE (sch5b_fb R g' Theta) (sphere(vec 0:real^2,&1))` INSIDE_INTER_OUTSIDE) THEN
  REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `(y:real^3)$3 < --(&9 / &8)` THENL
   [SUBGOAL_THEN `sch5b_st R ((g':real^3->real^3)((Theta:real^3->real^3) y)) IN
                  inside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)))` ASSUME_TAC THENL
     [MP_TAC(ISPECL sch5b_bvars12 SCH5B_BOT_SIDES) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN
      ASM_REWRITE_TAC[sch5b_band; IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNION] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^3)$3 = --(&9 / &8)` THENL
   [SUBGOAL_THEN `sch5b_st R ((g':real^3->real^3)((Theta:real^3->real^3) y)) IN
                  IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1))` ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o CONJUNCT1 o MATCH_MP (ISPECL sch5b_bvars12 SCH5B_BOT_J)) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN
      ASM_REWRITE_TAC[sch5b_circ; IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNION; REAL_LE_REFL; REAL_LT_REFL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_st R ((g':real^3->real^3)((Theta:real^3->real^3) y)) IN
                outside(IMAGE (sch5b_fb R g' Theta) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL sch5b_bvars10 SCH5B_UPPER_OUTSIDE) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[sch5b_band; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^3)$3 <= --(&9 / &8)) /\ ~((y:real^3)$3 < --(&9 / &8))`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (sch5b_fb R g' Theta) (sphere(vec 0:real^2,&1))` OUTSIDE_NO_OVERLAP) THEN
  ASM SET_TAC[]);;

let SCH5B_DISC_BOUNDARY = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb'.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb'
     ==> !x. x IN sch5b_disc Ri cb /\ ~(x IN sch5b_odisc Ri cb)
             ==> ?y. y IN sch5b_circ(--(&9 / &8)) /\ x = g'(Theta y)`,
  REPEAT GEN_TAC THEN SCH5B_DISC_SETUP_TAC THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN sphere(vec 0,&1) /\
                ~(x = (g':real^3->real^3)((Theta:real^3->real^3)(vector[&1; &0; &4 / &3])))`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "DST" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `(x:real^3) IN sphere(vec 0,&1)`)
          (ASSUME `~(x = (g':real^3->real^3)((Theta:real^3->real^3)
                     (vector[&1; &0; &4 / &3])))`)))) THEN
  REWRITE_TAC[ASSUME `(x:real^3) IN sch5b_disc Ri cb`;
              ASSUME `~((x:real^3) IN sch5b_odisc Ri cb)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[IN_UNION] THEN
  FIRST_ASSUM(SUBST1_TAC o CONJUNCT1 o MATCH_MP (ISPECL sch5b_bvars12 SCH5B_BOT_J)) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(y:real^3) IN sch5b_circ(--(&9 / &8))` THEN
  REWRITE_TAC[sch5b_circ; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&3 / &2) /\ ~(y = vector[&1; &0; &4 / &3]:real^3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\y:real^3. y$3`) THEN REWRITE_TAC[VECTOR_3] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "BB" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
      (CONJ (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)
            (ASSUME `~(y = vector[&1; &0; &4 / &3]:real^3)`))))) THEN
  USE_THEN "S1" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `(x:real^3) IN sphere(vec 0,&1)`)
          (ASSUME `~(x = (g':real^3->real^3)((Theta:real^3->real^3)
                     (vector[&1; &0; &4 / &3])))`)))) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The surgered sphere map s1 (0-homogeneous): Theta o collar                *)
(* on the cap c = x3/|x| > -2/5, g o P on the rest; both formulas agree for  *)
(* -9/20 < c <= -1/4.  Smoothness on x <> 0.                                 *)
(* ------------------------------------------------------------------------- *)

(* Select the bundle assumption sch5b_bot ... among the assumptions. *)

let sch5b_is_bot th =
  try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_bot" with Failure _ -> false;;

let sch5b_s1 = new_definition
 `sch5b_s1 (g:real^3->real^3) (Ri:real^3->real^3) (cb:real^2->real^2)
           (Theta:real^3->real^3) (e0:real) (x:real^3) =
    if --(&2 / &5) < x$3 / norm x then Theta(sch_cap_collar e0 (inv(norm x) % x))
    else g(sch5b_pp Ri cb x)`;;

let SCH5B_S1_AGREE = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 t.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\
     t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\ t$3 < &1 / &4
     ==> sch5b_pp Ri cb t = g'(Theta(sch_cap_collar e0 t)) /\
         g(sch5b_pp Ri cb t) = Theta(sch_cap_collar e0 t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "EQ"))))) THEN
  MP_TAC(SPEC `t:real^3` SCH5B_PHI_NORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch5b_phi t IN annulus (&3 / &4) (&2) /\
                sch5b_phi t IN annulus (&1 / &2) (&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    TRY(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_cap_collar e0 t = sch5b_ell(sch5b_phi t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e0:real`; `t:real^3`] SCH5C_COLLAR_CYL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCH5B_PHI_ELL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL (sch5b_bvars10 @ [`sch5b_phi t`]) SCH5B_FB_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch5b_pp Ri cb t = sch5b_sti Ri (sch5b_fb R g' Theta (sch5b_phi t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[sch5b_pp] THEN AP_TERM_TAC THEN USE_THEN "EQ" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let SCH5B_S1_SPHERE = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 t.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ t IN sphere(vec 0,&1)
     ==> (--(&9 / &20) < t$3 ==> sch5b_s1 g Ri cb Theta e0 t = Theta(sch_cap_collar e0 t)) /\
         (t$3 < &1 / &4 ==> sch5b_s1 g Ri cb Theta e0 t = g(sch5b_pp Ri cb t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(t:real^3) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[sch5b_s1; REAL_DIV_1; REAL_INV_1; VECTOR_MUL_LID] THEN
  CONJ_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_AGREE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_AGREE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

let SCH5B_S1_HOMOG = prove
 (`!(g:real^3->real^3) Ri (cb:real^2->real^2) (Theta:real^3->real^3) e0 x.
     ~(x = vec 0)
     ==> sch5b_s1 g Ri cb Theta e0 x = sch5b_s1 g Ri cb Theta e0 (inv(norm x) % x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(inv(norm x) % x:real^3) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sch5b_s1; REAL_DIV_1; REAL_INV_1; VECTOR_MUL_LID; sch5b_pp] THEN
  ASM_SIMP_TAC[CONJUNCT2(CONJUNCT2 SCH5B_PHI_FACTS)] THEN
  REWRITE_TAC[VECTOR_MUL_COMPONENT; real_div; REAL_MUL_AC]);;

let SCH5B_S1_SMOOTH = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16
     ==> smooth_map_on {x | ~(x = vec 0)} (sch5b_s1 g Ri cb Theta e0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `diffeomorphism_on (sch5v_slab(&3 / &2))
                  (IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))) Theta Theta' /\
                sch_neck (g:real^3->real^3) g'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sch5b_pancake (g:real^3->real^3) g' a lam c c' Theta Theta'` THEN
    SIMP_TAC[sch5b_pancake];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real`; `Theta:real^3->real^3`; `Theta':real^3->real^3`;
                 `sch5v_slab(&3 / &2)`] SCH5C_THETA_COLLAR) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  ABBREV_TAC `U1 = {x:real^3 | ~(x = vec 0) /\ --(&2 / &5) * norm x < x$3}` THEN
  ABBREV_TAC `U2 = {x:real^3 | ~(x = vec 0) /\ x$3 < --(&7 / &20) * norm x}` THEN
  SUBGOAL_THEN `open(U1:real^3->bool) /\ open(U2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U1"; "U2"] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{x:real^3 | ~(x = vec 0) /\ --(&2 / &5) * norm x < x$3} =
                    {x | x IN {x:real^3 | ~(x = vec 0)} /\ &0 < x$3 + &2 / &5 * norm x}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC];
      SUBGOAL_THEN `{x:real^3 | ~(x = vec 0) /\ x$3 < --(&7 / &20) * norm x} =
                    {x | x IN {x:real^3 | ~(x = vec 0)} /\ &0 < --(x$3) - &7 / &20 * norm x}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC]] THEN
    MATCH_MP_TAC SCH5C_OPEN_POS THEN REWRITE_TAC[OPEN_NONZERO] THEN
    SCH5C_SMOOTH_TAC THEN REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. ~(x = vec 0)
                ==> norm(inv(norm x) % x) = &1 /\
                    (inv(norm x) % x)$3 = x$3 / norm x /\
                    inv(norm x) % x IN sphere(vec 0,&1)` (LABEL_TAC "NRM") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(inv(norm x) % x:real^3) = &1` ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; VECTOR_MUL_COMPONENT] THEN REWRITE_TAC[real_div; REAL_MUL_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U1 (sch5b_s1 g Ri cb Theta e0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `((Theta:real^3->real^3) o sch_cap_collar e0) o (\x:real^3. inv(norm x) % x)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "U1" THEN REWRITE_TAC[IN_ELIM_THM; o_THM; sch5b_s1] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `--(&2 / &5) < (x:real^3)$3 / norm x` (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `sch5c_cone` THEN
    ASM_REWRITE_TAC[SCH5C_CONE_FACTS] THEN CONJ_TAC THENL
     [EXPAND_TAC "U1" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      USE_THEN "NRM" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `x:real^3` th) (ASSUME `~(x = vec 0:real^3)`))) THEN
      ASM_REWRITE_TAC[sch5c_cone; IN_ELIM_THM] THEN
      SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE] THEN EXPAND_TAC "U1" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U2 (sch5b_s1 g Ri cb Theta e0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `(g:real^3->real^3) o sch5b_sti Ri o (cb:real^2->real^2) o sch5b_phi` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "U2" THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      USE_THEN "NRM" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `x:real^3` th) (ASSUME `~(x = vec 0:real^3)`))) THEN
      SUBGOAL_THEN `(inv(norm x) % x:real^3)$3 < &1 / &4` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `Ri:real^3->real^3`; `cb:real^2->real^2`;
                     `Theta:real^3->real^3`; `e0:real`; `x:real^3`] SCH5B_S1_HOMOG) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `inv(norm x) % x:real^3`]) SCH5B_S1_SPHERE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
      ASM_SIMP_TAC[sch5b_pp; CONJUNCT2(CONJUNCT2 SCH5B_PHI_FACTS)];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SCH5_SPHERE_IN_ANNULUS THEN
      MP_TAC(ISPECL sch5b_bvars10 SCH5B_ST_PTOP) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `sch_neck (g:real^3->real^3) g'` THEN
      SIMP_TAC[sch_neck; diffeomorphism_on]] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MP_TAC(ISPECL sch5b_bvars10 SCH5B_ST_PTOP) THEN ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `ball(vec 0:real^2,&2)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "U2" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      USE_THEN "NRM" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `x:real^3` th) (ASSUME `~(x = vec 0:real^3)`))) THEN
      ASM_SIMP_TAC[GSYM(CONJUNCT2(CONJUNCT2 SCH5B_PHI_FACTS))] THEN
      MP_TAC(SPEC `inv(norm x) % x:real^3` SCH5B_PHI_NORM) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^3)$3 / norm x < &1 / &4` ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[IN_BALL_0];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `{x:real^3 | ~(x = vec 0) /\ x$3 < norm x}` THEN
      REWRITE_TAC[SCH5B_PHI_SMOOTH] THEN EXPAND_TAC "U2" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `x:real^3` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `sch_ball (cb:real^2->real^2) cb'` THEN
      SIMP_TAC[sch_ball; diffeomorphism_on]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `--(&2 / &5) * norm(x:real^3) < x$3` THENL
   [EXISTS_TAC `U1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "U1" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    EXISTS_TAC `U2:real^3->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "U2" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `&0 < norm(x:real^3)` MP_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* s1 is injective on the sphere and an immersion along it.                  *)
(* ------------------------------------------------------------------------- *)

(* The cap part (t3 > -1/4) and the disc part (t3 < -1/4) have disjoint      *)
(* images: a cap point on S lies in the band above height -9/8.              *)

let SCH5B_S1_CROSS = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 u v.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16 /\
     u IN sphere(vec 0,&1) /\ u$3 < --(&1 / &4) /\
     v IN sphere(vec 0,&1) /\ --(&1 / &4) < v$3
     ==> ~(g(sch5b_pp Ri cb u) = Theta(sch_cap_collar e0 v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  MP_TAC(SPEC `v:real^3` SCH5C_SPHERE_IN_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `sch_cap_collar e0 v IN sch5v_slab(&3 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5C_COLLAR_IN_SLAB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(sch_cap_collar e0 v)$3 = -- &1 + (v:real^3)$3 / &2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e0:real`; `v:real^3`] SCH5C_COLLAR_SPHERE_FORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_3];
    ALL_TAC] THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_PP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `u:real^3`) (MP_TAC o SPEC `u:real^3` o
    CONJUNCT1 o CONJUNCT2)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(sch_cap_collar e0 v)$1 pow 2 + (sch_cap_collar e0 v)$2 pow 2 = &1`
  ASSUME_TAC THENL
   [UNDISCH_TAC `sch5b_pancake (g:real^3->real^3) g' a lam c c' Theta Theta'` THEN
    REWRITE_TAC[sch5b_pancake] THEN
    DISCH_THEN(MP_TAC o SPEC `sch_cap_collar e0 v` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `(Theta:real^3->real^3)(sch_cap_collar e0 v)`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `sch5b_pp Ri cb u` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_DISC_BAND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `sch_cap_collar e0 v`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`v:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `(g':real^3->real^3)((Theta:real^3->real^3)(sch_cap_collar e0 v)) =
                sch5b_pp Ri cb u` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `(Theta:real^3->real^3)(sch_cap_collar e0 v)`)) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `sch5b_pp Ri cb u`]
      SCH5_NECK_FACTS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN
      UNDISCH_TAC `sch5b_pancake (g:real^3->real^3) g' a lam c c' Theta Theta'` THEN
      SIMP_TAC[sch5b_pancake];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SCH5B_S1_INJ_CASES = prove
 (`!a b. (--(&9 / &20) < a /\ --(&9 / &20) < b) \/ (a < &1 / &4 /\ b < &1 / &4) \/
         (a < --(&1 / &4) /\ --(&1 / &4) < b) \/ (b < --(&1 / &4) /\ --(&1 / &4) < a)`,
  REAL_ARITH_TAC);;

let SCH5B_S1_INJ = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16
     ==> !t t'. t IN sphere(vec 0,&1) /\ t' IN sphere(vec 0,&1) /\
                sch5b_s1 g Ri cb Theta e0 t = sch5b_s1 g Ri cb Theta e0 t'
                ==> t = t'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`t:real^3`; `t':real^3`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN `diffeomorphism_on (sch5v_slab(&3 / &2))
                  (IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))) Theta Theta' /\
                sch_neck (g:real^3->real^3) g'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sch5b_pancake (g:real^3->real^3) g' a lam c c' Theta Theta'` THEN
    SIMP_TAC[sch5b_pancake];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1) ==> (g':real^3->real^3)(g x) = x`
  (LABEL_TAC "GI") THENL
   [UNDISCH_TAC `sch_neck (g:real^3->real^3) g'` THEN
    REWRITE_TAC[sch_neck; diffeomorphism_on] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real`; `Theta:real^3->real^3`; `Theta':real^3->real^3`;
                 `sch5v_slab(&3 / &2)`] SCH5C_THETA_COLLAR) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(LABEL_TAC "TI" o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_SPHERE) THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t':real^3`]) SCH5B_S1_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C2") (LABEL_TAC "D2")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (LABEL_TAC "D1")) THEN
  MP_TAC(SPECL [`(t:real^3)$3`; `(t':real^3)$3`] SCH5B_S1_INJ_CASES) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [USE_THEN "TI" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "C1" (fun th -> REWRITE_TAC[GSYM(MP th
      (ASSUME `--(&9 / &20) < (t:real^3)$3`))]) THEN
    USE_THEN "C2" (fun th -> REWRITE_TAC[GSYM(MP th
      (ASSUME `--(&9 / &20) < (t':real^3)$3`))]) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(g:real^3->real^3)(sch5b_pp Ri cb t) = g(sch5b_pp Ri cb t')` MP_TAC THENL
     [USE_THEN "D1" (fun th -> REWRITE_TAC[GSYM(MP th
        (ASSUME `(t:real^3)$3 < &1 / &4`))]) THEN
      USE_THEN "D2" (fun th -> REWRITE_TAC[GSYM(MP th
        (ASSUME `(t':real^3)$3 < &1 / &4`))]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL sch5b_bvars12 SCH5B_PP_FACTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PA") (LABEL_TAC "PB")) THEN
    USE_THEN "PA" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (CONJ (ASSUME `(t:real^3) IN sphere(vec 0,&1)`)
      (ASSUME `(t:real^3)$3 < &1 / &4`)))) THEN
    USE_THEN "PA" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (CONJ (ASSUME `(t':real^3) IN sphere(vec 0,&1)`)
      (ASSUME `(t':real^3)$3 < &1 / &4`)))) THEN
    DISCH_THEN(MP_TAC o AP_TERM `g':real^3->real^3`) THEN
    USE_THEN "GI" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `sch5b_pp Ri cb t IN sphere(vec 0,&1)`)]) THEN
    USE_THEN "GI" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `sch5b_pp Ri cb t' IN sphere(vec 0,&1)`)]) THEN
    DISCH_TAC THEN
    USE_THEN "PB" (MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`; `t':real^3`]) SCH5B_S1_CROSS) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "D1" (fun th -> REWRITE_TAC[GSYM(MP th (MP (REAL_ARITH
      `(t:real^3)$3 < --(&1 / &4) ==> t$3 < &1 / &4`) (ASSUME `(t:real^3)$3 < --(&1 / &4)`)))]) THEN
    USE_THEN "C2" (fun th -> REWRITE_TAC[GSYM(MP th (MP (REAL_ARITH
      `--(&1 / &4) < (t':real^3)$3 ==> --(&9 / &20) < t'$3`)
      (ASSUME `--(&1 / &4) < (t':real^3)$3`)))]) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t':real^3`; `t:real^3`]) SCH5B_S1_CROSS) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "D2" (fun th -> REWRITE_TAC[GSYM(MP th (MP (REAL_ARITH
      `(t':real^3)$3 < --(&1 / &4) ==> t'$3 < &1 / &4`) (ASSUME `(t':real^3)$3 < --(&1 / &4)`)))]) THEN
    USE_THEN "C1" (fun th -> REWRITE_TAC[GSYM(MP th (MP (REAL_ARITH
      `--(&1 / &4) < (t:real^3)$3 ==> --(&9 / &20) < t$3`)
      (ASSUME `--(&1 / &4) < (t:real^3)$3`)))]) THEN
    ASM_REWRITE_TAC[]]);;

let SCH5B_S1_IMM = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16
     ==> !t v. t IN sphere(vec 0,&1) /\ orthogonal t v /\
               frechet_derivative (sch5b_s1 g Ri cb Theta e0) (at t) v = vec 0
               ==> v = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`t:real^3`; `v:real^3`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `diffeomorphism_on (sch5v_slab(&3 / &2))
                  (IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))) Theta Theta' /\
                sch_neck (g:real^3->real^3) g'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sch5b_pancake (g:real^3->real^3) g' a lam c c' Theta Theta'` THEN
    SIMP_TAC[sch5b_pancake];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_s1 g Ri cb Theta e0 differentiable (at t)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCH5B_S1_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `a:real`; `lam:real`; `c:real^2->real^2`;
                            `c':real^2->real^2`; `Theta':real^3->real^3`; `R:real^3->real^3`;
                            `cb':real^2->real^2`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `vec 0 IN sphere(vec 0:real^3,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `--(&9 / &20) < (t:real^3)$3` THENL
   [MP_TAC(SPEC `t:real^3` SCH5C_SPHERE_IN_CONE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`e0:real`; `Theta:real^3->real^3`; `Theta':real^3->real^3`;
                   `sch5v_slab(&3 / &2)`] SCH5C_THETA_COLLAR) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^3` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`sch5b_s1 g Ri cb Theta e0`; `(Theta:real^3->real^3) o sch_cap_collar e0`;
                   `t:real^3`; `(t:real^3)$3 + &9 / &20`] SCH5_SPHERE_TANGENT_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `--(&9 / &20) < (t:real^3)$3` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `x:real^3`]) SCH5B_S1_SPHERE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_PP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "PA" o CONJUNCT1) THEN
  MP_TAC(ISPECL sch5b_bvars10 SCH5B_ST_PTOP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "S1") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(vec 0,&2) ==> (cb':real^2->real^2)(cb z) = z /\
                                                  cb z IN IMAGE cb (ball(vec 0,&2))`
  (LABEL_TAC "CB") THENL
   [UNDISCH_TAC `sch_ball (cb:real^2->real^2) cb'` THEN
    REWRITE_TAC[sch_ball; diffeomorphism_on] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  USE_THEN "PA" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (CONJ (ASSUME `(t:real^3) IN sphere(vec 0,&1)`)
    (MP (REAL_ARITH `~(--(&9 / &20) < (t:real^3)$3) ==> t$3 < &1 / &4`)
        (ASSUME `~(--(&9 / &20) < (t:real^3)$3)`))))) THEN
  SUBGOAL_THEN `!v. orthogonal (t:real^3) v /\
                    frechet_derivative (sch5b_s1 g Ri cb Theta e0) (at t) v = vec 0
                    ==> v = vec 0` (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC(ISPECL [`sch5b_s1 g Ri cb Theta e0`;
                       `sch5b_phii o (cb':real^2->real^2) o sch5b_st R o (g':real^3->real^3)`;
                       `t:real^3`; `--(&1 / &4) - (t:real^3)$3`] SCH5B_LINV_IMMERSION) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `~(--(&9 / &20) < (t:real^3)$3)` THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `sch5b_s1 g Ri cb Theta e0 t = g(sch5b_pp Ri cb t)` SUBST1_TAC THENL
     [MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_SPHERE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
      UNDISCH_TAC `~(--(&9 / &20) < (t:real^3)$3)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `sch5b_pp Ri cb t`]
      SCH5_NECK_FACTS) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[o_THM] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `{x:real^3 | ((R:real^3->real^3) x)$3 < &1}` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        USE_THEN "S1" (fun th -> MP_TAC(MATCH_MP th
          (CONJ (ASSUME `sch5b_pp Ri cb t IN sphere(vec 0,&1)`)
                (ASSUME `~(sch5b_pp Ri cb t = (g':real^3->real^3)((Theta:real^3->real^3)
                           (vector[&1; &0; &4 / &3])))`)))) THEN
        SIMP_TAC[];
        ASM_REWRITE_TAC[o_THM] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `IMAGE (cb:real^2->real^2) (ball(vec 0,&2))` THEN
        UNDISCH_TAC `sch_ball (cb:real^2->real^2) cb'` THEN
        REWRITE_TAC[sch_ball; diffeomorphism_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[FUN_IN_IMAGE]];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV; SCH5B_PHI_SMOOTH]];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3)$3 < --(&1 / &4)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`x - t:real^3`; `3`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; GSYM dist; DIMINDEX_3; ARITH] THEN
      UNDISCH_TAC `dist(x:real^3,t) < --(&1 / &4) - t$3` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "PA" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (CONJ (ASSUME `(x:real^3) IN sphere(vec 0,&1)`)
      (MP (REAL_ARITH `(x:real^3)$3 < --(&1 / &4) ==> x$3 < &1 / &4`)
          (ASSUME `(x:real^3)$3 < --(&1 / &4)`))))) THEN
    SUBGOAL_THEN `sch5b_s1 g Ri cb Theta e0 x = g(sch5b_pp Ri cb x)` SUBST1_TAC THENL
     [MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `x:real^3`]) SCH5B_S1_SPHERE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
      UNDISCH_TAC `(x:real^3)$3 < --(&1 / &4)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `sch5b_pp Ri cb x`]
      SCH5_NECK_FACTS) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[o_THM] THEN
    USE_THEN "CB" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP th
      (ASSUME `sch5b_phi x IN ball(vec 0,&2)`))]) THEN
    MP_TAC(CONJUNCT1 SCH5B_PHI_FACTS) THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3)$3 < --(&1 / &4)` THEN REAL_ARITH_TAC;
      SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The cofactor conormal of s against a map A that agrees with               *)
(* Ds on the tangent plane (n . A t = det A), and constant sign of a         *)
(* continuous nonvanishing function on the band -9/20 < t3 < -1/4 of the     *)
(* sphere.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SCH5B_CONORMAL_ALG = prove
 (`!a b c w t:real^3.
     (t$1 % ((b + t$2 % w) cross (c + t$3 % w)) +
      t$2 % ((c + t$3 % w) cross (a + t$1 % w)) +
      t$3 % ((a + t$1 % w) cross (b + t$2 % w))) dot (t$1 % a + t$2 % b + t$3 % c) =
     (t dot t) * ((a cross b) dot c)`,
  REWRITE_TAC[DOT_3; CROSS_COMPONENTS; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

let SCH5B_CONORMAL_DET = prove
 (`!(s:real^3->real^3) (A:real^3->real^3) t.
     norm t = &1 /\ s differentiable (at t) /\ linear A /\
     (!v. orthogonal t v ==> frechet_derivative s (at t) v = A v)
     ==> sch5_conormal s t dot A t = det(matrix A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `D = frechet_derivative (s:real^3->real^3) (at t)` THEN
  SUBGOAL_THEN `linear(D:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3) dot t = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!j. 1 <= j /\ j <= 3
                    ==> (D:real^3->real^3)(basis j) =
                        (A:real^3->real^3)(basis j) + (t:real^3)$j % (D t - A t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `basis j:real^3 = (t:real^3)$j % t + (basis j - t$j % t)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `orthogonal (t:real^3) (basis j - t$j % t)` ASSUME_TAC THENL
     [REWRITE_TAC[orthogonal; DOT_RSUB; DOT_RMUL] THEN
      ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear(A:real^3->real^3)`)]) THEN
    REWRITE_TAC[MATCH_MP LINEAR_CMUL (ASSUME `linear(A:real^3->real^3)`)] THEN
    SUBGOAL_THEN `(D:real^3->real^3)(basis j - (t:real^3)$j % t) = A(basis j - t$j % t)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP LINEAR_SUB (ASSUME `linear(A:real^3->real^3)`);
                MATCH_MP LINEAR_CMUL (ASSUME `linear(A:real^3->real^3)`)] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^3->real^3) t = (t:real^3)$1 % A(basis 1) + t$2 % A(basis 2) +
                                       t$3 % A(basis 3)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    REWRITE_TAC[DIMINDEX_3; VSUM_3] THEN
    REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear(A:real^3->real^3)`);
                MATCH_MP LINEAR_CMUL (ASSUME `linear(A:real^3->real^3)`)];
    ALL_TAC] THEN
  SUBGOAL_THEN `det(matrix(A:real^3->real^3)) =
                (A(basis 1) cross A(basis 2)) dot A(basis 3)` SUBST1_TAC THENL
   [SIMP_TAC[DET_3; matrix; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[DOT_3; CROSS_COMPONENTS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[sch5_conormal] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 3 /\ 1 <= 2 /\ 2 <= 3 /\ 3 <= 3`] THEN
  REWRITE_TAC[SCH5B_CONORMAL_ALG] THEN ASM_REWRITE_TAC[REAL_MUL_LID]);;

let SCH5B_SPHERE_BAND_CONNECTED = prove
 (`connected {t:real^3 | t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\ t$3 < --(&1 / &4)}`,
  SUBGOAL_THEN
   `{t:real^3 | t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\ t$3 < --(&1 / &4)} =
    IMAGE (\y:real^3. vector[sqrt(&1 - y$3 pow 2) * y$1; sqrt(&1 - y$3 pow 2) * y$2;
                             y$3]:real^3)
          (sch5b_band (--(&9 / &20)) (--(&1 / &4)))` SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^3` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; sch5b_band; IN_SPHERE_0; NORM_EQ_1; DOT_3] THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `&0 < &1 - (t:real^3)$3 pow 2` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&0 < &1 - x pow 2 <=> x pow 2 < &1 pow 2`] THEN
        REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < sqrt(&1 - (t:real^3)$3 pow 2)` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `vector[(t:real^3)$1 / sqrt(&1 - t$3 pow 2); t$2 / sqrt(&1 - t$3 pow 2);
                         t$3]:real^3` THEN
      ASM_REWRITE_TAC[VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      ASM_SIMP_TAC[REAL_POW_DIV; SQRT_POW_2; REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `~(&1 - (t:real^3)$3 pow 2 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(t:real^3)$1 * t$1 + t$2 * t$2 + t$3 * t$3 = &1` THEN
      CONV_TAC REAL_FIELD;
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_3] THEN
      SUBGOAL_THEN `&0 <= &1 - (y:real^3)$3 pow 2` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&0 <= &1 - x pow 2 <=> x pow 2 <= &1 pow 2`] THEN
        REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `sqrt(&1 - (y:real^3)$3 pow 2) * sqrt(&1 - y$3 pow 2) = &1 - y$3 pow 2`
      MP_TAC THENL [ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 = &1` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[SCH5B_BAND_CONNECTED] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `{y:real^3 | y$3 > --(&1)} INTER {y | y$3 < &1}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    SUBGOAL_THEN `open({y:real^3 | y$3 > --(&1)} INTER {y | y$3 < &1})` ASSUME_TAC THENL
     [SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT];
      ALL_TAC] THEN
    SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN
    GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `&0 < &1 - x pow 2 <=> x pow 2 < &1 pow 2`] THEN
    REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; sch5b_band; IN_INTER; IN_ELIM_THM; real_gt] THEN REAL_ARITH_TAC]);;

let SCH5B_BAND_SIGN = prove
 (`!f:real^3->real.
     (\t. lift(f t)) continuous_on
       {t | t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\ t$3 < --(&1 / &4)} /\
     (!t. t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\ t$3 < --(&1 / &4) ==> ~(f t = &0))
     ==> ?sg. (sg = &1 \/ sg = -- &1) /\
              !t. t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\ t$3 < --(&1 / &4)
                  ==> &0 < sg * f t`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = {t:real^3 | t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\
                              t$3 < --(&1 / &4)}` THEN
  SUBGOAL_THEN `(vector[sqrt(&91 / &100); &0; --(&3 / &10)]:real^3) IN B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM; IN_SPHERE_0; NORM_EQ_1; DOT_3; VECTOR_3] THEN
    SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_ARITH `&0 <= &91 / &100`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `t0 = vector[sqrt(&91 / &100); &0; --(&3 / &10)]:real^3` THEN
  SUBGOAL_THEN `connected(IMAGE (\t. lift((f:real^3->real) t)) B)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[SCH5B_SPHERE_BAND_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t t'. t IN B /\ t' IN B /\ (f:real^3->real) t <= &0 /\ &0 <= f t' ==> F`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (\t. lift((f:real^3->real) t)) B`; `lift((f:real^3->real) t)`;
                   `lift((f:real^3->real) t')`; `&0`; `1`] CONNECTED_IVT_COMPONENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop; LIFT_DROP] THEN
      REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THENL
       [EXISTS_TAC `t:real^3`; EXISTS_TAC `t':real^3`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; GSYM drop] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^1` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    UNDISCH_TAC `(u:real^3) IN B` THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((f:real^3->real) t0 = &0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
      check (fun th -> not(can (term_match [] `!t t':real^3. (P:real^3->real^3->bool) t t' ==> F`) (concl th)))) THEN
    UNDISCH_TAC `(t0:real^3) IN B` THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  EXISTS_TAC `if &0 < (f:real^3->real) t0 then &1 else -- &1` THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:real^3) IN B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `~((f:real^3->real) t = &0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
      check (fun th -> not(can (term_match [] `!t t':real^3. (P:real^3->real^3->bool) t t' ==> F`) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real^3`; `t0:real^3`] o
      check (can (term_match [] `!t t':real^3. (P:real^3->real^3->bool) t t' ==> F`) o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`t0:real^3`; `t:real^3`] o
      check (can (term_match [] `!t t':real^3. (P:real^3->real^3->bool) t t' ==> F`) o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The blend of a signed tube map of s with a map Gc defined                 *)
(* on the cone c = x3/|x| > -9/20 (weight chi = smooth_step(20(c + 2/5))),   *)
(* its smoothness on the shell 1/2 < |x| < 2 and its radial derivative at    *)
(* sphere points.                                                            *)
(* ------------------------------------------------------------------------- *)

let sch5b_chi = new_definition
 `sch5b_chi (x:real^3) = smooth_step(&20 * (x$3 / norm x + &2 / &5))`;;

let sch5b_tube = new_definition
 `sch5b_tube (s:real^3->real^3) sg (x:real^3) =
    s(inv(norm x) % x) + (sg * (norm x - &1)) % sch5_conormal s (inv(norm x) % x)`;;

let sch5b_blend = new_definition
 `sch5b_blend (s:real^3->real^3) (Gc:real^3->real^3) sg (x:real^3) =
    if x IN sch5c_cone then (&1 - sch5b_chi x) % sch5b_tube s sg x + sch5b_chi x % Gc x
    else sch5b_tube s sg x`;;

let SCH5B_CHI_FACTS = prove
 (`smooth_map_on {x:real^3 | ~(x = vec 0)} (\x. lift(sch5b_chi x)) /\
   (!x:real^3. x$3 / norm x <= --(&2 / &5) ==> sch5b_chi x = &0) /\
   (!x:real^3. --(&7 / &20) <= x$3 / norm x ==> sch5b_chi x = &1) /\
   (!x:real^3. &0 <= sch5b_chi x /\ sch5b_chi x <= &1) /\
   (!x:real^3 u. ~(x = vec 0) /\ &0 < u ==> sch5b_chi(u % x) = sch5b_chi x)`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[sch5b_chi] THEN SUBGOAL_THEN `open {x:real^3 | ~(x = vec 0)}` ASSUME_TAC THENL
     [REWRITE_TAC[OPEN_NONZERO]; ALL_TAC] THEN
    SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; NORM_EQ_0] THEN SIMP_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[sch5b_chi] THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[sch5b_chi] THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[sch5b_chi; SMOOTH_STEP_BOUNDS];
    REPEAT STRIP_TAC THEN REWRITE_TAC[sch5b_chi; NORM_MUL; VECTOR_MUL_COMPONENT] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < u ==> abs u = u`] THEN
    UNDISCH_TAC `&0 < u` THEN UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD]);;

let SCH5B_TUBE_SMOOTH = prove
 (`!(s:real^3->real^3) sg.
     smooth_map_on {x | ~(x = vec 0)} s
     ==> smooth_map_on {x | ~(x = vec 0)} (sch5b_tube s sg)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open {x:real^3 | ~(x = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_NONZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `!h:real^3->real^3. smooth_map_on {x | ~(x = vec 0)} h
                  ==> smooth_map_on {x:real^3 | ~(x = vec 0)} (\x. h(inv(norm x) % x))`
  (LABEL_TAC "comp") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `{x:real^3 | ~(x = vec 0)}`;
                   `\x:real^3. inv(norm x) % x`; `h:real^3->real^3`]
      SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; NORM_0] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_tube s sg =
                (\x:real^3. s(inv(norm x) % x) +
                            drop((\x. lift(sg * (norm x - &1))) x) %
                            (\x. sch5_conormal s (inv(norm x) % x)) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; sch5b_tube; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "comp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `\x:real^3. lift(sg * (norm x - &1))`;
                 `\x:real^3. sch5_conormal (s:real^3->real^3) (inv(norm x) % x)`]
    SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    USE_THEN "comp" MATCH_MP_TAC THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SCH5_CONORMAL_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let SCH5B_TUBE_RAY = prove
 (`!(s:real^3->real^3) sg t u.
     t IN sphere(vec 0,&1) /\ &0 < u
     ==> sch5b_tube s sg (u % t) = s t + (sg * (u - &1)) % sch5_conormal s t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[sch5b_tube; NORM_MUL; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < u ==> abs u = u`; VECTOR_MUL_ASSOC; REAL_MUL_LINV;
               REAL_LT_IMP_NZ; VECTOR_MUL_LID]);;

let SCH5B_BLEND_SMOOTH = prove
 (`!(s:real^3->real^3) (Gc:real^3->real^3) sg.
     smooth_map_on {x | ~(x = vec 0)} s /\ smooth_map_on sch5c_cone Gc
     ==> smooth_map_on (annulus (&1 / &2) (&2)) (sch5b_blend s Gc sg)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open {x:real^3 | ~(x = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_NONZERO]; ALL_TAC] THEN
  MP_TAC SCH5B_CHI_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->real^3`; `sg:real`] SCH5B_TUBE_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC SCH5C_CONE_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch5c_cone SUBSET {x:real^3 | ~(x = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `U2 = {x:real^3 | ~(x = vec 0) /\ x$3 < --(&2 / &5) * norm x}` THEN
  SUBGOAL_THEN `open(U2:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U2" THEN
    SUBGOAL_THEN `{x:real^3 | ~(x = vec 0) /\ x$3 < --(&2 / &5) * norm x} =
                  {x | x IN {x:real^3 | ~(x = vec 0)} /\ &0 < --(x$3) - &2 / &5 * norm x}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SCH5C_OPEN_POS THEN REWRITE_TAC[OPEN_NONZERO] THEN
    SCH5C_SMOOTH_TAC THEN REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_ANNULUS] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^3) IN sch5c_cone` THENL
   [EXISTS_TAC `sch5c_cone` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\x:real^3. drop(lift(&1 - sch5b_chi x)) % sch5b_tube s sg x +
                           drop(lift(sch5b_chi x)) % (Gc:real^3->real^3) x` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SIMP_TAC[sch5b_blend; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  EXISTS_TAC `U2:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "U2" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `~((x:real^3) IN sch5c_cone)` THEN
    UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&2)` THEN
    REWRITE_TAC[sch5c_cone; annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `&1 / &2 < norm(x:real^3)` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `sch5b_tube s sg` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "U2" THEN SET_TAC[]] THEN
  EXPAND_TAC "U2" THEN REWRITE_TAC[IN_ELIM_THM; sch5b_blend] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `sch5b_chi y = &0` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!x:real^3. x$3 / norm x <= --(&2 / &5) ==> sch5b_chi x = &0`) (concl th))) THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    VECTOR_ARITH_TAC]);;

let SCH5B_VD_LINE = prove
 (`!p w:real^3 u0. ((\u:real^1. p + drop u % w) has_vector_derivative w) (at u0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\u:real^1. p:real^3`; `vec 0:real^3`; `\u:real^1. drop u % (w:real^3)`;
                 `w:real^3`; `at(u0:real^1)`] HAS_VECTOR_DERIVATIVE_ADD) THEN
  REWRITE_TAC[VECTOR_ADD_LID; HAS_VECTOR_DERIVATIVE_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]);;

let SCH5B_BLEND_RAY = prove
 (`!(s:real^3->real^3) (Gc:real^3->real^3) sg t.
     smooth_map_on {x | ~(x = vec 0)} s /\ smooth_map_on sch5c_cone Gc /\
     t IN sphere(vec 0,&1)
     ==> frechet_derivative (sch5b_blend s Gc sg) (at t) t =
         if --(&9 / &20) < t$3
         then (&1 - sch5b_chi t) % (sg % sch5_conormal s t) +
              sch5b_chi t % frechet_derivative Gc (at t) t
         else sg % sch5_conormal s t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH5_RAY_DERIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_SIMP_TAC[OPEN_ANNULUS; SCH5B_BLEND_SMOOTH; SCH5_SPHERE_IN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(t:real^3) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^1. dist(u,lift(&1)) < &1 / &2
                           ==> &1 / &2 < drop u /\ drop u < &3 / &2 /\
                               norm(drop u % t:real^3) = drop u /\
                               (drop u % t:real^3)$3 / norm(drop u % t) = t$3`
  (LABEL_TAC "U") THENL
   [GEN_TAC THEN REWRITE_TAC[dist; NORM_1; DROP_SUB; LIFT_DROP] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 / &2 < drop u /\ drop u < &3 / &2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 / &2 < u ==> abs u = u`] THEN
    UNDISCH_TAC `&1 / &2 < drop u` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\u:real^1. (&1 - sch5b_chi t) % ((s:real^3->real^3) t - sg % sch5_conormal s t +
                                                 drop u % (sg % sch5_conormal s t)) +
                           sch5b_chi t % (Gc:real^3->real^3)(drop u % t)` THEN
    EXISTS_TAC `&1 / &2` THEN REWRITE_TAC[REAL_ARITH `&0 < &1 / &2`] THEN CONJ_TAC THENL
     [X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
      USE_THEN "U" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `dist(u:real^1,lift(&1)) < &1 / &2`))) THEN
      SUBGOAL_THEN `drop u % (t:real^3) IN sch5c_cone` ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 < drop u * ((t:real^3)$3 + &9 / &20)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[sch5c_cone; IN_ELIM_THM; VECTOR_MUL_COMPONENT] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[sch5b_blend] THEN
      SUBGOAL_THEN `sch5b_chi(drop u % t) = sch5b_chi t` SUBST1_TAC THENL
       [MP_TAC SCH5B_CHI_FACTS THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
        CONJ_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `norm(vec 0:real^3) = &1` THEN
          REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`s:real^3->real^3`; `sg:real`; `t:real^3`; `drop u`] SCH5B_TUBE_RAY) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THENL
     [REWRITE_TAC[SCH5B_VD_LINE]; ALL_TAC] THEN
    SUBGOAL_THEN `(\u:real^1. (Gc:real^3->real^3)(drop u % t)) = Gc o (\u. drop u % t)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SCH5_CHAIN_VECTOR THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`vec 0:real^3`; `t:real^3`; `lift(&1)`] SCH5B_VD_LINE) THEN
      REWRITE_TAC[VECTOR_ADD_LID];
      REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID] THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `sch5c_cone` THEN
      ASM_REWRITE_TAC[SCH5C_CONE_FACTS] THEN
      MP_TAC(SPEC `t:real^3` SCH5C_SPHERE_IN_CONE) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\u:real^1. ((s:real^3->real^3) t - sg % sch5_conormal s t) +
                         drop u % (sg % sch5_conormal s t)` THEN
  EXISTS_TAC `&1 / &2` THEN REWRITE_TAC[REAL_ARITH `&0 < &1 / &2`; SCH5B_VD_LINE] THEN
  X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
  USE_THEN "U" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (ASSUME `dist(u:real^1,lift(&1)) < &1 / &2`))) THEN
  SUBGOAL_THEN `~(drop u % (t:real^3) IN sch5c_cone)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= drop u * (--(&9 / &20) - (t:real^3)$3)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[sch5c_cone; IN_ELIM_THM; VECTOR_MUL_COMPONENT] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sch5b_blend] THEN
  MP_TAC(ISPECL [`s:real^3->real^3`; `sg:real`; `t:real^3`; `drop u`] SCH5B_TUBE_RAY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The blended collar is transverse along the sphere, hence a                *)
(* neck by SCH5_NECK_FROM_TRANSVERSE; near the cap it is Gc o radial.        *)
(* ------------------------------------------------------------------------- *)

let SCH5B_BLEND_TRANSVERSE = prove
 (`!(s:real^3->real^3) (Gc:real^3->real^3) sg t.
     smooth_map_on {x | ~(x = vec 0)} s /\ smooth_map_on sch5c_cone Gc /\
     (!t. t IN sphere(vec 0,&1) /\ --(&2 / &5) < t$3 ==> Gc t = s t) /\
     (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v /\ frechet_derivative s (at t) v = vec 0
            ==> v = vec 0) /\
     (!t. t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3
          ==> ~(det(matrix(frechet_derivative Gc (at t))) = &0)) /\
     (sg = &1 \/ sg = -- &1) /\
     (!t. t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\ t$3 < --(&1 / &4)
          ==> &0 < sg * det(matrix(frechet_derivative Gc (at t)))) /\
     t IN sphere(vec 0,&1)
     ==> ~(sch5_conormal s t dot frechet_derivative (sch5b_blend s Gc sg) (at t) t = &0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "AG") (CONJUNCTS_THEN2 (LABEL_TAC "IM")
    (CONJUNCTS_THEN2 (LABEL_TAC "DET") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "SG") ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `norm(t:real^3) = &1 /\ ~(t = vec 0:real^3)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[GSYM NORM_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^3->real^3) differentiable (at t)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(sch5_conormal (s:real^3->real^3) t = vec 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5_CONORMAL_NZ THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "IM" MATCH_MP_TAC THEN EXISTS_TAC `t:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sch5_conormal (s:real^3->real^3) t dot sch5_conormal s t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->real^3`; `Gc:real^3->real^3`; `sg:real`; `t:real^3`]
    SCH5B_BLEND_RAY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC SCH5B_CHI_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch5b_chi t = &0 \/ --(&2 / &5) < (t:real^3)$3` MP_TAC THENL
   [ASM_CASES_TAC `--(&2 / &5) < (t:real^3)$3` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!x:real^3. x$3 / norm x <= --(&2 / &5) ==> sch5b_chi x = &0`) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_DIV_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    REWRITE_TAC[COND_ID; DOT_RMUL] THEN
    UNDISCH_TAC `sg = &1 \/ sg = -- &1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ARITH `--(&2 / &5) < t ==> --(&9 / &20) < t`] THEN
  SUBGOAL_THEN `--(&9 / &20) < (t:real^3)$3` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `t:real^3` SCH5C_SPHERE_IN_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(Gc:real^3->real^3) differentiable (at t)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `sch5c_cone` THEN
    ASM_REWRITE_TAC[SCH5C_CONE_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5_conormal (s:real^3->real^3) t dot frechet_derivative Gc (at t) t =
                det(matrix(frechet_derivative (Gc:real^3->real^3) (at t)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5B_CONORMAL_DET THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE] THEN
    MP_TAC(ISPECL [`s:real^3->real^3`; `Gc:real^3->real^3`; `t:real^3`;
                   `(t:real^3)$3 + &2 / &5`] SCH5_SPHERE_TANGENT_EQ) THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "AG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`x - t:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; GSYM dist; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "DET" (MP_TAC o SPEC `t:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `dd = det(matrix(frechet_derivative (Gc:real^3->real^3) (at t)))` THEN
  ABBREV_TAC `k = sch5b_chi t` THEN
  ABBREV_TAC `nn = sch5_conormal (s:real^3->real^3) t dot sch5_conormal s t` THEN
  SUBGOAL_THEN `&0 <= k /\ k <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `--(&7 / &20) <= (t:real^3)$3` THENL
   [SUBGOAL_THEN `k = &1` SUBST1_TAC THENL
     [EXPAND_TAC "k" THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x:real^3. --(&7 / &20) <= x$3 / norm x ==> sch5b_chi x = &1`) (concl th))) THEN
      ASM_REWRITE_TAC[REAL_DIV_1];
      UNDISCH_TAC `~(dd = &0)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "SG" (MP_TAC o SPEC `t:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sg * ((&1 - k) * sg * nn + k * dd)` ASSUME_TAC THENL
   [SUBGOAL_THEN `sg * ((&1 - k) * sg * nn + k * dd) = (&1 - k) * (sg * sg) * nn + k * (sg * dd)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sg * sg = &1` SUBST1_TAC THENL
     [UNDISCH_TAC `sg = &1 \/ sg = -- &1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `k = &0` THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < nn` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `k <= &1` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `&0 < nn` THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`&0 <= k`; `~(k = &0)`] THEN REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `&0 < sg * ((&1 - k) * sg * nn + k * dd)` THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL]);;

let SCH5B_DIR_COMPONENT = prove
 (`!x y:real^3. inv(norm x) % x = inv(norm y) % y ==> x$3 / norm x = y$3 / norm y`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `\z:real^3. z$3`) THEN
  REWRITE_TAC[VECTOR_MUL_COMPONENT; real_div] THEN REAL_ARITH_TAC);;

let SCH5B_BLEND_NECK = prove
 (`!(s:real^3->real^3) (Gc:real^3->real^3) sg.
     smooth_map_on {x | ~(x = vec 0)} s /\ smooth_map_on sch5c_cone Gc /\
     (!t. t IN sphere(vec 0,&1) /\ --(&2 / &5) < t$3 ==> Gc t = s t) /\
     (!x y. x IN sphere(vec 0,&1) /\ y IN sphere(vec 0,&1) /\ s x = s y ==> x = y) /\
     (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v /\ frechet_derivative s (at t) v = vec 0
            ==> v = vec 0) /\
     (!t. t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3
          ==> ~(det(matrix(frechet_derivative Gc (at t))) = &0)) /\
     (sg = &1 \/ sg = -- &1) /\
     (!t. t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\ t$3 < --(&1 / &4)
          ==> &0 < sg * det(matrix(frechet_derivative Gc (at t))))
     ==> ?eta g1 g1'. &0 < eta /\ eta < &1 /\ sch_neck g1 g1' /\
                      (!t. t IN sphere(vec 0,&1) ==> g1 t = s t) /\
                      (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v
                             ==> frechet_derivative g1 (at t) v =
                                 frechet_derivative s (at t) v) /\
                      (!x. x IN sch_capcone ==> g1 x = Gc(sch5_radial (eta / &2) x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC SCH5B_CHI_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sch5b_blend s Gc sg`; `s:real^3->real^3`; `sch5_conormal (s:real^3->real^3)`;
                 `annulus (&1 / &2) (&2):real^3->bool`] SCH5_NECK_FROM_TRANSVERSE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN REWRITE_TAC[SCH5_SPHERE_IN_ANNULUS];
      MATCH_MP_TAC SCH5B_BLEND_SMOOTH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN REAL_ARITH_TAC;
      X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`s:real^3->real^3`; `sg:real`; `t:real^3`; `&1`] SCH5B_TUBE_RAY) THEN
      ASM_REWRITE_TAC[REAL_LT_01; VECTOR_MUL_LID; REAL_SUB_REFL; REAL_MUL_RZERO;
                      VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      DISCH_TAC THEN REWRITE_TAC[sch5b_blend] THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `--(&2 / &5) < (t:real^3)$3` THENL
       [SUBGOAL_THEN `(Gc:real^3->real^3) t = s t` SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
            `!t:real^3. t IN sphere(vec 0,&1) /\ --(&2 / &5) < t$3 ==> (Gc:real^3->real^3) t = (s:real^3->real^3) t`) (concl th))) THEN
          ASM_REWRITE_TAC[];
          VECTOR_ARITH_TAC];
        SUBGOAL_THEN `sch5b_chi t = &0` SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
            `!x:real^3. x$3 / norm x <= --(&2 / &5) ==> sch5b_chi x = &0`) (concl th))) THEN
          UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
          SIMP_TAC[IN_SPHERE_0; REAL_DIV_1] THEN
          UNDISCH_TAC `~(--(&2 / &5) < (t:real^3)$3)` THEN REAL_ARITH_TAC;
          VECTOR_ARITH_TAC]];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH5_CONORMAL_ORTH THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
      ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `vec 0 IN sphere(vec 0:real^3,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
      X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC SCH5B_BLEND_TRANSVERSE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (X_CHOOSE_THEN `G':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`eta:real`; `sch5b_blend s Gc sg o sch5_radial (eta / &2)`;
                        `sch5_radinv (eta / &2) o (G':real^3->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(x:real^3) IN annulus (&1 / &2) (&2) /\ ~(x = vec 0) /\
                --(&1 / &4) < x$3 / norm x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN sch_capcone` THEN
    REWRITE_TAC[sch_capcone; annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 / &2 < norm(vec 0:real^3)` THEN
      REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
       [UNDISCH_TAC `&1 / &2 < norm(x:real^3)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eta / &2`; `x:real^3`] SCH5_RADIAL_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ASSUME `&0 < eta`) THEN MP_TAC(ASSUME `eta < &1`) THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ABBREV_TAC `r = sch5_radial (eta / &2) (x:real^3)` THEN
  SUBGOAL_THEN `(r:real^3)$3 / norm r = (x:real^3)$3 / norm x` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5B_DIR_COMPONENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &4 < norm(r:real^3) /\ norm r < &3 / &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(r:real^3) IN annulus (&1 - (eta / &2) / &2) (&1 + eta / &2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    MP_TAC(ASSUME `&0 < eta`) THEN MP_TAC(ASSUME `eta < &1`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^3) IN sch5c_cone` ASSUME_TAC THENL
   [REWRITE_TAC[sch5c_cone; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [MP_TAC(ASSUME `&3 / &4 < norm(r:real^3)`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ASSUME `norm(r:real^3) < &3 / &2`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(r:real^3)` ASSUME_TAC THENL
     [MP_TAC(ASSUME `&3 / &4 < norm(r:real^3)`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `--(&9 / &20) < (r:real^3)$3 / norm r` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC(ASSUME `--(&1 / &4) < (x:real^3)$3 / norm x`) THEN
      REAL_ARITH_TAC;
      SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < norm(r:real^3)`] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_chi r = &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!x:real^3. --(&7 / &20) <= x$3 / norm x ==> sch5b_chi x = &1`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ASSUME `--(&1 / &4) < (x:real^3)$3 / norm x`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sch5b_blend] THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The bottom surgered neck g1: on the sphere it is s1, with                 *)
(* the tangential derivatives of s1, and on the cone of the cap it is the    *)
(* model collar Theta o sch_cap_collar e1.                                   *)
(* ------------------------------------------------------------------------- *)

let SCH5B_BOTTOM_NECK = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16
     ==> ?g1 g1' e1.
           sch_neck g1 g1' /\ &0 < e1 /\ e1 <= &1 / &16 /\
           (!x. x IN sch_capcone ==> g1 x = Theta(sch_cap_collar e1 x)) /\
           (!t. t IN sphere(vec 0,&1) ==> g1 t = sch5b_s1 g Ri cb Theta e0 t) /\
           (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v
                  ==> frechet_derivative g1 (at t) v =
                      frechet_derivative (sch5b_s1 g Ri cb Theta e0) (at t) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN `diffeomorphism_on (sch5v_slab(&3 / &2))
                  (IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))) Theta Theta'`
  ASSUME_TAC THENL
   [UNDISCH_TAC `sch5b_pancake (g:real^3->real^3) g' a lam c c' Theta Theta'` THEN
    SIMP_TAC[sch5b_pancake];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real`; `Theta:real^3->real^3`; `Theta':real^3->real^3`;
                 `sch5v_slab(&3 / &2)`] SCH5C_THETA_COLLAR) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "TD") (K ALL_TAC))) THEN
  SUBGOAL_THEN
   `?sg. (sg = &1 \/ sg = -- &1) /\
         !t. t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\ t$3 < --(&1 / &4)
             ==> &0 < sg * det(matrix(frechet_derivative
                                        ((Theta:real^3->real^3) o sch_cap_collar e0) (at t)))`
  (X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN ASSUME_TAC)) THENL
   [MATCH_MP_TAC SCH5B_BAND_SIGN THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sch5c_cone` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SCH5_DET_DERIV_CONTINUOUS_ON THEN ASM_REWRITE_TAC[SCH5C_CONE_FACTS];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
        MP_TAC(SPEC `t:real^3` SCH5C_SPHERE_IN_CONE) THEN ASM_SIMP_TAC[]];
      X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
      USE_THEN "TD" (MP_TAC o SPEC `t:real^3`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sch5b_s1 g Ri cb Theta e0`; `(Theta:real^3->real^3) o sch_cap_collar e0`;
                 `sg:real`] SCH5B_BLEND_NECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SCH5B_S1_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `a:real`; `lam:real`; `c:real^2->real^2`;
                            `c':real^2->real^2`; `Theta':real^3->real^3`; `R:real^3->real^3`;
                            `cb':real^2->real^2`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_SPHERE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      UNDISCH_TAC `--(&2 / &5) < (t:real^3)$3` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SCH5B_S1_INJ THEN
      MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `a:real`; `lam:real`; `c:real^2->real^2`;
                            `c':real^2->real^2`; `Theta':real^3->real^3`; `R:real^3->real^3`;
                            `cb':real^2->real^2`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SCH5B_S1_IMM THEN
      MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `a:real`; `lam:real`; `c:real^2->real^2`;
                            `c':real^2->real^2`; `Theta':real^3->real^3`; `R:real^3->real^3`;
                            `cb':real^2->real^2`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
      USE_THEN "TD" (MP_TAC o SPEC `t:real^3`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (X_CHOOSE_THEN `g1:real^3->real^3`
    (X_CHOOSE_THEN `g1':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`g1:real^3->real^3`; `g1':real^3->real^3`; `e0 * eta / &2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e0 * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[o_THM] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ARITH `e0 * eta / &2 = e0 * (eta / &2)`] THEN
    MATCH_MP_TAC SCH5C_COLLAR_RADIAL THEN
    UNDISCH_TAC `(x:real^3) IN sch_capcone` THEN REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 / &2 < norm(vec 0:real^3)` THEN
      REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `eta / &2 * --(&1 / &2) <= eta / &2 * (norm(x:real^3) - &1)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        MAP_EVERY UNDISCH_TAC [`&0 < eta`; `&1 / &2 < norm(x:real^3)`] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `eta < &1` THEN REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Locality of images (an embedded sphere near the image of an               *)
(* open part), so that S1 = s1(S^2) and S = g(S^2) agree near g(D), and the  *)
(* height derivative of s1 on the cap.                                       *)
(* ------------------------------------------------------------------------- *)

let SCH5B_LOCAL_IMAGE = prove
 (`!(f:real^3->real^3) U u.
     f continuous_on sphere(vec 0,&1) /\
     (!x y. x IN sphere(vec 0,&1) /\ y IN sphere(vec 0,&1) /\ f x = f y ==> x = y) /\
     (?O. open O /\ U = sphere(vec 0,&1) INTER O) /\ u IN U
     ==> ?r. &0 < r /\
             !z. z IN IMAGE f (sphere(vec 0,&1)) /\ z IN ball(f u,r) ==> z IN IMAGE f U`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `O:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  SUBGOAL_THEN `compact(IMAGE (f:real^3->real^3) (sphere(vec 0,&1) DIFF O))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC COMPACT_DIFF THEN ASM_REWRITE_TAC[COMPACT_SPHERE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:real^3->real^3) (sphere(vec 0,&1) DIFF O)`; `(f:real^3->real^3) u`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:real^3) IN sphere(vec 0,&1) /\ u IN O` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `x:real^3 = u` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_IMAGE; IN_BALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:real^3) IN O` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let SCH5B_S1_PART_IMAGES = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16
     ==> IMAGE (sch5b_s1 g Ri cb Theta e0) {t | t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4)} =
         IMAGE g (sch5b_odisc Ri cb) /\
         IMAGE (sch5b_s1 g Ri cb Theta e0) {t | t IN sphere(vec 0,&1) /\ t$3 <= --(&1 / &4)} =
         IMAGE g (sch5b_disc Ri cb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_PP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))));
    GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))))]) THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN CONJ_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM] THEN X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let SCH5B_S1_LOCAL_EQ = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 t.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16 /\
     t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4)
     ==> ?r. &0 < r /\
             IMAGE (sch5b_s1 g Ri cb Theta e0) (sphere(vec 0,&1)) INTER
             ball(g(sch5b_pp Ri cb t),r) =
             IMAGE g (sphere(vec 0,&1)) INTER ball(g(sch5b_pp Ri cb t),r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN `sch_neck (g:real^3->real^3) g'` ASSUME_TAC THENL
   [UNDISCH_TAC `sch5b_pancake (g:real^3->real^3) g' a lam c c' Theta Theta'` THEN
    SIMP_TAC[sch5b_pancake];
    ALL_TAC] THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`]) SCH5B_S1_PART_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_DISC_ST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_PP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^3` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sch5b_s1 g Ri cb Theta e0`;
                 `{t:real^3 | t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4)}`; `t:real^3`]
    SCH5B_LOCAL_IMAGE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC SCH5B_S1_SMOOTH THEN
        MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `a:real`; `lam:real`; `c:real^2->real^2`;
                              `c':real^2->real^2`; `Theta':real^3->real^3`; `R:real^3->real^3`;
                              `cb':real^2->real^2`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN GEN_TAC THEN
        DISCH_THEN(fun th -> REWRITE_TAC[GSYM NORM_EQ_0; th]) THEN REAL_ARITH_TAC];
      MATCH_MP_TAC SCH5B_S1_INJ THEN
      MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `a:real`; `lam:real`; `c:real^2->real^2`;
                            `c':real^2->real^2`; `Theta':real^3->real^3`; `R:real^3->real^3`;
                            `cb':real^2->real^2`] THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `{x:real^3 | x$3 < --(&1 / &4)}` THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN SET_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `sch5b_odisc Ri cb`; `sch5b_pp Ri cb t`]
    SCH5B_LOCAL_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `sch_neck (g:real^3->real^3) g'` THEN
        SIMP_TAC[sch_neck; diffeomorphism_on; SMOOTH_MAP_ON_CONTINUOUS_ON];
        REWRITE_TAC[SUBSET; SCH5_SPHERE_IN_ANNULUS]];
      UNDISCH_TAC `sch_neck (g:real^3->real^3) g'` THEN
      REWRITE_TAC[sch_neck; diffeomorphism_on] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN annulus (&1 / &2) (&2) /\ (y:real^3) IN annulus (&1 / &2) (&2)`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC SCH5B_ODISC_OPEN THEN
      MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                            `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                            `Theta':real^3->real^3`; `R:real^3->real^3`; `cb':real^2->real^2`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r1 r2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sch5b_s1 g Ri cb Theta e0 t = g(sch5b_pp Ri cb t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `(t:real^3)$3 < --(&1 / &4)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (sch5b_s1 g Ri cb Theta e0) {t | t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4)}
                SUBSET IMAGE (sch5b_s1 g Ri cb Theta e0) (sphere(vec 0,&1)) /\
                IMAGE (g:real^3->real^3) (sch5b_odisc Ri cb) SUBSET IMAGE g (sphere(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_BALL] THEN X_GEN_TAC `z:real^3` THEN
  ASM_CASES_TAC `dist((g:real^3->real^3)(sch5b_pp Ri cb t),z) < min r1 r2` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dist((g:real^3->real^3)(sch5b_pp Ri cb t),z) < r1 /\
                dist((g:real^3->real^3)(sch5b_pp Ri cb t),z) < r2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dist((g:real^3->real^3)(sch5b_pp Ri cb t),z) < min r1 r2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `z IN IMAGE (sch5b_s1 g Ri cb Theta e0)
                        {t | t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4)}` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!z:real^3. z IN IMAGE (sch5b_s1 g Ri cb Theta e0) (sphere(vec 0,&1)) /\ z IN ball(w,r)
                    ==> z IN IMAGE (sch5b_s1 g Ri cb Theta e0) U`) (concl th))) THEN
      ASM_REWRITE_TAC[IN_BALL];
      ASM SET_TAC[]];
    SUBGOAL_THEN `(z:real^3) IN IMAGE g (sch5b_odisc Ri cb)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!z:real^3. z IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\ z IN ball(w,r)
                    ==> z IN IMAGE g U`) (concl th))) THEN
      ASM_REWRITE_TAC[IN_BALL];
      ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Morse data of s1 on the cap: the height derivative along                  *)
(* the sphere is lam v3 / 2, so the north pole is the only critical point    *)
(* there; at the pole the surface is the exact paraboloid of the dome, which *)
(* gives a (-1,-1) height chart (product form of the pancake near the axis). *)
(* ------------------------------------------------------------------------- *)

let SCH5B_CAP_HEIGHT_DERIV = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 t.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16 /\
     t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3
     ==> !v. orthogonal t v
             ==> (frechet_derivative (sch5b_s1 g Ri cb Theta e0) (at t) v)$3 = lam * v$3 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN `sch5b_s1 g Ri cb Theta e0 differentiable (at t)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCH5B_S1_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `a:real`; `lam:real`; `c:real^2->real^2`;
                            `c':real^2->real^2`; `Theta':real^3->real^3`; `R:real^3->real^3`;
                            `cb':real^2->real^2`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `vec 0 IN sphere(vec 0:real^3,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `D = frechet_derivative (sch5b_s1 g Ri cb Theta e0) (at t)` THEN
  SUBGOAL_THEN `((\x. lift((sch5b_s1 g Ri cb Theta e0 x)$3)) has_derivative
                 (\w. lift(((D:real^3->real^3) w)$3))) (at t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sch5b_s1 g Ri cb Theta e0`; `\y:real^3. lift(y$3)`;
                   `D:real^3->real^3`; `\y:real^3. lift(y$3)`; `t:real^3`] DIFF_CHAIN_AT) THEN
    REWRITE_TAC[o_DEF; HAS_DERIVATIVE_LIFT_COMPONENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXPAND_TAC "D" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x:real^3. lift(a + lam * (-- &1 + x$3 / &2))) has_derivative
                 (\w. lift(lam * w$3 / &2))) (at t)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:real^3. lift(a + lam * (-- &1 + x$3 / &2))) =
                  (\x. lift(a - lam) + (lam / &2) % lift(x$3))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(\w:real^3. lift(lam * w$3 / &2)) = (\w. vec 0 + (lam / &2) % lift(w$3))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_LID; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_LIFT_COMPONENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift((sch5b_s1 g Ri cb Theta e0 x)$3)`;
                 `\x:real^3. lift(a + lam * (-- &1 + x$3 / &2))`; `t:real^3`;
                 `(t:real^3)$3 + &9 / &20`] SCH5_SPHERE_TANGENT_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `--(&9 / &20) < (t:real^3)$3` THEN REAL_ARITH_TAC;
      REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
      REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
    MP_TAC(SPEC `t:real^3` SCH5C_SPHERE_IN_CONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `x:real^3`]) SCH5B_S1_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPEC `x:real^3` SCH5C_SPHERE_IN_CONE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `sch_cap_collar e0 x IN sch5v_slab(&3 / &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SCH5C_COLLAR_IN_SLAB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `sch5b_pancake (g:real^3->real^3) g' a lam c c' Theta Theta'` THEN
    REWRITE_TAC[sch5b_pancake] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`e0:real`; `x:real^3`] SCH5C_COLLAR_SPHERE_FORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_3];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[SYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) o check
    (fun th -> can (term_match [] `((\x. lift((sch5b_s1 g Ri cb Theta e0 x)$3)) has_derivative w) (at t)`) (concl th))) THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[SYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) o check
    (fun th -> can (term_match [] `((\x:real^3. lift(a + lam * (-- &1 + x$3 / &2))) has_derivative w) (at t)`) (concl th))) THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_EQ]);;

let SCH5B_CAP_NOT_CRIT = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 (g1:real^3->real^3) t.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16 /\
     (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v
            ==> frechet_derivative g1 (at t) v =
                frechet_derivative (sch5b_s1 g Ri cb Theta e0) (at t) v) /\
     t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\ ~(t = basis 3)
     ==> ~(sch_crit g1 t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[sch_crit] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `basis 3 - (t:real^3)$3 % t`) THEN
  SUBGOAL_THEN `norm(t:real^3) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `orthogonal (t:real^3) (basis 3 - t$3 % t)` ASSUME_TAC THENL
   [REWRITE_TAC[orthogonal; DOT_RSUB; DOT_RMUL] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `norm(t:real^3) = &1` THEN REWRITE_TAC[NORM_EQ_1] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_CAP_HEIGHT_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `basis 3 - (t:real^3)$3 % t`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
    SIMP_TAC[sch5b_pancake];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3)$3 pow 2 < &1` MP_TAC THENL
   [SUBGOAL_THEN `(t:real^3)$1 pow 2 + t$2 pow 2 + t$3 pow 2 = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `norm(t:real^3) = &1` THEN REWRITE_TAC[NORM_EQ_1; DOT_3] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `x < &1 <=> ~(&1 <= x)`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(t:real^3)$1 = &0 /\ t$2 = &0 /\ t$3 = &1` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= (t:real^3)$1 pow 2 /\ &0 <= t$2 pow 2` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
      SUBGOAL_THEN `(t:real^3)$1 pow 2 = &0 /\ t$2 pow 2 = &0 /\ t$3 pow 2 = &1`
      STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_EQ_0; ARITH_EQ]) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `((t:real^3)$3 - &1) * (t$3 + &1) = &0` MP_TAC THENL
       [UNDISCH_TAC `(t:real^3)$3 pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      REWRITE_TAC[REAL_ENTIRE] THEN
      UNDISCH_TAC `--(&9 / &20) < (t:real^3)$3` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `~(t = basis 3:real^3)` THEN REWRITE_TAC[] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; BASIS_COMPONENT; ARITH] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `lam * (&1 - t * t) / &2 = &0 <=> lam * (&1 - t * t) = &0`] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_SUB_0; GSYM REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;

let SCH5B_POLE_POINT = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16
     ==> sch5b_s1 g Ri cb Theta e0 (basis 3) = Theta(vector[&0; &0; --(&1 / &2)]) /\
         Theta(vector[&0; &0; --(&1 / &2)]) =
         vector[(c(vec 0))$1; (c(vec 0))$2; a - lam / &2]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN `(basis 3:real^3) IN sphere(vec 0,&1) /\ (basis 3:real^3)$3 = &1 /\
                (basis 3:real^3)$1 = &0 /\ (basis 3:real^3)$2 = &0` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; BASIS_COMPONENT; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `basis 3:real^3`]) SCH5B_S1_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MP (CONJUNCT1 th) (REAL_ARITH `--(&9 / &20) < &1`)]) THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`e0:real`; `basis 3:real^3`] SCH5C_COLLAR_SPHERE_FORM) THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  UNDISCH_TAC `sch5b_pancake (g:real^3->real^3) g' a lam c c' Theta Theta'` THEN
  REWRITE_TAC[sch5b_pancake] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(vector[&0; &0; --(&1 / &2)]:real^3) IN sch5v_slab(&3 / &2) /\
                (vector[&0; &0; --(&1 / &2)]:real^3)$1 pow 2 +
                (vector[&0; &0; --(&1 / &2)]:real^3)$2 pow 2 < &1 / &4` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sch5v_slab; IN_ELIM_THM; VECTOR_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[sch5v_at; sch5v_pr; VECTOR_3] THEN
  SUBGOAL_THEN `vector[&0; &0]:real^2 = vec 0` SUBST1_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT]; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC);;

let SCH5B_POLE_EQUIV = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 y.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16 /\
     y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 < &1 / &16 /\
     abs(y$3 + &1 / &2) < &1 / &8
     ==> (Theta y IN IMAGE (sch5b_s1 g Ri cb Theta e0) (sphere(vec 0,&1)) <=>
          y$3 = --(&1 / &2) - (y$1 pow 2 + y$2 pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_pancake] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_pancake" with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GN") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CB") (CONJUNCTS_THEN2 (LABEL_TAC "TD")
    (CONJUNCTS_THEN2 (LABEL_TAC "HT") (CONJUNCTS_THEN2 (LABEL_TAC "PF") (LABEL_TAC "SC"))))))) THEN
  SUBGOAL_THEN `!y y':real^3. y IN sch5v_slab(&3 / &2) /\ y' IN sch5v_slab(&3 / &2) /\
                              (Theta:real^3->real^3) y = Theta y' ==> y = y'` (LABEL_TAC "TI") THENL
   [USE_THEN "TD" (MP_TAC o REWRITE_RULE[diffeomorphism_on]) THEN MESON_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (LABEL_TAC "D1")) THEN
    ASM_CASES_TAC `(t:real^3)$3 < &1 / &4` THENL
     [USE_THEN "D1" (fun th -> MP_TAC(MP th (ASSUME `(t:real^3)$3 < &1 / &4`))) THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL sch5b_bvars12 SCH5B_PP_FACTS) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real^3` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "SC" (fun th -> MP_TAC(MP (SPEC `y:real^3` th)
        (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`))) THEN
      MATCH_MP_TAC(TAUT `p /\ ~q ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `sch5b_pp Ri cb t` THEN ASM_MESON_TAC[];
        UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 < &1 / &16` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "C1" (fun th -> MP_TAC(MP th (MP (REAL_ARITH
      `~((t:real^3)$3 < &1 / &4) ==> --(&9 / &20) < t$3`) (ASSUME `~((t:real^3)$3 < &1 / &4)`)))) THEN
    DISCH_TAC THEN
    MP_TAC(SPEC `t:real^3` SCH5C_SPHERE_IN_CONE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((t:real^3)$3 < &1 / &4)` THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    SUBGOAL_THEN `y = sch_cap_collar e0 (t:real^3)` ASSUME_TAC THENL
     [USE_THEN "TI" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST [MATCH_MP_TAC SCH5C_COLLAR_IN_SLAB THEN ASM_REWRITE_TAC[] THEN NO_TAC;
             ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`e0:real`; `t:real^3`] SCH_CAP_COLLAR_SPHERE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((t:real^3)$3 < &1 / &4)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ANTS_TAC THENL [UNDISCH_TAC `~((t:real^3)$3 < &1 / &4)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhand(concl th) = `y:real^3`)) THEN
    REWRITE_TAC[sch_cap1; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(SPEC `--((y:real^3)$3)` SCH_CAP_PROFILE_TIP) THEN
    ANTS_TAC THENL [UNDISCH_TAC `abs((y:real^3)$3 + &1 / &2) < &1 / &8` THEN REAL_ARITH_TAC;
                    ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 = sch_cap_profile(--(y$3))` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 = sch_cap_profile(--(y$3)) /\
                  --(&9 / &20) < &2 * (y$3 + &1) /\ &2 * (y$3 + &1) <= &1 /\
                  --(&1 / &4) < &2 * (y$3 + &1)` STRIP_ASSUME_TAC THENL
     [MP_TAC th THEN
      MP_TAC(SPEC `--((y:real^3)$3)` SCH_CAP_PROFILE_TIP) THEN
      MP_TAC(SPECL [`(y:real^3)$1`; `(y:real^3)$2`] (REAL_ARITH
        `!a b. &0 <= a pow 2 /\ &0 <= b pow 2 ==> &0 <= a pow 2 + b pow 2`)) THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN
      MAP_EVERY UNDISCH_TAC [`(y:real^3)$1 pow 2 + y$2 pow 2 < &1 / &16`;
                             `abs((y:real^3)$3 + &1 / &2) < &1 / &8`] THEN
      REPEAT DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC]) THEN
  MP_TAC(ISPECL [`e0:real`; `y:real^3`] SCH5C_COLLAR_SINV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    STRIP_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `sch5c_sinv y` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `sch5c_sinv y`]) SCH5B_S1_SPHERE) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(sch5c_sinv y)$3 = &2 * ((y:real^3)$3 + &1)` THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `sch_cap_collar e0 (sch5c_sinv y) = y` THEN SIMP_TAC[]);;

let SCH5B_POLE_HCHART = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16
     ==> sch_hchart (IMAGE (sch5b_s1 g Ri cb Theta e0) (sphere(vec 0,&1)))
                    (Theta(vector[&0; &0; --(&1 / &2)])) (-- &1) (-- &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`]) SCH5B_POLE_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_pancake] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_pancake" with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GN") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CB") (CONJUNCTS_THEN2 (LABEL_TAC "TD")
    (CONJUNCTS_THEN2 (LABEL_TAC "HT") (CONJUNCTS_THEN2 (LABEL_TAC "PF") (LABEL_TAC "SC"))))))) THEN
  ABBREV_TAC `q = sqrt lam` THEN
  SUBGOAL_THEN `&0 < q /\ q pow 2 = lam /\ ~(q = &0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE; ASSUME `&0 < lam`] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN SIMP_TAC[SQRT_POS_LT; ASSUME `&0 < lam`];
    ALL_TAC] THEN
  ABBREV_TAC `r = min (&1 / &2) (min (lam / &8) (q / &4))` THEN
  SUBGOAL_THEN `&0 < r /\ r < &1 /\ r <= lam / &8 /\ r <= q / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[sch_hchart] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `(c:real^2->real^2) o (\u. inv q % u)`;
                        `(\w:real^2. q % w) o (c':real^2->real^2)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `diffeomorphism_on (ball(vec 0,r)) (ball(vec 0,r / q))
                  (\u:real^2. inv q % u) (\w. q % w)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL_0; NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < q ==> abs q = q`] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID];
      X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
      ASM_SIMP_TAC[REAL_FIELD `~(q = &0) ==> (inv q * n) * q = n`];
      X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
      UNDISCH_TAC `norm(w:real^2) < r / q` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (ball(vec 0,r / q)) (IMAGE (c:real^2->real^2) (ball(vec 0,r / q)))
                  c c'` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^2,&2)`; `IMAGE (c:real^2->real^2) (ball(vec 0,&2))`] THEN
    REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [USE_THEN "CB" (fun th -> REWRITE_TAC[REWRITE_RULE[sch_ball] th]); ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN GEN_TAC THEN
    SUBGOAL_THEN `r / q <= &1 / &4` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,r)`; `ball(vec 0:real^2,r / q)`;
                 `IMAGE (c:real^2->real^2) (ball(vec 0,r / q))`; `\u:real^2. inv q % u`;
                 `\w:real^2. q % w`; `c:real^2->real^2`; `c':real^2->real^2`]
    DIFFEOMORPHISM_ON_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE ((c:real^2->real^2) o (\u. inv q % u)) (ball(vec 0,r)) =
                IMAGE c (ball(vec 0,r / q))` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[diffeomorphism_on] o check (fun th ->
      can (term_match [] `diffeomorphism_on (ball(vec 0:real^2,r)) t ((c:real^2->real^2) o f) h`)
        (concl th))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[o_THM; VECTOR_MUL_RZERO] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_3];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real`] THEN
  REWRITE_TAC[IN_BALL_0; VECTOR_3; o_THM] THEN STRIP_TAC THEN
  ABBREV_TAC `w = inv q % (u:real^2)` THEN
  ABBREV_TAC `rho = (w:real^2)$1 pow 2 + w$2 pow 2` THEN
  SUBGOAL_THEN `(u:real^2)$1 pow 2 + u$2 pow 2 < lam / &16` ASSUME_TAC THENL
   [SUBGOAL_THEN `(u:real^2)$1 pow 2 + u$2 pow 2 = norm u pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_POW_2; DOT_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(q / &4) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[NORM_POS_LE; ARITH_EQ] THEN
      MAP_EVERY UNDISCH_TAC [`norm(u:real^2) < r`; `r <= q / &4`] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_POW_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho * lam = (u:real^2)$1 pow 2 + u$2 pow 2 /\ rho < &1 / &16` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `rho = ((u:real^2)$1 pow 2 + u$2 pow 2) / lam` SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["rho"; "w"] THEN
      REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_POW_MUL; REAL_POW_INV] THEN
      ASM_REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      UNDISCH_TAC `(u:real^2)$1 pow 2 + u$2 pow 2 < lam / &16` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `y = vector[(w:real^2)$1; w$2; (z - a) / lam]:real^3` THEN
  SUBGOAL_THEN `abs((y:real^3)$3 + &1 / &2) < &1 / &8 /\ (y:real^3)$1 pow 2 + y$2 pow 2 = rho`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN ASM_REWRITE_TAC[VECTOR_3] THEN
    SUBGOAL_THEN `(z - a) / lam + &1 / &2 = (z - (a - lam / &2)) / lam` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < lam ==> abs lam = lam`; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 < &1 / &4`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `vector[((c:real^2->real^2) w)$1; (c w)$2; z]:real^3 = (Theta:real^3->real^3) y`
  SUBST1_TAC THENL
   [USE_THEN "PF" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
      (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 < &1 / &4`))]) THEN
    EXPAND_TAC "y" THEN REWRITE_TAC[sch5v_at; sch5v_pr; VECTOR_3] THEN
    SUBGOAL_THEN `vector[(w:real^2)$1; w$2]:real^2 = w` SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]; ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `y:real^3`]) SCH5B_POLE_EQUIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  EXPAND_TAC "y" THEN REWRITE_TAC[VECTOR_3] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `--(&1) * x + --(&1) * y = --(x + y)`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `(u:real^2)$1 pow 2 + u$2 pow 2`)) THEN
  ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Morse data of the surgered neck g1 (any neck with the                     *)
(* values and tangential derivatives of s1 on the sphere): critical points   *)
(* are the north pole and the transported critical points of g in the disc; *)
(* height charts transfer; saddles correspond to the saddles of g in D.      *)
(* ------------------------------------------------------------------------- *)

let sch5b_g1 = new_definition
 `sch5b_g1 (g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'
           (R:real^3->real^3) Ri (cb:real^2->real^2) cb' e0 (g1:real^3->real^3) g1' <=>
    sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16 /\
    sch_neck g1 g1' /\
    (!t. t IN sphere(vec 0,&1) ==> g1 t = sch5b_s1 g Ri cb Theta e0 t) /\
    (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v
           ==> frechet_derivative g1 (at t) v =
               frechet_derivative (sch5b_s1 g Ri cb Theta e0) (at t) v)`;;

let sch5b_gvars = sch5b_bvars12 @ [`e0:real`; `g1:real^3->real^3`; `g1':real^3->real^3`];;

let SCH5B_G1_IMAGE_EQ = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 (g1:real^3->real^3) g1'.
     sch5b_g1 g g' a lam c c' Theta Theta' R Ri cb cb' e0 g1 g1'
     ==> IMAGE g1 (sphere(vec 0,&1)) = IMAGE (sch5b_s1 g Ri cb Theta e0) (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5b_g1] THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  ASM_REWRITE_TAC[]);;

let SCH5B_G1_SOUTH = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 (g1:real^3->real^3) g1' t.
     sch5b_g1 g g' a lam c c' Theta Theta' R Ri cb cb' e0 g1 g1' /\
     t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4)
     ==> g1 t = g(sch5b_pp Ri cb t) /\ sch5b_pp Ri cb t IN sphere(vec 0,&1) /\
         sch5b_pp Ri cb t IN sch5b_odisc Ri cb /\
         (sch_crit g1 t <=> sch_crit g (sch5b_pp Ri cb t)) /\
         (!k1 k2. sch_hchart (IMAGE g1 (sphere(vec 0,&1))) (g1 t) k1 k2 <=>
                  sch_hchart (IMAGE g (sphere(vec 0,&1))) (g(sch5b_pp Ri cb t)) k1 k2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (ISPECL sch5b_gvars SCH5B_G1_IMAGE_EQ) th]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch5b_g1] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_g1" with Failure _ -> false)) THEN
  SUBGOAL_THEN `sch_neck (g:real^3->real^3) g'` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot] o check sch5b_is_bot) THEN
    SIMP_TAC[sch5b_pancake];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g1:real^3->real^3) t = g(sch5b_pp Ri cb t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    UNDISCH_TAC `(t:real^3)$3 < --(&1 / &4)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_PP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `t:real^3`) (MP_TAC o SPEC `t:real^3` o
    CONJUNCT1 o CONJUNCT2)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(t:real^3)$3 < --(&1 / &4)` THEN
                  REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_LOCAL_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SCH5_CRIT_LOCAL_BALL THEN
    MAP_EVERY EXISTS_TAC [`g1':real^3->real^3`; `g':real^3->real^3`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (ISPECL sch5b_gvars SCH5B_G1_IMAGE_EQ) th]) THEN
    FIRST_X_ASSUM ACCEPT_TAC;
    REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SCH5_HCHART_LOCAL THENL
     [EXISTS_TAC `IMAGE (sch5b_s1 g Ri cb Theta e0) (sphere(vec 0,&1))`;
      EXISTS_TAC `IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`] THEN
    EXISTS_TAC `r:real` THEN ASM_MESON_TAC[]]);;

let SCH5B_G1_POLE = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 (g1:real^3->real^3) g1'.
     sch5b_g1 g g' a lam c c' Theta Theta' R Ri cb cb' e0 g1 g1'
     ==> g1(basis 3) = vector[(c(vec 0))$1; (c(vec 0))$2; a - lam / &2] /\
         sch_hchart (IMAGE g1 (sphere(vec 0,&1))) (g1(basis 3)) (-- &1) (-- &1) /\
         ~(basis 3 IN sch_saddles g1) /\
         (!t. sch_crit g1 t
              ==> t = basis 3 \/
                  (t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4) /\
                   sch_crit g (sch5b_pp Ri cb t)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (ISPECL sch5b_gvars SCH5B_G1_IMAGE_EQ) th]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch5b_g1]) THEN
  SUBGOAL_THEN `(basis 3:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`]) SCH5B_POLE_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g1:real^3->real^3)(basis 3) = (Theta:real^3->real^3)(vector[&0; &0; --(&1 / &2)])`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sch_hchart (IMAGE (sch5b_s1 g Ri cb Theta e0) (sphere(vec 0,&1)))
                  ((g1:real^3->real^3)(basis 3)) (-- &1) (-- &1)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhand(concl th) = `(g1:real^3->real^3)(basis 3)` &&
      rand(concl th) = `(Theta:real^3->real^3)(vector[&0; &0; --(&1 / &2)])`)) THEN
    MATCH_MP_TAC SCH5B_POLE_HCHART THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `a:real`; `lam:real`; `c:real^2->real^2`;
                          `c':real^2->real^2`; `Theta':real^3->real^3`; `R:real^3->real^3`;
                          `cb':real^2->real^2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[sch_saddles; IN_ELIM_THM] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (ISPECL sch5b_gvars SCH5B_G1_IMAGE_EQ) th]) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (sch5b_s1 g Ri cb Theta e0) (sphere(vec 0,&1))`;
                   `(g1:real^3->real^3)(basis 3)`; `-- &1`] SCH5_MAX_NOT_SADDLE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sch_crit]; ALL_TAC] THEN
  ASM_CASES_TAC `(t:real^3)$3 < --(&1 / &4)` THENL
   [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (sch5b_gvars @ [`t:real^3`]) SCH5B_G1_SOUTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t = basis 3:real^3` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `g1:real^3->real^3`; `t:real^3`]) SCH5B_CAP_NOT_CRIT) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((t:real^3)$3 < --(&1 / &4))` THEN REAL_ARITH_TAC);;

let SCH5B_G1_MORSE = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 (g1:real^3->real^3) g1'.
     sch5b_g1 g g' a lam c c' Theta Theta' R Ri cb cb' e0 g1 g1' /\ sch_morse g /\
     (!t. sch_crit g t ==> ~((g t)$3 = a - lam / &2))
     ==> sch_morse g1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_gvars SCH5B_G1_POLE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "CC")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch_morse] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch_morse" with Failure _ -> false)) THEN
  SUBGOAL_THEN `(basis 3:real^3) IN sphere(vec 0,&1) /\ ~((basis 3:real^3)$3 < --(&1 / &4))`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch5b_g1] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_g1" with Failure _ -> false)) THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_PP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "PD" o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[sch_morse] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `basis 3 INSERT {t | t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4) /\
                                   sch_crit g (sch5b_pp Ri cb t)}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FINITE_INSERT] THEN
      MP_TAC(ISPECL [`sch5b_pp Ri cb`;
                     `{t | t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4) /\
                           sch_crit g (sch5b_pp Ri cb t)}`] FINITE_IMAGE_INJ_EQ) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN USE_THEN "PD" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t | sch_crit (g:real^3->real^3) t}` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT] THEN X_GEN_TAC `t:real^3` THEN
      DISCH_THEN(fun th -> USE_THEN "CC" (MP_TAC o C MATCH_MP th)) THEN MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real^3`; `t':real^3`] THEN STRIP_TAC THEN
    USE_THEN "CC" (fun th -> MP_TAC(MATCH_MP th (ASSUME `sch_crit (g1:real^3->real^3) t`))) THEN
    USE_THEN "CC" (fun th -> MP_TAC(MATCH_MP th (ASSUME `sch_crit (g1:real^3->real^3) t'`))) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) THEN REWRITE_TAC[] THENL
     [MP_TAC(ISPECL (sch5b_gvars @ [`t:real^3`]) SCH5B_G1_SOUTH) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `sch5b_pp Ri cb t` o check (fun th -> can (term_match []
        `!t:real^3. sch_crit g t ==> ~((g t)$3 = a - lam / &2)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `((g1:real^3->real^3) t)$3 = (g1(basis 3))$3` THEN
      ASM_REWRITE_TAC[VECTOR_3] THEN MESON_TAC[];
      MP_TAC(ISPECL (sch5b_gvars @ [`t':real^3`]) SCH5B_G1_SOUTH) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `sch5b_pp Ri cb t'` o check (fun th -> can (term_match []
        `!t:real^3. sch_crit g t ==> ~((g t)$3 = a - lam / &2)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `((g1:real^3->real^3) (basis 3))$3 = (g1 t')$3` THEN
      ASM_REWRITE_TAC[VECTOR_3] THEN MESON_TAC[];
      MP_TAC(ISPECL (sch5b_gvars @ [`t:real^3`]) SCH5B_G1_SOUTH) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL (sch5b_gvars @ [`t':real^3`]) SCH5B_G1_SOUTH) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      USE_THEN "PD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t t':real^3. sch_crit g t /\ sch_crit g t' /\ (g t)$3 = (g t')$3 ==> t = t'`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "CC" (fun th -> MP_TAC(MATCH_MP th (ASSUME `sch_crit (g1:real^3->real^3) t`))) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) THENL
     [MAP_EVERY EXISTS_TAC [`-- &1`; `-- &1`] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL (sch5b_gvars @ [`t:real^3`]) SCH5B_G1_SOUTH) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t:real^3. sch_crit g t ==> ?k1 k2. sch_hchart s (g t) k1 k2`) (concl th))) THEN
      ASM_REWRITE_TAC[]]]);;

let SCH5B_G1_HEIGHTS = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 (g1:real^3->real^3) g1'.
     sch5b_g1 g g' a lam c c' Theta Theta' R Ri cb cb' e0 g1 g1' /\
     (!t. sch_crit g t ==> ~((g t)$3 = a))
     ==> !t. sch_crit g1 t ==> ~((g1 t)$3 = a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL sch5b_gvars SCH5B_G1_POLE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `t:real^3` o last o CONJUNCTS)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THENL
   [ASM_REWRITE_TAC[VECTOR_3] THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_g1; sch5b_bot; sch5b_pancake] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_g1" with Failure _ -> false)) THEN
    STRIP_TAC THEN UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL (sch5b_gvars @ [`t:real^3`]) SCH5B_G1_SOUTH) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t:real^3. sch_crit g t ==> ~((g t)$3 = a)`) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

let SCH5B_G1_SADDLES = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 (g1:real^3->real^3) g1'.
     sch5b_g1 g g' a lam c c' Theta Theta' R Ri cb cb' e0 g1 g1' /\ sch_morse g /\
     (!t. sch_crit g t ==> ~((g t)$3 = a - lam / &2))
     ==> IMAGE (sch5b_pp Ri cb) (sch_saddles g1) = sch_saddles g INTER sch5b_odisc Ri cb /\
         (!t. t IN sch_saddles g1 ==> g1 t = g(sch5b_pp Ri cb t)) /\
         CARD(sch_saddles g1) = CARD(sch_saddles g INTER sch5b_odisc Ri cb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_gvars SCH5B_G1_POLE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CC")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch5b_g1] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_g1" with Failure _ -> false)) THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_PP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "PD")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "PIM")))))) THEN
  SUBGOAL_THEN `!t. t IN sch_saddles g1 <=>
                    t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4) /\
                    sch5b_pp Ri cb t IN sch_saddles g` (LABEL_TAC "SD") THENL
   [X_GEN_TAC `t:real^3` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `sch_crit (g1:real^3->real^3) t /\
                    sch_hchart (IMAGE g1 (sphere(vec 0,&1))) (g1 t) (&1) (-- &1)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[sch_saddles; IN_ELIM_THM]; ALL_TAC] THEN
      USE_THEN "CC" (fun th -> MP_TAC(MATCH_MP th (ASSUME `sch_crit (g1:real^3->real^3) t`))) THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL (sch5b_gvars @ [`t:real^3`]) SCH5B_G1_SOUTH) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN REWRITE_TAC[sch_saddles; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      STRIP_TAC THEN
      MP_TAC(ISPECL (sch5b_gvars @ [`t:real^3`]) SCH5B_G1_SOUTH) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      UNDISCH_TAC `sch5b_pp Ri cb t IN sch_saddles g` THEN
      REWRITE_TAC[sch_saddles; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN sch_saddles g1 ==> g1 t = g(sch5b_pp Ri cb t)` ASSUME_TAC THENL
   [X_GEN_TAC `t:real^3` THEN USE_THEN "SD" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    MP_TAC(ISPECL (sch5b_gvars @ [`t:real^3`]) SCH5B_G1_SOUTH) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (sch5b_pp Ri cb) (sch_saddles g1) = sch_saddles g INTER sch5b_odisc Ri cb`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:real^3` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(t:real^3) IN sch_saddles g1` THEN USE_THEN "SD" (fun th -> REWRITE_TAC[th]) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL (sch5b_gvars @ [`t:real^3`]) SCH5B_G1_SOUTH) THEN ASM_SIMP_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `(u:real^3) IN IMAGE (sch5b_pp Ri cb)
                     {t | t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4)}` MP_TAC THENL
       [USE_THEN "PIM" SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:real^3` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "SD" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhand(concl th) = `IMAGE (sch5b_pp Ri cb) (sch_saddles (g1:real^3->real^3))`)) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real^3`; `t':real^3`] THEN
    USE_THEN "SD" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    USE_THEN "PD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t | sch_crit (g1:real^3->real^3) t}` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL (sch5b_gvars) SCH5B_G1_MORSE) THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[sch_morse];
      REWRITE_TAC[sch_saddles; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]]]);;

let SCH5B_G1_LEVEL = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 (g1:real^3->real^3) g1'.
     sch5b_g1 g g' a lam c c' Theta Theta' R Ri cb cb' e0 g1 g1'
     ==> sch_level g1 a = {x | x IN IMAGE g (sch5b_odisc Ri cb) /\ x$3 = a}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[sch_level] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (ISPECL sch5b_gvars SCH5B_G1_IMAGE_EQ) th]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch5b_g1]) THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`]) SCH5B_S1_PART_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM o CONJUNCT1) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    UNDISCH_TAC `(x:real^3) IN IMAGE g (sch5b_odisc Ri cb)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> (x:real^3) IN IMAGE (f:real^3->real^3) s ==> x IN IMAGE f t`) THEN SET_TAC[]] THEN
  UNDISCH_TAC `(x:real^3) IN IMAGE (sch5b_s1 g Ri cb Theta e0) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(t:real^3)$3 < --(&1 / &4)` THENL
   [EXISTS_TAC `t:real^3` THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~((t:real^3)$3 < --(&1 / &4))` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `t:real^3` SCH5C_SPHERE_IN_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((t:real^3)$3 < --(&1 / &4))` THEN
                  REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `sch_cap_collar e0 t IN sch5v_slab(&3 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5C_COLLAR_IN_SLAB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(sch_cap_collar e0 (t:real^3))$3 = -- &1 + t$3 / &2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e0:real`; `t:real^3`] SCH5C_COLLAR_SPHERE_FORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((t:real^3)$3 < --(&1 / &4))` THEN
                    REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[VECTOR_3];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_bot; sch5b_pancake] o check sch5b_is_bot) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `((Theta:real^3->real^3)(sch_cap_collar e0 t))$3 = a + lam * (-- &1 + t$3 / &2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3)$3 <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lam * (-- &1 + (t:real^3)$3 / &2) <= lam * --(&1 / &2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(t:real^3)$3 <= &1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3)$3 = a + lam * (-- &1 + (t:real^3)$3 / &2)` MP_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `x:real^3`)) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhand(concl th) = `sch5b_s1 g Ri cb Theta e0 t`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`(x:real^3)$3 = a`; `&0 < lam`;
                         `lam * (-- &1 + (t:real^3)$3 / &2) <= lam * --(&1 / &2)`] THEN
  REAL_ARITH_TAC);;

let SCH5B_S1_IMAGE = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0.
     sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16
     ==> IMAGE (sch5b_s1 g Ri cb Theta e0) (sphere(vec 0,&1)) =
         (IMAGE g (sch5b_disc Ri cb) UNION IMAGE Theta (sch5b_band (--(&9 / &8)) (-- &1)))
         UNION IMAGE Theta sch_cap1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`]) SCH5B_S1_PART_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!t. t IN sphere(vec 0,&1) /\ --(&1 / &4) < t$3
        ==> sch5b_s1 g Ri cb Theta e0 t = (Theta:real^3->real^3)(sch_cap_collar e0 t)`
  (LABEL_TAC "CAPF") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `t:real^3`]) SCH5B_S1_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `--(&1 / &4) < (t:real^3)$3` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  ASM_REWRITE_TAC[IN_UNION] THEN EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(t:real^3)$3 <= --(&1 / &4)` THENL
     [DISJ1_TAC THEN DISJ1_TAC THEN EXISTS_TAC `t:real^3` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "CAPF" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(t:real^3) IN sphere(vec 0,&1)`)
      (MP (REAL_ARITH `~((t:real^3)$3 <= --(&1 / &4)) ==> --(&1 / &4) < t$3`)
          (ASSUME `~((t:real^3)$3 <= --(&1 / &4))`))))) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`e0:real`; `t:real^3`] SCH_CAP_COLLAR_SPHERE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
      UNDISCH_TAC `~((t:real^3)$3 <= --(&1 / &4))` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `&0 <= (t:real^3)$3` THENL
     [ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `sch_cap_collar e0 t` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(t:real^3)$3 < &0` ASSUME_TAC THENL
       [UNDISCH_TAC `~(&0 <= (t:real^3)$3)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISJ1_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `sch_cap_collar e0 t` THEN ASM_REWRITE_TAC[sch5b_band; IN_ELIM_THM]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [POP_ASSUM MP_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> (x:real^3) IN IMAGE (f:real^3->real^3) s ==> x IN IMAGE f t`) THEN SET_TAC[];
    ALL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
  (SUBGOAL_THEN `--(&9 / &20) < &2 * ((y:real^3)$3 + &1) /\ &2 * (y$3 + &1) <= &1 /\
                 y$1 pow 2 + y$2 pow 2 = sch_cap_profile(--(y$3))` STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `(y:real^3) IN s`) (concl th))) THEN
     REWRITE_TAC[sch5b_band; sch_cap1; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     TRY(MATCH_MP_TAC(TAUT `(p /\ q) /\ r ==> p /\ q /\ r`) THEN CONJ_TAC THENL
          [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
         CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC) THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
   MP_TAC(ISPECL [`e0:real`; `y:real^3`] SCH5C_COLLAR_SINV) THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
   EXISTS_TAC `sch5c_sinv y` THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
   MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`; `sch5c_sinv y`]) SCH5B_S1_SPHERE) THEN
   ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o CONJUNCT1) THEN
   ANTS_TAC THENL
    [UNDISCH_TAC `(sch5c_sinv y)$3 = &2 * ((y:real^3)$3 + &1)` THEN
     DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
     DISCH_THEN SUBST1_TAC] THEN
   UNDISCH_TAC `sch_cap_collar e0 (sch5c_sinv y) = y` THEN DISCH_THEN SUBST1_TAC THEN
   FIRST_ASSUM ACCEPT_TAC));;

(* ------------------------------------------------------------------------- *)
(* The bottom surgery theorem.  From a pancake chart Theta at                *)
(* a regular level a of a Morse collared sphere g (a - lam/2 not a critical  *)
(* value) we get a Morse neck g1 equal to the model collar near the cap,     *)
(* a closed disc D of the parameter sphere bounded by the band circle at     *)
(* height -9/8 (interior D0), with g1(S^2) = g(D) + lower band + cap1, the   *)
(* saddles of g1 = the saddles of g in D0, and the level a of g1 = g(D0) at  *)
(* height a, and the critical points of g1 in image form.                    *)
(* ------------------------------------------------------------------------- *)

(* Critical points of g1 in image form: the pole basis 3 (image the apex of  *)
(* the model cap) and the transported critical points of g in D0.           *)

let SCH5B_G1_CRITS = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' R Ri
    (cb:real^2->real^2) cb' e0 (g1:real^3->real^3) g1'.
     sch5b_g1 g g' a lam c c' Theta Theta' R Ri cb cb' e0 g1 g1' /\ sch_morse g /\
     (!t. sch_crit g t ==> ~((g t)$3 = a - lam / &2))
     ==> IMAGE g1 (sch_saddles g1) = IMAGE g (sch_saddles g INTER sch5b_odisc Ri cb) /\
         (!t. sch_crit g1 t
              ==> t = basis 3 /\ g1 t = Theta(vector[&0; &0; --(&1 / &2)]) \/
                  (?u. u IN sch5b_odisc Ri cb /\ sch_crit g u /\ g1 t = g u)) /\
         (!u. u IN sch5b_odisc Ri cb /\ sch_crit g u ==> ?t. sch_crit g1 t /\ g1 t = g u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch5b_bot g g' a lam c c' Theta Theta' R Ri cb cb' /\ &0 < e0 /\ e0 <= &1 / &16`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sch5b_g1 g g' a lam c c' Theta Theta' R Ri cb cb' e0 g1 g1'` THEN
    REWRITE_TAC[sch5b_g1] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL sch5b_gvars SCH5B_G1_SADDLES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PPS") (CONJUNCTS_THEN2 (LABEL_TAC "G1S") (K ALL_TAC))) THEN
  MP_TAC(ISPECL sch5b_gvars SCH5B_G1_POLE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PV") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "POLE")))) THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`e0:real`]) SCH5B_POLE_POINT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "PP" o CONJUNCT2) THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_PP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "PIM" o last o CONJUNCTS) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "PPS" (SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> (f:real^3->real^3) x = (h:real^3->real^3) x) ==> IMAGE f s = IMAGE h s`) THEN
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    USE_THEN "G1S" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "POLE" (fun th -> MP_TAC(MATCH_MP th (ASSUME `sch_crit (g1:real^3->real^3) t`))) THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "PV" SUBST1_TAC THEN USE_THEN "PP" (SUBST1_TAC o SYM) THEN REFL_TAC;
      DISJ2_TAC THEN EXISTS_TAC `sch5b_pp Ri cb t` THEN
      MP_TAC(ISPECL (sch5b_gvars @ [`t:real^3`]) SCH5B_G1_SOUTH) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(u:real^3) IN IMAGE (sch5b_pp Ri cb)
                    {t:real^3 | t IN sphere(vec 0,&1) /\ t$3 < --(&1 / &4)}` MP_TAC THENL
     [USE_THEN "PIM" SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `t:real^3` THEN
    MP_TAC(ISPECL (sch5b_gvars @ [`t:real^3`]) SCH5B_G1_SOUTH) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let SCH5B_BOTTOM = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch5b_pancake g g' a lam c c' Theta Theta' /\ sch_morse g /\
     (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     (!t. sch_crit g t ==> ~((g t)$3 = a - lam / &2))
     ==> ?g1 g1' e1 D D0.
           sch_neck g1 g1' /\ sch_morse g1 /\ (!t. sch_crit g1 t ==> ~((g1 t)$3 = a)) /\
           &0 < e1 /\ e1 <= &1 / &16 /\
           (!x. x IN sch_capcone ==> g1 x = Theta(sch_cap_collar e1 x)) /\
           D SUBSET sphere(vec 0,&1) /\ D0 SUBSET D /\
           (?U. open U /\ D0 = sphere(vec 0,&1) INTER U) /\ compact D /\ connected D /\
           (!y. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1 /\ y$3 < &4 / &3
                ==> (g'(Theta y) IN D <=> y$3 <= --(&9 / &8)) /\
                    (g'(Theta y) IN D0 <=> y$3 < --(&9 / &8))) /\
           (!x. x IN D /\ ~(x IN D0) ==> ?y. y IN sch5b_circ(--(&9 / &8)) /\ x = g'(Theta y)) /\
           IMAGE g1 (sphere(vec 0,&1)) =
           (IMAGE g D UNION IMAGE Theta (sch5b_band (--(&9 / &8)) (-- &1))) UNION
           IMAGE Theta sch_cap1 /\
           CARD(sch_saddles g1) = CARD(sch_saddles g INTER D0) /\
           (!u. u IN sch_saddles g INTER D0 ==> ?t. t IN sch_saddles g1 /\ g1 t = g u) /\
           sch_level g1 a = {x | x IN IMAGE g D0 /\ x$3 = a} /\
           IMAGE g1 (sch_saddles g1) = IMAGE g (sch_saddles g INTER D0) /\
           (!t. sch_crit g1 t
                ==> t = basis 3 /\ g1 t = Theta(vector[&0; &0; --(&1 / &2)]) \/
                    (?u. u IN D0 /\ sch_crit g u /\ g1 t = g u)) /\
           (!u. u IN D0 /\ sch_crit g u ==> ?t. sch_crit g1 t /\ g1 t = g u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5B_BOT_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` (X_CHOOSE_THEN `Ri:real^3->real^3`
    (X_CHOOSE_THEN `cb:real^2->real^2` (X_CHOOSE_THEN `cb':real^2->real^2` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`&1 / &16`]) SCH5B_BOTTOM_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `sch5b_g1 g g' a lam c c' Theta Theta' R Ri cb cb' (&1 / &16) g1 g1'`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[sch5b_g1] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`g1:real^3->real^3`; `g1':real^3->real^3`; `e1:real`;
                        `sch5b_disc Ri cb`; `sch5b_odisc Ri cb`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`&1 / &16`; `g1:real^3->real^3`; `g1':real^3->real^3`])
    SCH5B_G1_MORSE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`&1 / &16`; `g1:real^3->real^3`; `g1':real^3->real^3`])
    SCH5B_G1_HEIGHTS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`&1 / &16`; `g1:real^3->real^3`; `g1':real^3->real^3`])
    SCH5B_G1_SADDLES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`&1 / &16`; `g1:real^3->real^3`; `g1':real^3->real^3`])
    SCH5B_G1_LEVEL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`&1 / &16`; `g1:real^3->real^3`; `g1':real^3->real^3`])
    SCH5B_G1_IMAGE_EQ) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`&1 / &16`]) SCH5B_S1_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_DISC_ST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_DISC_COMPACT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_ODISC_OPEN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_DISC_BAND) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL sch5b_bvars12 SCH5B_DISC_BOUNDARY) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars12 @ [`&1 / &16`; `g1:real^3->real^3`; `g1':real^3->real^3`])
    SCH5B_G1_CRITS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(u:real^3) IN IMAGE (sch5b_pp Ri cb) (sch_saddles g1)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^3` THEN ASM_SIMP_TAC[]);;

