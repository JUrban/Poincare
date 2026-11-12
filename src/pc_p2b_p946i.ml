(* ========================================================================= *)
(* Unit pc_p2b_p946i: spheres in far level sets of the soliton potential of  *)
(* MT Prop 9.46, inside eps-necks, with intrinsic curvature close to 1,      *)
(* whose area is then at most about 8 pi by the reverse Gauss-Bonnet         *)
(* inequality.                                                               *)
(* ========================================================================= *)

needs "src/pc_p2b_p946h.ml";;
needs "src/pc_p2a_cylm.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The reverse Gauss-Bonnet inequality.  The planar form of                  *)
(* CML_GB_INEQ (pc_cm_lemma122) with the inequality reversed, and the       *)
(* sphere form of GBS2_GB_SPHERE_AREA (pc_cm_gbs2) with a lower curvature   *)
(* bound: R >= 2 k1 on a Riemannian 2-sphere of area a gives k1 a <= 4 pi.  *)
(* ========================================================================= *)

let P2BX46_GB_INEQ_REV = prove
 (`!(mu:real^2->real) mu' Gf.
     smooth_map_on (:real^2) (\z. lift(mu z)) /\ (!z. &0 < mu z) /\
     smooth_map_on (:real^2) (\z. lift(mu' z)) /\ (!z. &0 < mu' z) /\
     (!z. ~(z = vec 0) ==> mu z = mu'(cml_inv z) / norm z pow 4) /\
     (\z. lift(Gf z)) absolutely_integrable_on (:real^2) /\
     (!z. Gf z <= --(cml_lap (\x. log(mu x)) z) / &2)
     ==> drop(integral (:real^2) (\z. lift(Gf z))) <= &4 * pi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\z. lift(log((mu:real^2->real) z))) /\
                smooth_map_on (:real^2) (\z. lift(log((mu':real^2->real) z)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CML_SM_LOG THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. log((mu:real^2->real) x)`; `\x. log((mu':real^2->real) x)`]
                CML_FLUX_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_LOG_REL THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `C:real`)] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_BALL_LIMIT) THEN
  SUBGOAL_THEN
   `!n. 1 <= n
        ==> drop(integral (ball(vec 0,&n)) (\z. lift((Gf:real^2->real) z))) <=
            &4 * pi + C / (&2 * &n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. log((mu:real^2->real) x)`; `&n`] CML_GREEN_DISC) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&n`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\z. lift(--(cml_lap (\x. log((mu:real^2->real) x)) z) / &2)) =
      (\z. --(inv(&2)) % lift(cml_lap (\x. log(mu x)) z))`
    ASSUME_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL] THEN GEN_TAC THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (ball(vec 0,&n))
                       (\z. lift(--(cml_lap (\x. log((mu:real^2->real) x)) z) / &2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
      SUBGOAL_THEN `C / (&2 * &n) = (C / &n) / &2` SUBST1_TAC THENL
       [SUBGOAL_THEN `&0 < &n` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
        ALL_TAC] THEN
      UNDISCH_TAC `abs (cml_flux (\x. log ((mu:real^2->real) x)) (&n) + &8 * pi) <= C / &n` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `Iv = drop(integral (:real^2) (\z. lift((Gf:real^2->real) z)))` THEN
  ABBREV_TAC `e = (Iv - &4 * pi) / &2` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\n. integral (ball(vec 0,&n)) (\z. lift((Gf:real^2->real) z))`;
                 `integral (:real^2) (\z. lift((Gf:real^2->real) z))`; `&4 * pi + e`]
                LIM_DROP_UBOUND) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  MATCH_MP_TAC(TAUT `p /\ ~q ==> ~(p ==> q)`) THEN CONJ_TAC THENL
   [ALL_TAC; EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC] THEN
  MP_TAC(SPEC `abs C / (&2 * e) + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &n /\ abs C / (&2 * e) + &1 <= &n` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= abs C / (&2 * e)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs C / (&2 * e) + &1 <= &N` THEN UNDISCH_TAC `N:num <= n` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= e ==> x <= p + b ==> x <= p + e`) THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN
  MATCH_MP_TAC(REAL_ARITH `abs c <= x ==> c <= x`) THEN
  SUBGOAL_THEN `(&2 * e) * (abs C / (&2 * e)) = abs C` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * e` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * e) * (abs C / (&2 * e)) <= (&2 * e) * &n` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The sphere form (copy of GBS2_GB_SPHERE_AREA with the bound reversed). *)

let P2BX46_GB_SPHERE_AREA_REV = prove
 (`!top atlas (g:A->real^2^2) S (psi:real^3->A) (psi':A->real^3) k1 a.
       hausdorff_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^2))->bool) /\
       riemannian_metric atlas g /\
       mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                  (sphere(vec 0:real^3,&1)) top atlas S psi psi' /\
       (!x. x IN S ==> &2 * k1 <= mfd_scalar atlas g x) /\
       mfd_has_volume (top,atlas) g S a
       ==> k1 * a <= &4 * pi`,
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                       `g:A->real^2^2`; `S:A->bool`; `psi:real^3->A`; `psi':A->real^3`;
                       `k1:real`; `a:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `S:A->bool`; `psi:real^3->A`; `psi':A->real^3`] GBS2_EMBED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^5` (X_CHOOSE_THEN `Q:real^5->real^5^5`
    (X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!U phi. (U,phi) IN (atlas:((A->bool)#(A->real^2))->bool)
                        ==> ?hc. smooth_map_on (IMAGE phi (U INTER S)) hc /\
                                 (!x. x IN U INTER S ==> hc(phi x) = (f:A->real^5) x)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> MESON_TAC[check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "frechet_derivative"
                               with Failure _ -> false)) (concl th) &&
      not(can (find_term (fun t -> try fst(dest_const t) = "metric_local"
                                   with Failure _ -> false)) (concl th))) th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `S:A->bool`;
                 `psi:real^3->A`; `psi':A->real^3`; `f:A->real^5`] GBS2_FPSI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `S:A->bool`;
                 `psi:real^3->A`; `psi':A->real^3`; `f:A->real^5`] GBS2_FE_TANGENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* homogeneity of the radial extension *)
  SUBGOAL_THEN `!t z. &0 < t /\ ~(z = vec 0)
                      ==> (f:A->real^5)((psi:real^3->A)(inv(norm(t % z)) % (t % z))) =
                          f(psi(inv(norm z) % z))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `inv(norm(t % z)) % (t % z) = inv(norm(z:real^3)) % z`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
    SUBGOAL_THEN `~(norm(z:real^3) = &0)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* uniformization *)
  MP_TAC(ISPECL [`\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))`; `Q:real^5->real^5^5`;
                 `lam:real`] GBS2_UNIFORMIZE) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `gbs2_conformal (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h`
  ASSUME_TAC THENL [REWRITE_TAC[gbs2_conformal] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the area *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `S:A->bool`; `psi:real^3->A`; `psi':A->real^3`; `f:A->real^5`;
                 `Q:real^5->real^5^5`; `h:real^3->real^3`; `a:real`] GBS2_AREA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  (* the planar factors *)
  MP_TAC(ISPECL [`\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))`; `Q:real^5->real^5^5`;
                 `h:real^3->real^3`; `stereo2_n_inv`] GBS2_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))`; `Q:real^5->real^5^5`;
                 `h:real^3->real^3`; `stereo2_s_inv`] GBS2_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))`; `Q:real^5->real^5^5`;
                 `h:real^3->real^3`] GBS2_MU_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!w:real^2. ~(w = vec 0)
               ==> gbs2_mu (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h
                           stereo2_n_inv w =
                   gbs2_mu (\z. f(psi(inv(norm z) % z))) Q h stereo2_s_inv (cml_inv w) /
                   norm w pow 4`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GBS2_MU_REL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. mfd_scalar atlas (g:A->real^2^2) ((psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv w))) =
        --(cml_lap (\x. log(gbs2_mu (\z. (f:A->real^5)(psi(inv(norm z) % z))) Q h
                                    stereo2_n_inv x)) w) /
        gbs2_mu (\z. f(psi(inv(norm z) % z))) Q h stereo2_n_inv w`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC GBS2_CURV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `S:A->bool`; `psi':A->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. (psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv w)) IN S`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GBS2_SPHERE_FACTS o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "mfd_diffeo" with Failure _ -> false))
          (concl th))) THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `stereo2_n_inv` GBS2_STEREO_INV_FACTS) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `mu = gbs2_mu (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h
                           stereo2_n_inv` THEN
  ABBREV_TAC `mu' = gbs2_mu (\z. (f:A->real^5)((psi:real^3->A)(inv(norm z) % z))) Q h
                            stereo2_s_inv` THEN
  (* the curvature bound and the integrability of k1 mu *)
  SUBGOAL_THEN `!z:real^2. k1 * mu z <= --(cml_lap (\x. log((mu:real^2->real) x)) z) / &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN
    SUBGOAL_THEN `&2 * k1 <= mfd_scalar atlas (g:A->real^2^2)
                    ((psi:real^3->A)((h:real^3->real^3)(stereo2_n_inv z)))`
    MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        is_imp(snd(strip_forall(concl th))) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_scalar" with Failure _ -> false))
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (mu:real^2->real) z` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^2. lift(k1 * (mu:real^2->real) z)) absolutely_integrable_on (:real^2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the planar Gauss-Bonnet inequality *)
  MP_TAC(ISPECL [`mu:real^2->real`; `mu':real^2->real`; `\z:real^2. k1 * (mu:real^2->real) z`]
                P2BX46_GB_INEQ_REV) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= &4 * pi ==> y <= &4 * pi`) THEN
  REWRITE_TAC[LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; DROP_CMUL]);;

(* ========================================================================= *)
(* A lower bound for the intrinsic curvature of a level set.                 *)
(* Where sec >= 0 and R <= 1 + dl, Hess f = g/2 - Ric has eigenvalues in    *)
(* [-dl/2, 1/2] on TN, so det II >= -dl/(4|grad f|^2) and the Gauss        *)
(* equation gives R_N >= R - 2 Ric(n,n) - dl/(2|grad f|^2).                 *)
(* ========================================================================= *)

let P2BX46_QUAD_DET = prove
 (`!x y z. (!a b. &0 <= a * a * x - &2 * a * b * z + b * b * y) ==> z * z <= x * y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`&1`; `&0`]) THEN FIRST_ASSUM(MP_TAC o SPECL [`&0`; `&1`]) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_LID; REAL_MUL_RID; REAL_ADD_LID;
              REAL_ADD_RID; REAL_SUB_RZERO; REAL_SUB_LZERO] THEN
  REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_CASES_TAC `z = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(y + &1) / (&2 * z)`; `&1`]) THEN
    SUBGOAL_THEN `(y + &1) / (&2 * z) * (y + &1) / (&2 * z) * x -
                  &2 * (y + &1) / (&2 * z) * &1 * z + &1 * &1 * y = --(&1)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_LZERO] THEN
      UNDISCH_TAC `~(z = &0)` THEN CONV_TAC REAL_FIELD;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real`; `x:real`]) THEN
  SUBGOAL_THEN `z * z * x - &2 * z * x * z + x * x * y = x * (x * y - z * z)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x` (fun th -> SIMP_TAC[MATCH_MP (CONJUNCT1 REAL_LE_MUL_EQ) th]) THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* The determinant of a 2x2 form with eigenvalues in [-m, M]. *)

let P2BX46_QUAD_DET2 = prove
 (`!x y z m M. &0 <= m /\ &0 <= M /\ z * z <= (x + m) * (y + m) /\
               z * z <= (M - x) * (M - y)
               ==> --(m * M) <= x * y - z * z`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x + y <= M - m` THENL
   [SUBGOAL_THEN `m * (x + y) <= m * (M - m)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `M * (M - m) <= M * (x + y)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let P2BX46_LEVEL_RN_GE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f W u x dl.
     p2b_shrinker (top,atlas) g f /\ open_in top W /\ lvs_regular atlas W f u /\
     x IN lvs_set W f u /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v) /\
     mfd_scalar atlas g x <= &1 + dl /\ &0 <= dl /\
     &0 < lgrad2 (metric_local atlas (chart_at atlas x) g)
                 (f o chart_inv (chart_at atlas x)) (SND(chart_at atlas x) x)
     ==> mfd_scalar atlas g x -
         &2 * mfd_ricci atlas g x (lvs_normal atlas g f x) (lvs_normal atlas g f x) -
         dl / (&2 * lgrad2 (metric_local atlas (chart_at atlas x) g)
                           (f o chart_inv (chart_at atlas x)) (SND(chart_at atlas x) x)) <=
         mfd_scalar (lvs_atlas top atlas W f u) (lvs_metric top atlas g W f u) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set W f u` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. p2b_mfd_hess atlas (g:A->real^3^3) f x a b =
          inv(&2) * (a dot (g x ** b)) - mfd_ricci atlas g x a b`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `mfd_ricci atlas (g:A->real^3^3) x a b + p2b_mfd_hess atlas g f x a b =
      inv(&2) * (a dot (g x ** b))`
    MP_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `f:A->real`; `u:real`; `x:A`] LVS_GAUSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `f:A->real`; `u:real`; `x:A`] LVS_GAUSS_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^2` (X_CHOOSE_THEN `v2:real^2` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `f:A->real`; `u:real`; `x:A`] LVS_II_PUSHFORWARD) THEN
  ASM_REWRITE_TAC[P2BX46_LHESS_MFD_HESS] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `J1 = lvs_jac top atlas W (f:A->real) u x v1` THEN
  ABBREV_TAC `J2 = lvs_jac top atlas W (f:A->real) u x v2` THEN
  ABBREV_TAC `s2 = lgrad2 (metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3))
                          (f o chart_inv (chart_at atlas x)) (SND(chart_at atlas x) x)` THEN
  ABBREV_TAC `p = mfd_ricci atlas (g:A->real^3^3) x J1 J1` THEN
  ABBREV_TAC `q = mfd_ricci atlas (g:A->real^3^3) x J2 J2` THEN
  ABBREV_TAC `r = mfd_ricci atlas (g:A->real^3^3) x J1 J2` THEN
  (* Ric on span(J1,J2): 0 <= Ric(w,w) <= (1 + dl)/2 |w|^2 *)
  SUBGOAL_THEN
   `!a b. &0 <= a * a * p + &2 * a * b * r + b * b * q /\
          a * a * p + &2 * a * b * r + b * b * q <= (&1 + dl) / &2 * (a * a + b * b)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
    ABBREV_TAC `w = a % (J1:real^3) + b % J2` THEN
    SUBGOAL_THEN `transp((g:A->real^3^3) x) = g x` ASSUME_TAC THENL
     [UNDISCH_TAC `metric_field (IMAGE (SND(chart_at atlas (x:A))) (FST(chart_at atlas x)))
                     (metric_local (atlas:((A->bool)#(A->real^3))->bool) (chart_at atlas x)
                                   (g:A->real^3^3))` THEN
      REWRITE_TAC[metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x` o
                 CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `w dot ((g:A->real^3^3) x ** w) = a * a + b * b` ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LADD; DOT_RADD;
                  DOT_LMUL; DOT_RMUL] THEN
      SUBGOAL_THEN `(J2:real^3) dot ((g:A->real^3^3) x ** J1) = J1 dot (g x ** J2)` SUBST1_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN
        REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?M:real^3^3. !v w. mfd_ricci atlas (g:A->real^3^3) x v w = v dot (M ** w)`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `(lambda i j. lricci (metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3))
                                     (SND(chart_at atlas x) x) (basis i) (basis j)):real^3^3` THEN
      MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                            (FST(chart_at atlas x))`;
                     `metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`]
        P2BX46_LRIC_MATRIX_DOT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[mfd_ricci];
      ALL_TAC] THEN
    SUBGOAL_THEN `(J2:real^3) dot ((M:real^3^3) ** J1) = J1 dot (M ** J2)` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[mfd_ricci] THEN
      MATCH_MP_TAC LRICCI_SYM THEN
      EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_ricci atlas (g:A->real^3^3) x w w = a * a * p + &2 * a * b * r + b * b * q`
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["p"; "q"; "r"; "w"] THEN
      REWRITE_TAC[ASSUME `!v w. mfd_ricci atlas (g:A->real^3^3) x v w = v dot ((M:real^3^3) ** w)`] THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LADD; DOT_RADD;
                  DOT_LMUL; DOT_RMUL] THEN
      REWRITE_TAC[ASSUME `(J2:real^3) dot ((M:real^3^3) ** J1) = J1 dot (M ** J2)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[SYM th]) o
      check (fun th -> is_eq(concl th) && lhs(concl th) =
        `mfd_ricci atlas (g:A->real^3^3) x w w`)) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[mfd_ricci] THEN
      MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                            (FST(chart_at atlas x))`;
                     `metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                     `&0`; `w:real^3`] CMPZ_LRICCI_SEC_LOWER) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; GSYM mfd_sectional];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `w:real^3`] P2BX46_MFD_RIC_LE_HALF) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) x * (a * a + b * b) <=
                  (&1 + dl) * (a * a + b * b)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `a:real` REAL_LE_SQUARE) THEN MP_TAC(SPEC `b:real` REAL_LE_SQUARE) THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the Hessian on span(J1,J2) has eigenvalues in [-dl/2, 1/2] *)
  SUBGOAL_THEN `--((dl / &2) * inv(&2)) <= (inv(&2) - p) * (inv(&2) - q) - r * r`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_QUAD_DET2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC P2BX46_QUAD_DET THEN MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`]) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `--r * --r <= x ==> r * r <= x`) THEN
      MATCH_MP_TAC P2BX46_QUAD_DET THEN MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`]) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt s2 /\ sqrt s2 pow 2 = s2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(inv(&2) - p) / sqrt s2 * (inv(&2) - q) / sqrt s2 - ((&0 - r) / sqrt s2) pow 2 =
    ((inv(&2) - p) * (inv(&2) - q) - r pow 2) / s2`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    ABBREV_TAC `t = sqrt s2` THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `--(dl / (&2 * s2)) <= &2 * d ==> a - dl / (&2 * s2) <= a + &2 * d`) THEN
  SUBGOAL_THEN `--(dl / (&2 * s2)) = &2 * (--(dl / &4) / s2)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < s2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* |nabla Rm| is bounded on the soliton (Shi's estimate,                     *)
(* P2A_REQ_SHI_SCALED_STATEMENT of pc_rfa_shiscale, for the soliton flow G   *)
(* on (-1 - r^2, -1], where |Rm(G t)| <= |Rm(g)| / |t| <= K1).              *)
(* ========================================================================= *)

let P2BX46_G_M1 = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K x.
     p2bx46_hyp top atlas g f K /\ x IN topspace top
     ==> p2bx46_G top atlas g f (--(&1)) x = g x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  REWRITE_TAC[P2BX46_G_PHI; REAL_ABS_NEG; REAL_ABS_NUM; MATRIX_CMUL_LID] THEN
  REWRITE_TAC[mfd_pullback_metric] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `x:A`] P2BX46_PHI_REFL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) (SND c x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX46_MPULLBACK_ID_LOCAL THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `K:real`; `chart_inv (c:(A->bool)#(A->real^N)) z`]
      P2BX46_PHI_REFL) THEN
    ASM_SIMP_TAC[];
    EXPAND_TAC "c" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* Copies of P2AU_BALL_CLOSURE_COMPACT (pc_p2a_flow3) and                   *)
(* P2AK0_FLOW_UPTO_OF_ON (pc_p2a_kap0): those units would add 27 and 6      *)
(* files to the closure for these two short lemmas.                          *)

let P2BX46_BALL_CLOSURE_COMPACT = prove
 (`!top atlas (g:A->real^N^N) p r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p IN topspace top
     ==> compact_in top (top closure_of (mfd_ball (top,atlas) g p r))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) p r` THEN
  REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top,atlas) (g:A->real^N^N)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LT_IMP_LE]]);;

let P2BX46_FLOW_UPTO_OF_ON = prove
 (`!top atlas a b (g:real->B->real^3^3) t1.
     ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t1 < b
     ==> rfs_flow_upto (top,atlas) a t1 g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`b - t1`;
      `\z:real^(1,3)finite_sum. (vectorize:real^3^3->real^(3,3)finite_prod)
         (metric_local atlas c ((g:real->B->real^3^3) (drop(fstcart z))) (sndcart z))`] THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_ARITH `t1 + (b - t1) = b`; FSTCART_PASTECART;
                 SNDCART_PASTECART; LIFT_DROP]]);;

let P2BX46_SHI_SOL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K K1.
     p2bx46_hyp top atlas g f K /\ &0 <= K1 /\
     (!x. x IN topspace top ==> mfd_rm_norm atlas g x <= K1)
     ==> ?C. !x. x IN topspace top
                 ==> lrm_deriv_norm2 1 (metric_local atlas (chart_at atlas x) g)
                                       (SND(chart_at atlas x) x) <= C`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(REWRITE_RULE[P2A_REQ_SHI_SCALED_STATEMENT]
           (ISPEC `UNIV:A->bool` RFA_P2A_REQ_SHI_SCALED)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "shi"))) THEN
  ABBREV_TAC `K2 = max K1 (&1)` THEN
  SUBGOAL_THEN `&1 <= K2 /\ K1 <= K2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K2" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = inv(sqrt K2)` THEN
  SUBGOAL_THEN `&0 < r /\ &0 < r pow 2 /\ r pow 2 <= &1 /\ inv(r pow 2) = K2 /\
                inv(r pow 6) = K2 pow 3`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt K2 /\ sqrt K2 pow 2 = K2` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_ARITH `&1 <= x ==> &0 < x`;
                   REAL_ARITH `&1 <= x ==> &0 <= x`];
      ALL_TAC] THEN
    EXPAND_TAC "r" THEN ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_INV; REAL_INV_INV] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ARITH_RULE `6 = 2 * 3`; GSYM REAL_POW_POW] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `C0 * K2 pow 3` THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (--(&1) - r pow 2) (&0)
                 (p2bx46_G top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_SOL_RICCI_FLOW THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "shi" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `--(&1) - r pow 2`; `--(&1)`;
    `p2bx46_G top atlas (g:A->real^3^3) f`; `x:A`; `r:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BX46_FLOW_UPTO_OF_ON THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      MATCH_MP_TAC P2BX46_BALL_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BX46_SOL_RIEM THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC P2BX46_SOL_COMPLETE THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas)
                       (p2bx46_G top atlas (g:A->real^3^3) f (--(&1))) x r` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K1 / abs t` THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BX46_SOL_RM_NORM THEN EXISTS_TAC `K:real` THEN
        ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `f:A->real`; `K:real`; `t:real`] P2BX46_SOL_FLOW) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `&1 <= abs t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K1:real` THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `p2bx46_G top atlas (g:A->real^3^3) f (--(&1))`; `x:A`; `r / &2`]
      MFD_CENTRE_IN_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX46_SOL_RIEM THEN EXISTS_TAC `K:real` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `p2bx46_G top atlas (g:A->real^3^3) f (--(&1))`; `g:A->real^3^3`;
                 `topspace top:A->bool`; `x:A`] P2B9S_METRIC_LOCAL_EQ_ON) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P2BX46_G_M1 THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC)] THEN
  MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN EXISTS_TAC `s:real^3->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* |dR| <= C |w| on the soliton.  In a G-orthonormal frame S                 *)
(* (matrix_inv G = S^T S), dR(S^T e_b) is a trace of nabla Ric             *)
(* (RFA_HT_DSC_FRAME), each frame value of nabla Ric is bounded by its norm *)
(* (RFA_HT_FRAME_ABS), |nabla Ric|^2 <= N |nabla Rm|^2 (RFA_HT_DRIC_NORM), *)
(* and dR(V) is expanded in the frame (RFA_HT_DSC_EXPAND).  With (9.21),    *)
(* 2 Ric(grad f, w) = dR(w) is bounded by C |w|.                            *)
(* ========================================================================= *)

let P2BX46_DSCALAR_BOUND = prove
 (`!U (G:real^N->real^N^N) y V.
     metric_field U G /\ y IN U
     ==> abs(drop(frechet_derivative (\x. lift(lscalar G x)) (at y) V)) <=
         &(dimindex(:N)) * &(dimindex(:N)) *
         sqrt(&(dimindex(:N)) * lrm_deriv_norm2 1 G y) * sqrt(V dot (G y ** V))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `D = &(dimindex(:N)) * lrm_deriv_norm2 1 (G:real^N->real^N^N) y` THEN
  SUBGOAL_THEN `ltnorm2 3 G (lnabla 2 G (lric2 G)) (y:real^N) <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC RFA_HT_DRIC_NORM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. 1 <= b /\ b <= dimindex(:N)
        ==> abs(drop(frechet_derivative (\x. lift(lscalar (G:real^N->real^N^N) x)) (at y)
                       (transp(S:real^N^N) ** basis b))) <= &(dimindex(:N)) * sqrt D`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`; `b:num`]
      RFA_HT_DSC_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
    MATCH_MP_TAC SUM_ABS_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC RFA_HT_FRAME_ABS THEN
    MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`; `G:real^N->real^N^N`] THEN
    ASM_SIMP_TAC[LRG_N2_FIELD; LENGTH; ALL; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. 1 <= b /\ b <= dimindex(:N)
        ==> abs((transp(S:real^N^N) ** basis b) dot ((G:real^N->real^N^N) y ** V)) <=
            sqrt(V dot (G y ** V))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(transp(S:real^N^N) ** basis b) dot
                  ((G:real^N->real^N^N) y ** (transp S ** basis b)) = &1`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`] RFA_HT_GRAM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `matrix_inv(transp(S:real^N^N))`;
                     `transp(S:real^N^N) ** basis b`; `transp(S:real^N^N) ** basis b`]
        LRG_FRAME_DOT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN `invertible(transp(S:real^N^N))` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[INVERTIBLE_TRANSP]; ALL_TAC] THEN
      ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
      ASM_SIMP_TAC[DOT_BASIS_BASIS];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `transp(S:real^N^N) ** basis b`; `V:real^N`] LRG_METRIC_CS) THEN
    ASM_REWRITE_TAC[REAL_MUL_LID] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM POW_2_SQRT_ABS] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`; `V:real^N`]
    RFA_HT_DSC_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(dimindex(:N)) *
              (sqrt(V dot ((G:real^N->real^N^N) y ** V)) * (&(dimindex(:N)) * sqrt D))` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
    MATCH_MP_TAC SUM_ABS_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[];
    REAL_ARITH_TAC]);;

(* (9.21) and the frame bound: |2 Ric(grad f, w)| = |dR(w)| <= C1 |w|. *)

let P2BX46_RIC_GRADF_BOUND = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K K1.
     p2bx46_hyp top atlas g f K /\ &0 <= K1 /\
     (!x. x IN topspace top ==> mfd_rm_norm atlas g x <= K1)
     ==> ?C1. &0 <= C1 /\
              !x w. x IN topspace top
                    ==> abs(&2 * mfd_ricci atlas g x (p2bx46_gradf atlas g f x) w) <=
                        C1 * sqrt(w dot (g x ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `K1:real`] P2BX46_SHI_SOL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
  EXISTS_TAC `&3 * &3 * sqrt(&3 * max C (&0))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `w:real^3`] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`]
    RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)`;
                 `\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool)
                                                       (x:A)) y)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                 `w:real^3`] P2BX46_DR_GRAD) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `matrix_inv(metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)
                 (SND(chart_at atlas x) x)) **
    (lambda a. rfa_d1 (\y. (f:A->real)(chart_inv (chart_at atlas x) y))
                      (SND(chart_at atlas x) x) (basis a)) =
    p2bx46_gradf atlas g f x`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2bx46_gradf; p3s_cgrad; P3S_JAC_ROW1; rfa_d1]; ALL_TAC] THEN
  REWRITE_TAC[GSYM mfd_ricci] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                 `w:real^3`] P2BX46_DSCALAR_BOUND) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; DIMINDEX_3] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `&0 <= w dot ((g:A->real^3^3) x ** w)` ASSUME_TAC THENL
   [ASM_CASES_TAC `w:real^3 = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `metric_field (IMAGE (SND(chart_at atlas (x:A))) (FST(chart_at atlas x)))
                   (metric_local (atlas:((A->bool)#(A->real^3))->bool) (chart_at atlas x)
                                 (g:A->real^3^3))` THEN
    REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x` o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= c ==> a <= max c (&0)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Alignment of a covector with a nearly extremal vector.  If                *)
(* lam(Z)^2 <= a |Z|^2 for all Z and lam(W0)^2 >= b |W0|^2, then the         *)
(* G-dual of W0 is mu lam up to sqrt(1 - b/a) |W0| (a Cauchy-Schwarz        *)
(* argument with the G-dual vector l of lam).                               *)
(* ========================================================================= *)

let P2BX46_COVEC_ALIGN0 = prove
 (`!U (G:real^N->real^N^N) y (l:real^N) (W0:real^N) a b.
     metric_field U G /\ y IN U /\ ~(W0 = vec 0) /\ &0 < b /\ b <= a /\
     (!Z. (Z dot (G y ** l)) pow 2 <= a * (Z dot (G y ** Z))) /\
     b * (W0 dot (G y ** W0)) <= (W0 dot (G y ** l)) pow 2
     ==> &0 < l dot (G y ** l) /\ l dot (G y ** l) <= a /\
         (!Z. (Z dot (G y ** l)) pow 2 <= (l dot (G y ** l)) * (Z dot (G y ** Z))) /\
         !Z. abs(Z dot (G y ** W0) -
                 (W0 dot (G y ** l)) / (l dot (G y ** l)) * (Z dot (G y ** l)))
             <= sqrt((&1 - b / a) * (W0 dot (G y ** W0))) * sqrt(Z dot (G y ** Z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y /\
                !v. ~(v = vec 0) ==> &0 < v dot (G y ** v)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `!Z. &0 <= Z dot ((G:real^N->real^N^N) y ** Z)` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `Z:real^N = vec 0` THEN
    ASM_SIMP_TAC[DOT_LZERO; REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < W0 dot ((G:real^N->real^N^N) y ** W0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((W0:real^N) dot ((G:real^N->real^N^N) y ** l) = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `&0 < b * (W0 dot ((G:real^N->real^N^N) y ** W0))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `b * (W0 dot ((G:real^N->real^N^N) y ** W0)) <=
                 (W0 dot (G y ** l)) pow 2` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(l:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((W0:real^N) dot ((G:real^N->real^N^N) y ** l) = &0)` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO];
    ALL_TAC] THEN
  ABBREV_TAC `q = (l:real^N) dot ((G:real^N->real^N^N) y ** l)` THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [EXPAND_TAC "q" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!Z. (Z dot ((G:real^N->real^N^N) y ** l)) pow 2 <= q * (Z dot (G y ** Z))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `Z:real^N`; `l:real^N`]
      LRG_METRIC_CS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `q <= a` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `l:real^N` o check (fun th ->
      is_forall(concl th) && not(can (find_term ((=) `q:real`)) (concl th)) &&
      can (find_term ((=) `a:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `Z:real^N` THEN
  ABBREV_TAC `c = ((W0:real^N) dot ((G:real^N->real^N^N) y ** l)) / q` THEN
  ABBREV_TAC `E = (W0:real^N) - c % l` THEN
  SUBGOAL_THEN `Z dot ((G:real^N->real^N^N) y ** W0) - c * (Z dot (G y ** l)) =
                Z dot (G y ** E)`
  SUBST1_TAC THENL
   [EXPAND_TAC "E" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RSUB; DOT_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^N) dot ((G:real^N->real^N^N) y ** W0) = W0 dot (G y ** l)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [SYM(ASSUME
      `transp((G:real^N->real^N^N) y) = G y`)] THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `E dot ((G:real^N->real^N^N) y ** E) =
                W0 dot (G y ** W0) - (W0 dot (G y ** l)) pow 2 / q`
  ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RSUB; DOT_RMUL;
                DOT_LSUB; DOT_LMUL] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN
    UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `E dot ((G:real^N->real^N^N) y ** E) <= (&1 - b / a) * (W0 dot (G y ** W0))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `b / a * (W0 dot ((G:real^N->real^N^N) y ** W0)) <=
                  (W0 dot (G y ** l)) pow 2 / q`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `((W0:real^N) dot ((G:real^N->real^N^N) y ** l)) pow 2 / a` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[real_div; REAL_ARITH `(b * i) * w = (b * w) * i`] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E dot ((G:real^N->real^N^N) y ** E)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Z dot ((G:real^N->real^N^N) y ** E)) pow 2 <=
                (Z dot (G y ** Z)) * (E dot (G y ** E))` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_CS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ee = E dot ((G:real^N->real^N^N) y ** E)` THEN
  ABBREV_TAC `zz = Z dot ((G:real^N->real^N^N) y ** Z)` THEN
  ABBREV_TAC `ww = W0 dot ((G:real^N->real^N^N) y ** W0)` THEN
  SUBGOAL_THEN `&0 <= zz` ASSUME_TAC THENL
   [EXPAND_TAC "zz" THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match [] `!Z. &0 <= Z dot ((G:real^N->real^N^N) y ** Z)`) (concl th)));
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt ee * sqrt zz = sqrt(zz * ee)` ASSUME_TAC THENL
   [REWRITE_TAC[SQRT_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt ee * sqrt zz` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `sqrt ee * sqrt zz`)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM POW_2_SQRT_ABS] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC]]);;

(* ========================================================================= *)
(* Euclidean tools on the neck annulus.  A two-set global                    *)
(* inverse function theorem; derivatives along radial rays and along great  *)
(* circles; the resulting increment bounds for a C^1 function.              *)
(* ========================================================================= *)

(* SMT_OPEN_INVERSE_SMOOTH (pc_smt_cover) for a bijection between two open  *)
(* sets.                                                                     *)

let P2BX46_OPEN_INVERSE_SMOOTH2 = prove
 (`!(f:real^N->real^N) g s t.
        open s /\ open t /\ smooth_map_on s f /\
        (!x. x IN s ==> f x IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g y IN s /\ f(g y) = y) /\
        (!x. x IN s ==> ~(det(matrix(frechet_derivative f (at x))) = &0))
        ==> smooth_map_on t g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `s:real^N->bool`; `(g:real^N->real^N) y0`]
    SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `k:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `u INTER (t:real^N->bool)` THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
  UNDISCH_TAC `diffeomorphism_on t0 u (f:real^N->real^N) k` THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `k:real^N->real^N` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET]] THEN
  X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^N->real^N) v IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `t0 SUBSET (s:real^N->bool)` THEN
    UNDISCH_TAC `IMAGE (k:real^N->real^N) u = t0` THEN
    UNDISCH_TAC `(v:real^N) IN u` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) = f((k:real^N->real^N) v)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
   [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[]]);;

(* Derivative of a function along a great circle and along a ray. *)

let P2BX46_VECTOR_CHAIN = prove
 (`!(f:real^1->real^N) f' (g:real^N->real^M) x.
     (f has_vector_derivative f') (at x) /\ g differentiable at (f x)
     ==> ((g o f) has_vector_derivative (frechet_derivative g (at (f x)) f')) (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN
   `(\h. drop h % frechet_derivative (g:real^N->real^M) (at ((f:real^1->real^N) x)) f') =
    frechet_derivative g (at (f x)) o (\h. drop h % f')`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_CMUL THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN
  ASM_REWRITE_TAC[GSYM has_vector_derivative; GSYM FRECHET_DERIVATIVE_WORKS]);;

let P2BX46_ARC_DERIV = prove
 (`!(Fn:real^3->real) u q t.
     (\z. lift(Fn z)) differentiable at (cos t % u + sin t % q)
     ==> ((\s. Fn(cos s % u + sin s % q)) has_real_derivative
          drop(frechet_derivative (\z. lift(Fn z)) (at (cos t % u + sin t % q))
                 (--(sin t) % u + cos t % q))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  SUBGOAL_THEN
   `((\s:real^1. cos(drop s) % (u:real^3) + sin(drop s) % q) has_vector_derivative
     (--(sin t) % u + cos t % q)) (at (lift t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC APX_REAL_VMUL_VD THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_COS; HAS_REAL_DERIVATIVE_SIN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real^1. cos(drop s) % (u:real^3) + sin(drop s) % q`;
                 `--(sin t) % (u:real^3) + cos t % q`;
                 `\z:real^3. lift((Fn:real^3->real) z)`; `lift t`] P2BX46_VECTOR_CHAIN) THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP]);;

let P2BX46_ARC_VECS = prove
 (`!(u:real^3) q t.
     norm u = &1 /\ norm q = &1 /\ u dot q = &0
     ==> norm(cos t % u + sin t % q) = &1 /\ norm(--(sin t) % u + cos t % q) = &1 /\
         (cos t % u + sin t % q) dot (--(sin t) % u + cos t % q) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORM_EQ_1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:real^3) dot u = &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; DOT_LNEG; DOT_RNEG] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

let P2BX46_ARC_BOUND = prove
 (`!(Fn:real^3->real) u q th B.
     norm u = &1 /\ norm q = &1 /\ u dot q = &0 /\ &0 <= th /\
     (!t. &0 <= t /\ t <= th
          ==> (\z. lift(Fn z)) differentiable at (cos t % u + sin t % q)) /\
     (!z v. norm z = &1 /\ z dot v = &0 /\ (\w. lift(Fn w)) differentiable at z
            ==> abs(drop(frechet_derivative (\w. lift(Fn w)) (at z) v)) <= B * norm v)
     ==> abs(Fn(cos th % u + sin th % q) - Fn u) <= B * th`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (Fn:real^3->real)(cos s % u + sin s % q)`;
                 `\s. drop(frechet_derivative (\z. lift((Fn:real^3->real) z))
                            (at (cos s % u + sin s % q)) (--(sin s) % u + cos s % q))`;
                 `real_interval[&0,th]`; `B:real`] REAL_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`u:real^3`; `q:real^3`; `t:real`] P2BX46_ARC_VECS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BX46_ARC_DERIV THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B * norm(--(sin t) % (u:real^3) + cos t % q)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL]];
    DISCH_THEN(MP_TAC o SPECL [`th:real`; `&0`]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; COS_0; SIN_0; VECTOR_MUL_LID;
                VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_SUB_RZERO] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= th ==> abs th = th`]]);;

(* The oscillation of a function on the unit sphere is at most pi B when its *)
(* tangential derivatives are at most B.                                     *)

let P2BX46_SPHERE_OSC = prove
 (`!(Fn:real^3->real) B w w'.
     &0 <= B /\ norm w = &1 /\ norm w' = &1 /\
     (!z. norm z = &1 ==> (\v. lift(Fn v)) differentiable at z) /\
     (!z v. norm z = &1 /\ z dot v = &0 /\ (\w. lift(Fn w)) differentiable at z
            ==> abs(drop(frechet_derivative (\w. lift(Fn w)) (at z) v)) <= B * norm v)
     ==> abs(Fn w - Fn w') <= B * pi`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`w':real^3`; `w:real^3`] APX_GREAT_CIRCLE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` (X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `w:real^3`)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * th` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX46_ARC_BOUND THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`w':real^3`; `q:real^3`; `t:real`] P2BX46_ARC_VECS) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* Along a ray: if the derivative along w is at least m on [r1,r2], then  *)
(* the increment is at least m (r2 - r1).                                    *)

let P2BX46_RAY_DERIV = prove
 (`!(Fn:real^3->real) w t.
     (\z. lift(Fn z)) differentiable at (t % w)
     ==> ((\s. Fn(s % w)) has_real_derivative
          drop(frechet_derivative (\z. lift(Fn z)) (at (t % w)) w)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  SUBGOAL_THEN `((\s:real^1. drop s % (w:real^3)) has_vector_derivative w) (at (lift t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real. x`; `&1`; `t:real`; `w:real^3`] APX_REAL_VMUL_VD) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real^1. drop s % (w:real^3)`; `w:real^3`;
                 `\z:real^3. lift((Fn:real^3->real) z)`; `lift t`] P2BX46_VECTOR_CHAIN) THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP]);;

let P2BX46_RAY_INCREMENT = prove
 (`!(Fn:real^3->real) w r1 r2 m.
     r1 <= r2 /\
     (!t. r1 <= t /\ t <= r2
          ==> (\z. lift(Fn z)) differentiable at (t % w) /\
              m <= drop(frechet_derivative (\z. lift(Fn z)) (at (t % w)) w))
     ==> m * (r2 - r1) <= Fn(r2 % w) - Fn(r1 % w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (Fn:real^3->real)(s % w) - m * s`;
                 `\s. drop(frechet_derivative (\z. lift((Fn:real^3->real) z)) (at (s % w)) w) - m`;
                 `real_interval[r1,r2]`; `r1:real`; `r2:real`]
    HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL; REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BX46_RAY_DERIV THEN ASM_SIMP_TAC[];
        GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_ID]];
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* Arithmetic for the comparability of |grad f| on a neck shell. *)

let P2BX46_COMPARE_ARITH = prove
 (`!l0 lmax lmin K D.
     &0 <= K /\ &0 <= D /\ &0 <= lmin /\ lmin <= lmax /\
     &4 * (K + sqrt D + &1) <= l0 /\
     lmax pow 2 <= l0 pow 2 + K * lmax + D /\
     l0 pow 2 - K * lmax - D <= lmin pow 2
     ==> lmax <= &2 * lmin /\ l0 <= &2 * lmin /\ lmax <= &2 * l0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt D /\ sqrt D pow 2 = D` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2]; ALL_TAC] THEN
  ABBREV_TAC `s = sqrt D` THEN
  SUBGOAL_THEN `&0 < l0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lmax <= l0 + K + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(l0 + s) * (l0 + K + s) < (lmax - K) * lmax` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= K * l0 /\ &0 <= l0 * s /\ &0 <= K * s` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `lmax pow 2 <= l0 pow 2 + K * lmax + D` THEN
    REWRITE_TAC[SYM(ASSUME `s pow 2 = D`)] THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lmax <= &5 / &4 * l0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&5 / &8 * l0 <= lmin` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[ARITH] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `l0 pow 2 - K * lmax - D` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `K * lmax <= K * (&5 / &4 * l0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `K * l0 <= l0 * l0 / &4 /\ s * s <= l0 * l0 / &16` MP_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[real_div; REAL_ARITH `l0 * l0 * i = (l0 * i) * l0`] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(l0 / &4) * (l0 / &4)` THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC(SPEC `l0:real` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `s pow 2 = D` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* A level set of a function on the shell 1/e <= |z| <= e                    *)
(* whose radial derivative z . grad F is >= A > 0 and whose tangential      *)
(* derivatives are <= B |v| / |z| with 10 B <= A is a radial graph over the *)
(* unit sphere (z -> exp(F z - u) (z / |z|) is a diffeomorphism of the open *)
(* shell onto an open set containing the unit sphere).                      *)
(* ========================================================================= *)

let P2BX46_E_PI_BOUNDS = prove
 (`&5 / &2 <= exp(&1) /\ inv(exp(&1)) <= &2 / &5 /\ &1 < exp(&1) /\
   &0 < inv(exp(&1)) /\ inv(exp(&1)) < &1 /\ pi <= &16 / &5`,
  SUBGOAL_THEN `&5 / &2 <= exp(&1)` ASSUME_TAC THENL
   [MP_TAC E_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_EXP_POS_LT];
    MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC;
    MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;

let P2BX46_SHELL_CROSS = prove
 (`!(Fn:real^3->real) A B w0 w.
     (!z. inv(exp(&1)) <= norm z /\ norm z <= exp(&1)
          ==> (\v. lift(Fn v)) differentiable at z /\
              A <= drop(frechet_derivative (\v. lift(Fn v)) (at z) z) /\
              (!v. z dot v = &0
                   ==> abs(drop(frechet_derivative (\v. lift(Fn v)) (at z) v))
                       <= B * norm v / norm z)) /\
     &0 < A /\ &0 <= B /\ &10 * B <= A /\ norm w0 = &1 /\ norm w = &1
     ==> Fn(inv(exp(&1)) % w) < Fn w0 /\ Fn w0 < Fn(exp(&1) % w)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sh") STRIP_ASSUME_TAC) THEN
  STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN
  SUBGOAL_THEN `abs((Fn:real^3->real) w - Fn w0) <= B * pi` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_SPHERE_OSC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REMOVE_THEN "sh" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN REMOVE_THEN "sh" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[REAL_DIV_1]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 < t /\ inv(exp(&1)) <= t /\ t <= exp(&1)
                    ==> (\v. lift((Fn:real^3->real) v)) differentiable at (t % w) /\
                        A * inv t <= drop(frechet_derivative (\v. lift(Fn v)) (at (t % w)) w)`
  (LABEL_TAC "ray") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REMOVE_THEN "sh" (MP_TAC o SPEC `t % (w:real^3)`) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `linear(frechet_derivative (\v. lift((Fn:real^3->real) v)) (at (t % (w:real^3))))`
    ASSUME_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `A <= drop(frechet_derivative (\v. lift((Fn:real^3->real) v)) (at (t % w))
                             (t % (w:real^3)))` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    REWRITE_TAC[DROP_CMUL] THEN DISCH_TAC THEN
    ABBREV_TAC `d = drop(frechet_derivative (\v. lift((Fn:real^3->real) v)) (at (t % w)) w)` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(t * d) * inv t` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_FIELD `&0 < t ==> (t * d) * inv t = d`; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A * inv(exp(&1))) * (exp(&1) - &1) <=
                (Fn:real^3->real)(exp(&1) % w) - Fn(&1 % w)`
  MP_TAC THENL
   [MATCH_MP_TAC P2BX46_RAY_INCREMENT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "ray" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A * inv t` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `A * (&1 - inv(exp(&1))) <= (Fn:real^3->real)(&1 % w) - Fn(inv(exp(&1)) % w)`
  MP_TAC THENL
   [MATCH_MP_TAC P2BX46_RAY_INCREMENT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "ray" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A * inv t` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(A * inv(exp(&1))) * (exp(&1) - &1) = A * (&1 - inv(exp(&1)))` SUBST1_TAC THENL
   [MP_TAC(SPEC `&1` REAL_EXP_POS_LT) THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN
  SUBGOAL_THEN `B * pi <= &16 / &50 * A /\ &3 / &5 * A <= A * (&1 - inv(exp(&1)))`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * &16 / &5` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Rays through the shell: the radial derivative bound in the parameter t. *)

let P2BX46_SHELL_RAY = prove
 (`!(Fn:real^3->real) A B w t.
     (!z. inv(exp(&1)) <= norm z /\ norm z <= exp(&1)
          ==> (\v. lift(Fn v)) differentiable at z /\
              A <= drop(frechet_derivative (\v. lift(Fn v)) (at z) z) /\
              (!v. z dot v = &0
                   ==> abs(drop(frechet_derivative (\v. lift(Fn v)) (at z) v))
                       <= B * norm v / norm z)) /\
     norm w = &1 /\ &0 < t /\ inv(exp(&1)) <= t /\ t <= exp(&1)
     ==> (\v. lift(Fn v)) differentiable at (t % w) /\
         A * inv t <= drop(frechet_derivative (\v. lift(Fn v)) (at (t % w)) w)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sh") STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "sh" (MP_TAC o SPEC `t % (w:real^3)`) THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\v. lift((Fn:real^3->real) v)) (at (t % (w:real^3))))`
  ASSUME_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `A <= drop(frechet_derivative (\v. lift((Fn:real^3->real) v)) (at (t % w))
                           (t % (w:real^3)))` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[DROP_CMUL] THEN DISCH_TAC THEN
  ABBREV_TAC `d = drop(frechet_derivative (\v. lift((Fn:real^3->real) v)) (at (t % w)) w)` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(t * d) * inv t` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_FIELD `&0 < t ==> (t * d) * inv t = d`; REAL_LE_REFL]]);;

let P2BX46_RAY_STRICT = prove
 (`!(Fn:real^3->real) A B w t1 t2.
     (!z. inv(exp(&1)) <= norm z /\ norm z <= exp(&1)
          ==> (\v. lift(Fn v)) differentiable at z /\
              A <= drop(frechet_derivative (\v. lift(Fn v)) (at z) z) /\
              (!v. z dot v = &0
                   ==> abs(drop(frechet_derivative (\v. lift(Fn v)) (at z) v))
                       <= B * norm v / norm z)) /\
     &0 < A /\ norm w = &1 /\ inv(exp(&1)) <= t1 /\ t1 < t2 /\ t2 <= exp(&1)
     ==> Fn(t1 % w) < Fn(t2 % w)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sh") STRIP_ASSUME_TAC) THEN
  STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN
  SUBGOAL_THEN `(A * inv(exp(&1))) * (t2 - t1) <= (Fn:real^3->real)(t2 % w) - Fn(t1 % w)`
  MP_TAC THENL
   [MATCH_MP_TAC P2BX46_RAY_INCREMENT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`Fn:real^3->real`; `A:real`; `B:real`; `w:real^3`; `t:real`]
      P2BX46_SHELL_RAY) THEN
    ANTS_TAC THENL [USE_THEN "sh" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A * inv t` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (A * inv(exp(&1))) * (t2 - t1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* The map Psi(z) = exp(F z - u) (z / |z|) and its derivative. *)

let P2BX46_PSI_DERIV = prove
 (`!(Fn:real^3->real) u y.
     ~(y = vec 0) /\ (\z. lift(Fn z)) differentiable at y
     ==> ((\z. exp(Fn z - u) % (inv(norm z) % z)) has_derivative
          (\h. exp(Fn y - u) % (inv(norm y) % h - ((y dot h) / norm y pow 3) % y) +
               (exp(Fn y - u) * drop(frechet_derivative (\z. lift(Fn z)) (at y) h)) %
               (inv(norm y) % y))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. exp((Fn:real^3->real) z - u)`;
                 `\h:real^3. exp((Fn:real^3->real) y - u) *
                             drop(frechet_derivative (\z. lift(Fn z)) (at y) h)`;
                 `\z:real^3. inv(norm z) % z`;
                 `\h:real^3. inv(norm(y:real^3)) % h - ((y dot h) / norm y pow 3) % y`;
                 `y:real^3`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`exp`; `exp((Fn:real^3->real) y - u)`;
                   `\z:real^3. lift((Fn:real^3->real) z - u)`;
                   `frechet_derivative (\z:real^3. lift((Fn:real^3->real) z)) (at y)`;
                   `y:real^3`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
    REWRITE_TAC[LIFT_DROP; HAS_REAL_DERIVATIVE_EXP] THEN ANTS_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN
      MP_TAC(ISPECL [`\z:real^3. lift((Fn:real^3->real) z)`;
                     `frechet_derivative (\z:real^3. lift((Fn:real^3->real) z)) (at y)`;
                     `\z:real^3. lift u`; `\h:real^3. vec 0:real^1`; `at (y:real^3)`]
        HAS_DERIVATIVE_SUB) THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO; ETA_AX] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      REWRITE_TAC[o_DEF] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL; LIFT_DROP]];
    MATCH_MP_TAC BEL_NORMALIZE_HAS_DERIVATIVE THEN ASM_REWRITE_TAC[]]);;

let P2BX46_PSI_KERNEL = prove
 (`!(L:real^3->real^1) (y:real^3) h E A.
     ~(y = vec 0) /\ linear L /\ &0 < E /\ &0 < A /\ A <= drop(L y) /\
     E % (inv(norm y) % h - ((y dot h) / norm y pow 3) % y) +
     (E * drop(L h)) % (inv(norm y) % y) = vec 0
     ==> h = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) dot y = norm y pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
  ABBREV_TAC `n = norm(y:real^3)` THEN
  ABBREV_TAC `d = drop((L:real^3->real^1) h)` THEN
  ABBREV_TAC `c = ((y:real^3) dot h) / n pow 3` THEN
  ABBREV_TAC `k = n * c - d` THEN
  SUBGOAL_THEN `(h:real^3) = k % y` ASSUME_TAC THENL
   [SUBGOAL_THEN `(E * inv n) % (h:real^3) = (E * c - E * d * inv n) % y` MP_TAC THENL
     [UNDISCH_TAC `E % (inv n % h - c % y) + (E * d) % (inv n % y) = vec 0:real^3` THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(%) (n * inv E):real^3->real^3`) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(n * inv E) * E * inv n = &1 /\
                  (n * inv E) * (E * c - E * d * inv n) = k`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN UNDISCH_TAC `&0 < E` THEN UNDISCH_TAC `&0 < n` THEN
      CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[VECTOR_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^3) dot h = k * n pow 2` MP_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      ASM_REWRITE_TAC[DOT_RMUL];
      ALL_TAC] THEN
    UNDISCH_TAC `((y:real^3) dot h) / n pow 3 = c` THEN UNDISCH_TAC `n * c - d = k` THEN
    UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `k * drop((L:real^3->real^1) y) = &0` MP_TAC THENL
   [UNDISCH_TAC `drop((L:real^3->real^1) h) = d` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [ASSUME `(h:real^3) = k % y`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    ASM_REWRITE_TAC[DROP_CMUL];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO]; ASM_REAL_ARITH_TAC]);;

(* The radial graph. *)

let p2bx46_shell = new_definition
 `p2bx46_shell (Fn:real^3->real) A B <=>
    !z. inv(exp(&1)) <= norm z /\ norm z <= exp(&1)
        ==> (\v. lift(Fn v)) differentiable at z /\
            A <= drop(frechet_derivative (\v. lift(Fn v)) (at z) z) /\
            (!v. z dot v = &0
                 ==> abs(drop(frechet_derivative (\v. lift(Fn v)) (at z) v))
                     <= B * norm v / norm z)`;;

let P2BX46_ANNULUS_E = prove
 (`!z:real^3. z IN annulus (inv(exp(&1))) (exp(&1))
              ==> inv(exp(&1)) < norm z /\ norm z < exp(&1) /\
                  inv(exp(&1)) <= norm z /\ norm z <= exp(&1) /\ ~(z = vec 0)`,
  GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_REAL_ARITH_TAC);;

let P2BX46_PSI_DET = prove
 (`!(Fn:real^3->real) A B u z.
     p2bx46_shell Fn A B /\ &0 < A /\ z IN annulus (inv(exp(&1))) (exp(&1))
     ==> ~(det(matrix(frechet_derivative
                (\z. exp(Fn z - u) % (inv(norm z) % z)) (at z))) = &0)`,
  REWRITE_TAC[p2bx46_shell] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX46_ANNULUS_E) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Fn:real^3->real`; `u:real`; `z:real^3`] P2BX46_PSI_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]) THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET; NOT_EXISTS_THM] THEN
  X_GEN_TAC `h:real^3` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(h:real^3 = vec 0)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BX46_PSI_KERNEL THEN
  MAP_EVERY EXISTS_TAC [`frechet_derivative (\v. lift((Fn:real^3->real) v)) (at z)`;
                        `z:real^3`; `exp((Fn:real^3->real) z - u)`; `A:real`] THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

let P2BX46_PSI_INJ = prove
 (`!(Fn:real^3->real) A B u z z'.
     p2bx46_shell Fn A B /\ &0 < A /\
     z IN annulus (inv(exp(&1))) (exp(&1)) /\ z' IN annulus (inv(exp(&1))) (exp(&1)) /\
     exp(Fn z - u) % (inv(norm z) % z) = exp(Fn z' - u) % (inv(norm z') % z')
     ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `z:real^3` P2BX46_ANNULUS_E) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `z':real^3` P2BX46_ANNULUS_E) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(inv(norm z) % (z:real^3)) = &1 /\ norm(inv(norm z') % (z':real^3)) = &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `exp((Fn:real^3->real) z - u) = exp(Fn z' - u)` ASSUME_TAC THENL
   [UNDISCH_TAC `exp((Fn:real^3->real) z - u) % (inv(norm z) % z) =
                 exp(Fn z' - u) % (inv(norm z') % z')` THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH `abs(exp x) = exp x <=> &0 <= exp x`] THEN
    SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm z) % (z:real^3) = inv(norm z') % z'` ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN
    EXISTS_TAC `exp((Fn:real^3->real) z - u)` THEN
    REWRITE_TAC[REAL_EXP_NZ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fn:real^3->real) z = Fn z'` ASSUME_TAC THENL
   [UNDISCH_TAC `exp((Fn:real^3->real) z - u) = exp(Fn z' - u)` THEN
    REWRITE_TAC[REAL_EXP_INJ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `w = inv(norm z) % (z:real^3)` THEN
  SUBGOAL_THEN `norm z % w = (z:real^3) /\ norm z' % w = (z':real^3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "w"; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(z:real^3) = norm(z':real^3)` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH `~(a = b) ==> a < b \/ b < a`)) THENL
   [MP_TAC(ISPECL [`Fn:real^3->real`; `A:real`; `B:real`; `w:real^3`;
                   `norm(z:real^3)`; `norm(z':real^3)`] P2BX46_RAY_STRICT);
    MP_TAC(ISPECL [`Fn:real^3->real`; `A:real`; `B:real`; `w:real^3`;
                   `norm(z':real^3)`; `norm(z:real^3)`] P2BX46_RAY_STRICT)] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[p2bx46_shell]) THEN ASM_REWRITE_TAC[REAL_LT_REFL]);;

(* Every ray meets the level u inside the open shell. *)

let P2BX46_RAY_IVT = prove
 (`!(Fn:real^3->real) A B u w0 w.
     p2bx46_shell Fn A B /\ &0 < A /\ &0 <= B /\ &10 * B <= A /\
     norm w0 = &1 /\ Fn w0 = u /\ norm w = &1
     ==> ?t. inv(exp(&1)) < t /\ t < exp(&1) /\ Fn(t % w) = u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN
  MP_TAC(ISPECL [`Fn:real^3->real`; `A:real`; `B:real`; `w0:real^3`; `w:real^3`]
    P2BX46_SHELL_CROSS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM p2bx46_shell]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. (Fn:real^3->real)(t % w)`; `inv(exp(&1))`; `exp(&1)`; `u:real`]
    REAL_IVT_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `drop(frechet_derivative (\z. lift((Fn:real^3->real) z)) (at (t % w)) w)` THEN
      MATCH_MP_TAC P2BX46_RAY_DERIV THEN
      MP_TAC(ISPECL [`Fn:real^3->real`; `A:real`; `B:real`; `w:real^3`; `t:real`]
        P2BX46_SHELL_RAY) THEN
      ANTS_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[p2bx46_shell]) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  ASM_CASES_TAC `t = inv(exp(&1))` THENL
   [UNDISCH_TAC `(Fn:real^3->real)(t % w) = u` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = exp(&1)` THENL
   [UNDISCH_TAC `(Fn:real^3->real)(t % w) = u` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2BX46_PSI_UNIT = prove
 (`!(Fn:real^3->real) u (z:real^3) w.
     ~(z = vec 0) /\ norm w = &1 /\ exp(Fn z - u) % (inv(norm z) % z) = w
     ==> Fn z = u /\ inv(norm z) % z = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(exp((Fn:real^3->real) z - u) % (inv(norm z) % z)) = exp(Fn z - u)`
  ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_EXP; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp((Fn:real^3->real) z - u) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Fn:real^3->real) z = u` ASSUME_TAC THENL
   [UNDISCH_TAC `exp((Fn:real^3->real) z - u) = &1` THEN
    REWRITE_TAC[REAL_EXP_EQ_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `exp((Fn:real^3->real) z - u) % (inv(norm z) % z) = w` THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_EXP_0; VECTOR_MUL_LID]);;

let P2BX46_RADIAL_GRAPH = prove
 (`!(Fn:real^3->real) A B s u w0.
     open s /\ (!z. inv(exp(&1)) <= norm z /\ norm z <= exp(&1) ==> z IN s) /\
     smooth_map_on s (\z. lift(Fn z)) /\ p2bx46_shell Fn A B /\
     &0 < A /\ &0 <= B /\ &10 * B <= A /\ norm w0 = &1 /\ Fn w0 = u
     ==> ?O sig. open O /\ sphere(vec 0,&1) SUBSET O /\ smooth_map_on O sig /\
                 (!w. w IN sphere(vec 0,&1)
                      ==> sig w IN annulus (inv(exp(&1))) (exp(&1)) /\
                          Fn(sig w) = u /\ inv(norm(sig w)) % sig w = w) /\
                 (!z. z IN annulus (inv(exp(&1))) (exp(&1)) /\ Fn z = u
                      ==> sig(inv(norm z) % z) = z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open(annulus (inv(exp(&1))) (exp(&1)):real^3->bool) /\
    annulus (inv(exp(&1))) (exp(&1)) SUBSET (s:real^3->bool) /\
    annulus (inv(exp(&1))) (exp(&1)) SUBSET {x:real^3 | ~(x = vec 0)}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS; SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2BX46_ANNULUS_E) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Sh = annulus (inv(exp(&1))) (exp(&1)):real^3->bool` THEN
  ABBREV_TAC `Psi = \z:real^3. exp((Fn:real^3->real) z - u) % (inv(norm z) % z)` THEN
  SUBGOAL_THEN `smooth_map_on Sh (Psi:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Psi" THEN
    SUBGOAL_THEN
     `(\z:real^3. exp((Fn:real^3->real) z - u) % (inv(norm z) % z)) =
      (\z. drop((\z. lift(exp(drop((\z. lift(Fn z) - lift u) z)))) z) %
           (\z. inv(norm z) % z) z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP; DROP_SUB]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_EXP THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z z'. z IN Sh /\ z' IN Sh /\ (Psi:real^3->real^3) z = Psi z' ==> z = z'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_PSI_INJ THEN
    MAP_EVERY EXISTS_TAC [`Fn:real^3->real`; `A:real`; `B:real`; `u:real`] THEN
    UNDISCH_TAC `(Psi:real^3->real^3) z = Psi z'` THEN EXPAND_TAC "Psi" THEN
    UNDISCH_TAC `(z:real^3) IN Sh` THEN UNDISCH_TAC `(z':real^3) IN Sh` THEN
    EXPAND_TAC "Sh" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (Psi:real^3->real^3) Sh)` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `T0 = IMAGE (Psi:real^3->real^3) Sh` THEN
  ABBREV_TAC `ginv = \y:real^3. @z. z IN Sh /\ (Psi:real^3->real^3) z = y` THEN
  SUBGOAL_THEN
   `(!z. z IN Sh ==> (Psi:real^3->real^3) z IN T0 /\ ginv(Psi z) = z) /\
    (!y. y IN T0 ==> ginv y IN Sh /\ Psi(ginv y) = y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN EXPAND_TAC "ginv" THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SELECT_ELIM_TAC THEN ASM_MESON_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SELECT_ELIM_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on T0 (ginv:real^3->real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_OPEN_INVERSE_SMOOTH2 THEN
    MAP_EVERY EXISTS_TAC [`Psi:real^3->real^3`; `Sh:real^3->bool`] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "Psi" THEN
    MATCH_MP_TAC P2BX46_PSI_DET THEN
    MAP_EVERY EXISTS_TAC [`A:real`; `B:real`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN Sh` THEN EXPAND_TAC "Sh" THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN sphere(vec 0,&1)
                           ==> ?t. t % w IN (Sh:real^3->bool) /\
                                   (Fn:real^3->real)(t % w) = u /\ &0 < t`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`Fn:real^3->real`; `A:real`; `B:real`; `u:real`; `w0:real^3`; `w:real^3`]
      P2BX46_RAY_IVT) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    EXPAND_TAC "Sh" THEN REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RID; REAL_ARITH `&0 < x ==> abs x = x`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN sphere(vec 0,&1)
                           ==> w IN (T0:real^3->bool) /\
                               (Psi:real^3->real^3)((ginv:real^3->real^3) w) = w /\
                               ginv w IN (Sh:real^3->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN T0` (fun th -> ASM_SIMP_TAC[th]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
      can (find_term ((=) `(Fn:real^3->real)`)) (concl th) &&
      can (find_term ((=) `sphere(vec 0:real^3,&1)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(Psi:real^3->real^3)(t % w) = w` (fun th -> ASM_MESON_TAC[th]) THEN
    EXPAND_TAC "Psi" THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_EXP_0; VECTOR_MUL_LID] THEN
    UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[NORM_MUL; REAL_MUL_RID; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`T0:real^3->bool`; `ginv:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
      can (find_term ((=) `ginv:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `sphere(vec 0:real^3,&1)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL [EXPAND_TAC "Sh" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((ginv:real^3->real^3) w = vec 0)` ASSUME_TAC THENL
     [UNDISCH_TAC `(Sh:real^3->bool) SUBSET {x:real^3 | ~(x = vec 0)}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BX46_PSI_UNIT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN SIMP_TAC[IN_SPHERE_0];
      ALL_TAC] THEN
    UNDISCH_TAC `(Psi:real^3->real^3)((ginv:real^3->real^3) w) = w` THEN
    EXPAND_TAC "Psi" THEN REWRITE_TAC[];
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `inv(norm z) % (z:real^3) = (Psi:real^3->real^3) z` SUBST1_TAC THENL
     [EXPAND_TAC "Psi" THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_EXP_0; VECTOR_MUL_LID];
      ASM_SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Necks only see the metric on topspace (G(-1) = g there, so                *)
(* the necks of the soliton flow at time -1 are necks of g).                *)
(* ========================================================================= *)

let P2BX46_NECK_CONG = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G1:A->real^3^3) G2 eps x e.
     smooth_manifold_atlas top atlas /\ (!z. z IN topspace top ==> G1 z = G2 z) /\
     rfs_neck (top,atlas) G1 eps x e
     ==> rfs_neck (top,atlas) G2 eps x e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN topspace top
                    ==> mfd_scalar atlas (G1:A->real^3^3) z = mfd_scalar atlas G2 z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_scalar] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `G1:A->real^3^3`; `G2:A->real^3^3`; `topspace top:A->bool`; `z:A`]
      P2B9S_METRIC_LOCAL_EQ_ON) THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN rfs_neck_dom eps
                    ==> rfs_pullback atlas e (G1:A->real^3^3) y = rfs_pullback atlas e G2 y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pullback; mpullback] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(e:real^3->A) y`]
      CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)`]
      MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[metric_local; o_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_close_on (rfs_kreg eps) eps (rfs_neck_dom eps) (cylinder_flow (&0))
                 (\y. mfd_scalar atlas (G1:A->real^3^3) x %% rfs_pullback atlas e G1 y)` THEN
  REWRITE_TAC[rfs_close_on] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "lck_dist2" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= d ==> b <= d`) THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
  ASM_SIMP_TAC[]);;

(* The chain rule for a map that agrees near y with a composite.            *)

let P2BX46_DERIV_CHAIN_LOCAL = prove
 (`!(h1:real^M->real^N) (h2:real^N->real^P) (h:real^M->real^P) y U.
     open U /\ y IN U /\ h1 differentiable at y /\ h2 differentiable at (h1 y) /\
     (!z. z IN U ==> h z = h2(h1 z))
     ==> h differentiable at y /\
         !v. frechet_derivative h (at y) v =
             frechet_derivative h2 (at (h1 y)) (frechet_derivative h1 (at y) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(h has_derivative (frechet_derivative (h2:real^N->real^P) (at ((h1:real^M->real^N) y)) o
                       frechet_derivative h1 (at y))) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(h2:real^N->real^P) o (h1:real^M->real^N)` THEN
    UNDISCH_TAC `open(U:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[DIST_SYM];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[differentiable]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_THM]);;

(* Local chart representation of a parametrization e near y, through a      *)
(* chart c at e y: an open N on which SND c o e is smooth with values in    *)
(* the chart image, inverted by chart_inv c, with invertible derivative.     *)

let P2BX46_PARAM_CHART_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f s (e:real^3->A) c y.
     p2b_shrinker (top,atlas) g f /\ mfd_param top atlas s e /\ y IN s /\
     c IN atlas /\ e y IN FST c
     ==> open s /\
         ?N. open N /\ y IN N /\ N SUBSET s /\
             smooth_map_on N (SND c o e) /\
             (SND c o e) differentiable at y /\
             IMAGE (SND c o e) N SUBSET IMAGE (SND c) (FST c) /\
             (!z. z IN N ==> chart_inv c ((SND c o e) z) = e z) /\
             invertible(matrix(frechet_derivative (SND c o e) (at y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `e:real^3->A`; `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`]
    APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:A->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `N = {z:real^3 | z IN s /\ (e:real^3->A) z IN FST(c:(A->bool)#(A->real^3))}` THEN
  SUBGOAL_THEN `(y:real^3) IN N /\ N SUBSET (s:real^3->bool) /\
                !z. z IN N ==> z IN s /\ (e:real^3->A) z IN FST(c:(A->bool)#(A->real^3))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  EXISTS_TAC `N:real^3->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `N:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_INTER] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3)))
                          (FST c INTER IMAGE (e:real^3->A) s)`;
                   `N:real^3->bool`; `SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)`;
                   `(e2:A->real^3) o chart_inv (c:(A->bool)#(A->real^3))`; `y:real^3`]
      LRG_DIFFEO_JACOBIAN_INVERTIBLE) THEN
    ASM_REWRITE_TAC[]]);;

let P2BX46_PARAM_F_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f s (e:real^3->A).
     p2b_shrinker (top,atlas) g f /\ mfd_param top atlas s e
     ==> smooth_map_on s (\z. lift(f(e z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(e:real^3->A) y`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `s:real^3->bool`; `e:real^3->A`; `c:(A->bool)#(A->real^3)`;
                 `y:real^3`] P2BX46_PARAM_CHART_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `c:(A->bool)#(A->real^3)`] RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `N:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\w. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) w))) o
              (SND c o (e:real^3->A))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [o_THM] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
    ASM_REWRITE_TAC[]]);;

(* The gradient of f o e for the pulled-back metric: it represents the      *)
(* derivative, has the length of grad f, and sees Ric(grad f, grad f).       *)

let P2BX46_PULL_GRAD = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f s (e:real^3->A) y.
     p2b_shrinker (top,atlas) g f /\ mfd_param top atlas s e /\ y IN s
     ==> ?W0. (!v. drop(frechet_derivative (\z. lift(f(e z))) (at y) v) =
                   v dot (rfs_pullback atlas e g y ** W0)) /\
              W0 dot (rfs_pullback atlas e g y ** W0) = p2bx46_ngrad atlas g f (e y) /\
              lricci (rfs_pullback atlas e g) y W0 W0 =
              mfd_ricci atlas g (e y) (p2bx46_gradf atlas g f (e y))
                                      (p2bx46_gradf atlas g f (e y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `s:real^3->bool`; `e:real^3->A`; `y:real^3`] APX_PULLBACK_RICCI_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) y =
    transp(matrix(frechet_derivative (SND(chart_at atlas (e y)) o e) (at y))) **
    metric_local atlas (chart_at atlas (e y)) g (SND(chart_at atlas (e y)) (e y)) **
    matrix(frechet_derivative (SND(chart_at atlas (e y)) o e) (at y))`
  SUBST1_TAC THENL [REWRITE_TAC[rfs_pullback; mpullback; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[p2bx46_ngrad; p2bx46_gradf] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(e:real^3->A) y`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `s:real^3->bool`; `e:real^3->A`; `c:(A->bool)#(A->real^3)`;
                 `y:real^3`] P2BX46_PARAM_CHART_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `c:(A->bool)#(A->real^3)`] RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) ((e:real^3->A) y) IN IMAGE (SND c) (FST c)`
  ASSUME_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) z))) differentiable
    at (SND c ((e:real^3->A) y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `J = matrix(frechet_derivative (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A))
                                            (at y))` THEN
  ABBREV_TAC `gp = metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)
                     (SND c ((e:real^3->A) y))` THEN
  ABBREV_TAC `gr = p3s_cgrad (metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3))
                             (\w. (f:A->real)(chart_inv c w)) (SND c ((e:real^3->A) y))` THEN
  SUBGOAL_THEN
   `!w. w dot ((gp:real^3^3) ** (gr:real^3)) =
        p3s_cdf (\w. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) w))
                (SND c ((e:real^3->A) y)) w`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["gp"; "gr"] THEN MATCH_MP_TAC P3S_CGRAD_DOT THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p3s_cdf (\w. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) w)) (SND c ((e:real^3->A) y))
            (gr:real^3) =
    lgrad2 (metric_local atlas c (g:A->real^3^3)) (\w. f(chart_inv c w)) (SND c (e y))`
  ASSUME_TAC THENL
   [EXPAND_TAC "gr" THEN MATCH_MP_TAC P2BX46_CDF_CGRAD THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. frechet_derivative (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)) (at y) v =
                    (J:real^3^3) ** v`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `frechet_derivative (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)) (at y)`
      MATRIX_WORKS) THEN
    ANTS_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^3^3) ** matrix_inv J ** (gr:real^3) = gr` ASSUME_TAC THENL
   [MP_TAC(ISPEC `J:real^3^3` MATRIX_INV) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. drop(frechet_derivative (\z. lift((f:A->real)((e:real^3->A) z))) (at y) v) =
        p3s_cdf (\w. f(chart_inv (c:(A->bool)#(A->real^3)) w)) (SND c (e y)) ((J:real^3^3) ** v)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)`;
                   `\w. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) w))`;
                   `\z. lift((f:A->real)((e:real^3->A) z))`; `y:real^3`; `N:real^3->bool`]
      P2BX46_DERIV_CHAIN_LOCAL) THEN
    ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
        can (find_term ((=) `chart_inv (c:(A->bool)#(A->real^3))`)) (concl th) &&
        can (find_term ((=) `N:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[o_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
    ASM_REWRITE_TAC[p3s_cdf];
    ALL_TAC] THEN
  EXISTS_TAC `matrix_inv(J:real^3^3) ** (gr:real^3)` THEN
  ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

(* ========================================================================= *)
(* Grad F in a neck, pointwise.  In the neck coordinates y the               *)
(* covector ds = sqrt 2 (y . dy)/|y|^2 is nearly extremal for the metric,   *)
(* and dF (F = f o e) is nearly parallel to it far out; so dF(y) is large   *)
(* and dF is small on the Euclidean tangent plane of the sphere through y.  *)
(* ========================================================================= *)

let P2BX46_RADIAL_ARITH = prove
 (`!X m E q a d.
     &0 < a /\ &0 <= q /\ &0 <= d /\ &2000 * d <= &1 /\ &0 <= E /\ abs(X - m) <= E /\
     &2 * (&1 - d) * q <= a * m pow 2 /\ a * E pow 2 <= &3 * d * q
     ==> q <= a * X pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 / &2000 - d) * q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?w. &0 <= w /\ q = a * w pow 2` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `sqrt(q / a)` THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_LE_DIV; REAL_LT_IMP_LE; REAL_DIV_LMUL;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&141 / &100 * w) pow 2 <= m pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `a * (&141 / &100 * w) pow 2 <= a * m pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (&1 - d) * q` THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      SUBGOAL_THEN `a * (&141 / &100 * w) pow 2 = &19881 / &10000 * q` SUBST1_TAC
      THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `E pow 2 <= (&4 / &100 * w) pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `a * E pow 2 <= a * (&4 / &100 * w) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 * d * q` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `a * (&4 / &100 * w) pow 2 = &16 / &10000 * q` SUBST1_TAC
      THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&141 / &100 * w <= abs m` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(x) <= abs m /\ &0 <= x ==> x <= abs m`) THEN
    ASM_REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `E <= &4 / &100 * w` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs E <= abs y /\ &0 <= E /\ &0 <= y ==> E <= y`) THEN
    ASM_REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `w pow 2 <= X pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let P2BX46_NECK_PT = prove
 (`!U (G:real^3->real^3^3) y (W0:real^3) a b.
     metric_field U G /\ y IN U /\ ~(y = vec 0) /\ &0 < b /\ b <= a /\
     &2000 * (&1 - b / a) <= &1 /\
     (!w. (sqrt(&2) * (y dot w) / (y dot y)) pow 2 <= a * (w dot (G y ** w))) /\
     b * (W0 dot (G y ** W0)) <= (sqrt(&2) * (y dot W0) / (y dot y)) pow 2 /\
     (!w. a * (w dot (G y ** w)) <= &3 * (w dot w) / (y dot y))
     ==> W0 dot (G y ** W0) <= a * (y dot (G y ** W0)) pow 2 /\
         !v. y dot v = &0
             ==> &2000 * a * (v dot (G y ** W0)) pow 2 <=
                 &3 * (W0 dot (G y ** W0)) * (v dot v) / (y dot y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `W0:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; DOT_RZERO] THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_MUL_RZERO; real_div; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!v. ~(v = vec 0) ==> &0 < v dot ((G:real^3->real^3^3) y ** v)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field U (G:real^3->real^3^3)` THEN REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT2 o CONJUNCT2) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Z. &0 <= Z dot ((G:real^3->real^3^3) y ** Z)` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `Z:real^3 = vec 0` THEN
    ASM_SIMP_TAC[DOT_LZERO; REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_METRIC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `l = matrix_inv((G:real^3->real^3^3) y) ** ((sqrt(&2) / (y dot y)) % y)` THEN
  SUBGOAL_THEN `!Z. Z dot ((G:real^3->real^3^3) y ** l) = sqrt(&2) * (y dot Z) / (y dot y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "l" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP MATRIX_INV th)]) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `l:real^3`; `W0:real^3`;
                 `a:real`; `b:real`] P2BX46_COVEC_ALIGN0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `lgl = l dot ((G:real^3->real^3^3) y ** l)` THEN
  SUBGOAL_THEN `&0 <= &1 - b / a /\ &0 <= W0 dot ((G:real^3->real^3^3) y ** W0)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LE] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `q = W0 dot ((G:real^3->real^3^3) y ** W0)` THEN
  ABBREV_TAC `d = &1 - b / a` THEN
  CONJ_TAC THENL
   [(* the radial derivative *)
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sqrt(d * q)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(&2) * ((y:real^3) dot y) / (y dot y) = sqrt(&2)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_MUL_RID]; ALL_TAC] THEN
    ABBREV_TAC `ds0 = sqrt(&2) * ((y:real^3) dot (W0:real^3)) / (y dot y)` THEN
    DISCH_TAC THEN MATCH_MP_TAC P2BX46_RADIAL_ARITH THEN
    MAP_EVERY EXISTS_TAC [`ds0 / lgl * sqrt(&2)`;
                          `sqrt(d * q) * sqrt(y dot ((G:real^3->real^3^3) y ** y))`; `d:real`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
      ASM_SIMP_TAC[REAL_LE_MUL];
      ASM_REWRITE_TAC[];
      (* a m^2 >= 2 (1 - d) q *)
      SUBGOAL_THEN `(ds0 / lgl * sqrt(&2)) pow 2 = &2 * ds0 pow 2 / lgl pow 2` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN
        SIMP_TAC[SQRT_POW_2; REAL_POS] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 - d = b / a` SUBST1_TAC THENL [EXPAND_TAC "d" THEN REAL_ARITH_TAC;
                                                       ALL_TAC] THEN
      SUBGOAL_THEN `b * q <= ds0 pow 2` ASSUME_TAC THENL
       [EXPAND_TAC "ds0" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < lgl pow 2 /\ lgl pow 2 <= a pow 2` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `&2 * b / a * q = (&2 * (b * q) / a pow 2) * a` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `(b * q) / a pow 2 <= ds0 pow 2 / lgl pow 2` ASSUME_TAC THENL
       [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
        `x * (&2 * a) <= y * (&2 * a) ==> (&2 * x) * a <= a * &2 * y`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      (* a E^2 <= 3 d q *)
      REWRITE_TAC[REAL_POW_MUL] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_MUL] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&3`)) (concl th))) THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_MUL_RID] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
        `(d * q) * (a * Y) <= (d * q) * &3 ==> a * (d * q) * Y <= &3 * d * q`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL]];
    (* the tangential derivative *)
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sqrt(d * q)`)) (concl th))) THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM real_div] THEN
    SUBGOAL_THEN `(v dot ((G:real^3->real^3^3) y ** W0)) pow 2 <=
                  (d * q) * (v dot (G y ** v))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(sqrt(d * q) * sqrt(v dot ((G:real^3->real^3^3) y ** v))) pow 2` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= y ==> x <= abs y`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
        MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LE_MUL];
        REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_MUL; REAL_LE_REFL]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&3`)) (concl th))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= &3 * q * ((v:real^3) dot v) / ((y:real^3) dot y)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[DOT_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2000 * a * ((d * q) * ((v:real^3) dot ((G:real^3->real^3^3) y ** v)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2000 * (d * q) * (&3 * ((v:real^3) dot v) / ((y:real^3) dot y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
        `&2000 * (d * q) * (a * Y) <= &2000 * (d * q) * Z ==>
         &2000 * a * ((d * q) * Y) <= &2000 * (d * q) * Z`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
      `(&2000 * d) * (&3 * q * V / Y) <= &1 * (&3 * q * V / Y)
       ==> &2000 * (d * q) * (&3 * V / Y) <= &3 * q * V / Y`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

(* The quadratic form of a metric field is nonnegative. *)

let P2BX46_MF_POS = prove
 (`!U (G:real^N->real^N^N) y w. metric_field U G /\ y IN U ==> &0 <= w dot (G y ** w)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `w:real^N = vec 0` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[metric_field]);;

(* |grad f|^2 in terms of the chart gradient. *)

let P2BX46_GRADF_NORM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f p.
     p2b_shrinker (top,atlas) g f /\ p IN topspace top
     ==> p2bx46_gradf atlas g f p dot (g p ** p2bx46_gradf atlas g f p) =
         p2bx46_ngrad atlas g f p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)`]
    RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[p2bx46_gradf; p2bx46_ngrad] THEN
  SUBGOAL_THEN `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)) p IN
                IMAGE (SND(chart_at atlas p)) (FST(chart_at atlas p))` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)))
                        (FST(chart_at atlas p))`;
                 `metric_local atlas (chart_at atlas (p:A)) (g:A->real^N^N)`;
                 `\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                     (p:A)) y)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)) p`;
                 `p3s_cgrad (metric_local atlas (chart_at atlas (p:A)) (g:A->real^N^N))
                    (\y. (f:A->real)(chart_inv (chart_at atlas p) y)) (SND(chart_at atlas p) p)`]
    P3S_CGRAD_DOT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)))
                      (FST(chart_at atlas p))` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC P2BX46_CDF_CGRAD THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)))
                    (FST(chart_at atlas p))` THEN ASM_REWRITE_TAC[]);;

(* The numerical constants of the neck estimates. *)

let P2BX46_NECK_CONSTS = prove
 (`!eps alpha1 r C1 L c.
     &0 < eps /\ eps <= inv(&100000) /\ &0 <= alpha1 /\ alpha1 <= inv(&100000) /\
     inv(&2) <= r /\ r <= &2 /\ &0 <= C1 /\ &16000 * C1 <= L /\ &0 < L /\
     c = (eps + &2 * alpha1) / (&1 - eps)
     ==> &0 <= c /\ c <= inv(&20000) /\ &0 <= C1 / L /\ C1 / L <= inv(&16000) /\
         &0 < (&1 - c) * r - C1 / L /\ (&1 - c) * r - C1 / L <= (&1 + c) * r /\
         &2000 * (&1 - ((&1 - c) * r - C1 / L) / ((&1 + c) * r)) <= &1 /\
         (&1 + c) * (&1 + eps) * &2 <= &3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c /\ c <= inv(&20000)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c = (eps + &2 * alpha1) / (&1 - eps)` THEN DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `c:real`)) THEN
  SUBGOAL_THEN `&0 <= C1 / L /\ C1 / L <= inv(&16000)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `t = C1 / L` THEN
  SUBGOAL_THEN `&0 <= c * r /\ c * r <= inv(&20000) * r /\
                c * eps <= inv(&20000) * inv(&100000)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < (&1 + c) * r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&2000 * (&1 - ((&1 - c) * r - t) / ((&1 + c) * r)) =
                  (&2000 * (&2 * c * r + t)) / ((&1 + c) * r)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < (&1 + c) * r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* The pointwise neck estimate for dF, F = f o e: Cauchy-Schwarz always, and *)
(* far out (|grad f| >= L) radial dominance and small tangential part.       *)

let P2BX46_NECK_GRAD_PT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K eps x e y alpha1 C1 L a.
     p2bx46_hyp top atlas g f K /\ rfs_neck (top,atlas) g eps x e /\
     y IN rfs_neck_dom eps /\ eps <= inv(&100000) /\ &0 <= alpha1 /\ alpha1 <= inv(&100000) /\
     (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
              lricci (cylinder_flow (&0)) y w w)
          <= alpha1 * (w dot (cylinder_flow (&0) y ** w))) /\
     inv(&2) <= mfd_scalar atlas g x /\ mfd_scalar atlas g x <= &2 /\
     &0 <= C1 /\
     (!p w. p IN topspace top
            ==> abs(&2 * mfd_ricci atlas g p (p2bx46_gradf atlas g f p) w) <=
                C1 * sqrt(w dot (g p ** w))) /\
     &16000 * C1 <= L /\ &0 < L /\
     a = (&1 + (eps + &2 * alpha1) / (&1 - eps)) * mfd_scalar atlas g x
     ==> (!v. a * drop(frechet_derivative (\z. lift(f(e z))) (at y) v) pow 2 <=
              &3 * p2bx46_ngrad atlas g f (e y) * (v dot v) / (y dot y)) /\
         (L pow 2 <= p2bx46_ngrad atlas g f (e y)
          ==> p2bx46_ngrad atlas g f (e y) <=
              a * drop(frechet_derivative (\z. lift(f(e z))) (at y) y) pow 2 /\
              (!v. y dot v = &0
                   ==> &2000 * a * drop(frechet_derivative (\z. lift(f(e z))) (at y) v) pow 2
                       <= &3 * p2bx46_ngrad atlas g f (e y) * (v dot v) / (y dot y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `a:real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `&0 < eps /\ mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_NECK_DOM_NONZERO) THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET topspace top` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`] P2BX46_PULL_GRAD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:real^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `(e:real^3->A) y`] P2BX46_GRADF_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the Ricci form of the pulled-back metric is >= 0 *)
  SUBGOAL_THEN `!w. &0 <= lricci (rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)) y w w`
  (LABEL_TAC "ricpos") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`; `w:real^3`; `w:real^3`]
      APX_PULLBACK_RICCI_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`; `alpha1:real`]
    APX_NECK_DS_ESTIMATE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ds") THEN
  SUBGOAL_THEN
   `!w. mfd_scalar atlas (g:A->real^3^3) x *
        (w dot (rfs_pullback atlas (e:real^3->A) g y ** w)) <=
        (&1 + eps) * (&2 / ((y:real^3) dot y) * (w dot w))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`; `w:real^3`]
      APX_NECK_C0_BOUNDS) THEN
    ASM_REWRITE_TAC[APX_CYL0_QUAD; MATRIX_VECTOR_LMUL; DOT_RMUL; NORM_POW_2] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `c = (eps + &2 * alpha1) / (&1 - eps)` THEN
  MP_TAC(ISPECL [`eps:real`; `alpha1:real`; `r:real`; `C1:real`; `L:real`; `c:real`]
    P2BX46_NECK_CONSTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `H = rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)` THEN
  ABBREV_TAC `q = p2bx46_ngrad atlas (g:A->real^3^3) f ((e:real^3->A) y)` THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `q:real` && lhs(concl th) = `W0 dot ((H:real^3->real^3^3) y ** W0)`)) THEN
    MATCH_MP_TAC P2BX46_MF_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the metric comparison with the cylinder: a |w|_H^2 <= 3 |w|^2 / |y|^2 *)
  SUBGOAL_THEN `!w. a * (w dot ((H:real^3->real^3^3) y ** w)) <= &3 * (w dot w) / ((y:real^3) dot y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "a" THEN
    SUBGOAL_THEN `&0 <= ((w:real^3) dot w) / ((y:real^3) dot y)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[DOT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&1 + eps`)) (concl th))) THEN
    DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + c) * ((&1 + eps) * (&2 / ((y:real^3) dot y) * ((w:real^3) dot w)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 + c) * ((&1 + eps) * (&2 / ((y:real^3) dot y) * ((w:real^3) dot w))) =
                  ((&1 + c) * (&1 + eps) * &2) * ((w dot w) / (y dot y))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* Cauchy-Schwarz *)
    X_GEN_TAC `v:real^3` THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps`; `H:real^3->real^3^3`; `y:real^3`; `v:real^3`;
                   `W0:real^3`] LRG_METRIC_CS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&3`)) (concl th))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
     [EXPAND_TAC "a" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `q * (a * ((v:real^3) dot ((H:real^3->real^3^3) y ** v)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a * X <= a * (Y * q) ==> a * X <= q * (a * Y)`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(REAL_ARITH `q * X <= q * (&3 * V / Y) ==> q * X <= &3 * q * V / Y`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC `b = (&1 - c) * r - C1 / L` THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `H:real^3->real^3^3`; `y:real^3`; `W0:real^3`;
                 `a:real`; `b:real`] P2BX46_NECK_PT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^3` THEN
      USE_THEN "ds" (MP_TAC o CONJUNCT1 o SPEC `w:real^3`) THEN
      USE_THEN "ricpos" (MP_TAC o SPEC `w:real^3`) THEN
      EXPAND_TAC "a" THEN REAL_ARITH_TAC;
      REMOVE_THEN "ds" (MP_TAC o CONJUNCT1 o SPEC `W0:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
        [`(e:real^3->A) y`; `p2bx46_gradf atlas (g:A->real^3^3) f ((e:real^3->A) y)`] o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `C1:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `L <= sqrt q /\ &0 <= sqrt q /\ sqrt q pow 2 = q` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `C1 * sqrt q <= C1 / L * q` ASSUME_TAC THENL
       [SUBGOAL_THEN `C1 * sqrt q = (C1 / L) * (L * sqrt q) /\
                      C1 / L * q = (C1 / L) * (sqrt q * sqrt q)`
        (CONJUNCTS_THEN SUBST1_TAC) THENL
         [CONJ_TAC THENL
           [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD;
            ASM_REWRITE_TAC[GSYM REAL_POW_2]];
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Phi = sqrt(f o e + C0) on a neck, pointwise.  By the                      *)
(* Hamilton identity f + C0 = R + |grad f|^2, so |grad Phi| <= 1/2 and, far *)
(* out, the radial derivative of Phi is bounded below by a constant.        *)
(* ========================================================================= *)

(* A copy of P2BX_SQRT_DERIV (pc_p2b_c910), kept here to keep the closure    *)
(* small.                                                                    *)

let P2BX46_SQRT_HAS_DERIV = prove
 (`!(f:real^M->real) D z dl.
     ((\w. lift(f w)) has_derivative D) (at z) /\ &0 < f z + dl
     ==> ((\w. lift(sqrt(f w + dl))) has_derivative
          (\h. inv(&2 * sqrt(f z + dl)) % D h)) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\w. lift(sqrt((f:real^M->real) w + dl))) =
                (lift o sqrt o drop) o (\w. lift(f w) + lift dl)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM LIFT_ADD; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `(\h. inv(&2 * sqrt((f:real^M->real) z + dl)) % (D:real^M->real^1) h) =
                (\x. inv(&2 * sqrt(f z + dl)) % x) o (\h. D h + vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[ETA_AX; HAS_DERIVATIVE_CONST];
    MP_TAC(SPEC `(f:real^M->real) z + dl` HAS_REAL_DERIVATIVE_SQRT) THEN
    ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; GSYM LIFT_ADD]]);;

let P2BX46_SQRT_FDERIV = prove
 (`!(Fn:real^M->real) y dl.
     (\z. lift(Fn z)) differentiable at y /\ &0 < Fn y + dl
     ==> (\z. lift(sqrt(Fn z + dl))) differentiable at y /\
         !v. drop(frechet_derivative (\z. lift(sqrt(Fn z + dl))) (at y) v) =
             drop(frechet_derivative (\z. lift(Fn z)) (at y) v) / (&2 * sqrt(Fn y + dl))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Fn:real^M->real`; `frechet_derivative (\z. lift((Fn:real^M->real) z)) (at y)`;
                 `y:real^M`; `dl:real`] P2BX46_SQRT_HAS_DERIV) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[differentiable]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[DROP_CMUL] THEN GEN_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let P2BX46_CMUL_FDERIV = prove
 (`!(Fn:real^M->real) y c.
     (\z. lift(Fn z)) differentiable at y
     ==> (\z. lift(c * Fn z)) differentiable at y /\
         !v. drop(frechet_derivative (\z. lift(c * Fn z)) (at y) v) =
             c * drop(frechet_derivative (\z. lift(Fn z)) (at y) v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\z. lift(c * (Fn:real^M->real) z)) has_derivative
                 (\h. c % frechet_derivative (\z. lift(Fn z)) (at y) h)) (at y)` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[differentiable]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[DROP_CMUL]);;

let P2BX46_PHI_ARITH = prove
 (`!D P q a V k.
     &0 < P /\ &0 <= q /\ q <= P /\ &0 <= V /\ &0 < a /\ &0 <= k
     ==> (k * a * D pow 2 <= &3 * q * V
          ==> k * a * (D / (&2 * sqrt P)) pow 2 <= &3 / &4 * V) /\
         (q <= a * D pow 2 /\ P <= &2 * q
          ==> &1 <= &8 * a * (D / (&2 * sqrt P)) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(D / (&2 * sqrt P)) pow 2 = D pow 2 / (&4 * P)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * P` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `k * a * D pow 2 / (&4 * P) = (k * a * D pow 2) / (&4 * P)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `q * V <= P * V` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    SUBGOAL_THEN `&8 * a * D pow 2 / (&4 * P) = (&8 * a * D pow 2) / (&4 * P)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let P2BX46_NGRAD_POS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f p.
     p2b_shrinker (top,atlas) g f /\ p IN topspace top ==> &0 <= p2bx46_ngrad atlas g f p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `p:A`] P2BX46_GRADF_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC P2BX46_MF_POS THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)))
                    (FST(chart_at atlas p))` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* The pointwise estimate for Phi = sqrt(f o e + C0). *)

let P2BX46_NECK_PHI_PT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K eps x e y alpha1 C1 L a C0.
     p2bx46_hyp top atlas g f K /\ rfs_neck (top,atlas) g eps x e /\
     y IN rfs_neck_dom eps /\ eps <= inv(&100000) /\ &0 <= alpha1 /\ alpha1 <= inv(&100000) /\
     (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
              lricci (cylinder_flow (&0)) y w w)
          <= alpha1 * (w dot (cylinder_flow (&0) y ** w))) /\
     inv(&2) <= mfd_scalar atlas g x /\ mfd_scalar atlas g x <= &2 /\
     &0 <= C1 /\
     (!p w. p IN topspace top
            ==> abs(&2 * mfd_ricci atlas g p (p2bx46_gradf atlas g f p) w) <=
                C1 * sqrt(w dot (g p ** w))) /\
     &16000 * C1 <= L /\ &0 < L /\
     a = (&1 + (eps + &2 * alpha1) / (&1 - eps)) * mfd_scalar atlas g x /\
     &0 < mfd_scalar atlas g (e y) /\
     f(e y) + C0 = mfd_scalar atlas g (e y) + p2bx46_ngrad atlas g f (e y)
     ==> (\z. lift(sqrt(f(e z) + C0))) differentiable at y /\
         (!v. a * drop(frechet_derivative (\z. lift(sqrt(f(e z) + C0))) (at y) v) pow 2 <=
              &3 / &4 * ((v dot v) / (y dot y))) /\
         (L pow 2 <= p2bx46_ngrad atlas g f (e y) /\
          mfd_scalar atlas g (e y) <= p2bx46_ngrad atlas g f (e y)
          ==> &1 <= &8 * a *
                    drop(frechet_derivative (\z. lift(sqrt(f(e z) + C0))) (at y) y) pow 2 /\
              (!v. y dot v = &0
                   ==> &2000 * a *
                       drop(frechet_derivative (\z. lift(sqrt(f(e z) + C0))) (at y) v) pow 2
                       <= &3 / &4 * ((v dot v) / (y dot y))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `a:real`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`;
                 `alpha1:real`; `C1:real`; `L:real`; `a:real`] P2BX46_NECK_GRAD_PT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cs") (LABEL_TAC "ref")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\ &0 < eps`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET topspace top` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((f:A->real)((e:real^3->A) z))) differentiable at y` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN MATCH_MP_TAC P2BX46_PARAM_F_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p2bx46_ngrad atlas (g:A->real^3^3) f ((e:real^3->A) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_NGRAD_POS THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (f:A->real)((e:real^3->A) y) + C0 /\
                p2bx46_ngrad atlas (g:A->real^3^3) f (e y) <= f(e y) + C0 /\
                (mfd_scalar atlas g (e y) <= p2bx46_ngrad atlas g f (e y)
                 ==> f(e y) + C0 <= &2 * p2bx46_ngrad atlas g f (e y))`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `(f:A->real)((e:real^3->A) y) + C0`)) THEN
  MP_TAC(MATCH_MP (BETA_RULE(ISPECL [`\z. (f:A->real)((e:real^3->A) z)`; `y:real^3`; `C0:real`]
                                    P2BX46_SQRT_FDERIV))
           (CONJ (ASSUME `(\z. lift((f:A->real)((e:real^3->A) z))) differentiable at y`)
                 (ASSUME `&0 < (f:A->real)((e:real^3->A) y) + C0`))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> &0 < &1 + c`) THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [REWRITE_TAC[DOT_POS_LT] THEN
    MP_TAC(SPEC `eps:real` APX_NECK_DOM_NONZERO) THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `P = (f:A->real)((e:real^3->A) y) + C0` THEN
  ABBREV_TAC `q = p2bx46_ngrad atlas (g:A->real^3^3) f ((e:real^3->A) y)` THEN
  SUBGOAL_THEN `!v:real^3. &0 <= (v dot v) / ((y:real^3) dot y)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[DOT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `v:real^3` THEN
    MP_TAC(ISPECL [`drop(frechet_derivative (\z. lift((f:A->real)((e:real^3->A) z))) (at y) v)`;
                   `P:real`; `q:real`; `a:real`; `((v:real^3) dot v) / ((y:real^3) dot y)`;
                   `&1`] P2BX46_PHI_ARITH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[REAL_MUL_LID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "cs" (MP_TAC o SPEC `v:real^3`) THEN REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  STRIP_TAC THEN REMOVE_THEN "ref" MP_TAC THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`drop(frechet_derivative (\z. lift((f:A->real)((e:real^3->A) z))) (at y) y)`;
                   `P:real`; `q:real`; `a:real`; `&0`; `&0`] P2BX46_PHI_ARITH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`drop(frechet_derivative (\z. lift((f:A->real)((e:real^3->A) z))) (at y) v)`;
                   `P:real`; `q:real`; `a:real`; `((v:real^3) dot v) / ((y:real^3) dot y)`;
                   `&2000`] P2BX46_PHI_ARITH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&2000`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC]]);;

(* ========================================================================= *)
(* Euclidean tools on the neck annulus 1/3 <= |z| <= 3:                      *)
(* oscillation bounds from derivative bounds, and the constant sign of a    *)
(* nonvanishing continuous radial derivative on the connected open annulus. *)
(* ========================================================================= *)

let P2BX46_NECK_DOM_3 = prove
 (`!eps z:real^3. &0 < eps /\ eps <= inv(&10) /\ inv(&3) <= norm z /\ norm z <= &3
                  ==> z IN rfs_neck_dom eps`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) /\ sqrt(&2) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) * eps /\ sqrt(&2) * eps <= &2 * inv(&10)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&0 < &2`];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&5 <= inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * inv(&10))` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `t = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&3 < exp t` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&3)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* The derivative of z |-> Fn(rho z). *)

let P2BX46_SCALE_FDERIV = prove
 (`!(Fn:real^N->real) rho z.
     (\v. lift(Fn v)) differentiable at (rho % z)
     ==> (\v. lift(Fn(rho % v))) differentiable at z /\
         !v. frechet_derivative (\v. lift(Fn(rho % v))) (at z) v =
             frechet_derivative (\w. lift(Fn w)) (at (rho % z)) (rho % v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(\v:real^N. rho % v)` ASSUME_TAC THENL
   [REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\v:real^N. rho % v`; `\w. lift((Fn:real^N->real) w)`;
                 `\v. lift((Fn:real^N->real)(rho % v))`; `z:real^N`; `(:real^N)`]
    P2BX46_DERIV_CHAIN_LOCAL) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; DIFFERENTIABLE_LINEAR] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `frechet_derivative (\v:real^N. rho % v) (at z) = (\v. rho % v)`
  (fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR]);;

(* The oscillation on a sphere of radius rho. *)

let P2BX46_SPHERE_OSC_R = prove
 (`!(Fn:real^3->real) B rho w w'.
     &0 <= B /\ &0 < rho /\ norm w = &1 /\ norm w' = &1 /\
     (!z. norm z = rho ==> (\v. lift(Fn v)) differentiable at z) /\
     (!z v. norm z = rho /\ z dot v = &0
            ==> abs(drop(frechet_derivative (\w. lift(Fn w)) (at z) v)) <= B * norm v / rho)
     ==> abs(Fn(rho % w) - Fn(rho % w')) <= B * pi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^3. norm z = &1
                 ==> (\v. lift((Fn:real^3->real)(rho % v))) differentiable at z /\
                     !v. frechet_derivative (\v. lift(Fn(rho % v))) (at z) v =
                         frechet_derivative (\w. lift(Fn w)) (at (rho % z)) (rho % v)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2BX46_SCALE_FDERIV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`\v:real^3. (Fn:real^3->real)(rho % v)`; `B:real`; `w:real^3`;
                           `w':real^3`] P2BX46_SPHERE_OSC)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`z:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`rho % z:real^3`; `rho % v:real^3`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `B:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[NORM_MUL; DOT_LMUL; DOT_RMUL; REAL_MUL_RZERO] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < rho ==> abs rho = rho`; REAL_MUL_RID] THEN
  MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
  UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD);;

(* A two-sided bound along a ray. *)

let P2BX46_RAY_BOUND = prove
 (`!(Fn:real^3->real) w r1 r2 M.
     r1 <= r2 /\
     (!t. r1 <= t /\ t <= r2
          ==> (\z. lift(Fn z)) differentiable at (t % w) /\
              abs(drop(frechet_derivative (\z. lift(Fn z)) (at (t % w)) w)) <= M)
     ==> abs(Fn(r2 % w) - Fn(r1 % w)) <= M * (r2 - r1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (Fn:real^3->real)(s % w)`;
                 `\t. drop(frechet_derivative (\z. lift((Fn:real^3->real) z)) (at (t % w)) w)`;
                 `real_interval[r1,r2]`; `M:real`] REAL_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN MATCH_MP_TAC P2BX46_RAY_DERIV THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(MP_TAC o SPECL [`r2:real`; `r1:real`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_SIMP_TAC[REAL_ARITH `r1 <= r2 ==> abs(r2 - r1) = r2 - r1`]]);;

(* The oscillation over the annulus 1/3 <= |z| <= 3 from |dFn(z)(v)| <= Kc |v|/|z|. *)

let P2BX46_SHELL_OSC = prove
 (`!(Fn:real^3->real) Kc w0 z.
     &0 <= Kc /\ norm w0 = &1 /\ inv(&3) <= norm z /\ norm z <= &3 /\
     (!y. inv(&3) <= norm y /\ norm y <= &3
          ==> (\v. lift(Fn v)) differentiable at y /\
              !v. abs(drop(frechet_derivative (\v. lift(Fn v)) (at y) v)) <= Kc * norm v / norm y)
     ==> abs(Fn z - Fn w0) <= &10 * Kc`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `rho = norm(z:real^3)` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z = rho % (inv rho % z:real^3) /\ norm(inv rho % z:real^3) = &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                 REAL_ARITH `&0 < rho ==> abs rho = rho`; REAL_MUL_LINV];
    ALL_TAC] THEN
  ABBREV_TAC `wz = inv rho % z:real^3` THEN
  SUBGOAL_THEN `abs((Fn:real^3->real)(rho % wz) - Fn(rho % w0)) <= Kc * pi` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_SPHERE_OSC_R THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Kc:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Kc:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((Fn:real^3->real)(rho % w0) - Fn(&1 % w0)) <= (&3 * Kc) * &2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!t. inv(&3) <= t /\ t <= &3
          ==> (\z. lift((Fn:real^3->real) z)) differentiable at (t % w0) /\
              abs(drop(frechet_derivative (\z. lift(Fn z)) (at (t % w0)) w0)) <= &3 * Kc`
    ASSUME_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `norm(t % w0:real^3) = t` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t % w0:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Kc:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `w0:real^3`)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kc * &1 / t` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `Kc * &1 <= Kc * (&3 * t)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `rho <= &1` THENL
     [MP_TAC(ISPECL [`Fn:real^3->real`; `w0:real^3`; `rho:real`; `&1`; `&3 * Kc`]
        P2BX46_RAY_BOUND) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= M * &2 - M * d ==> abs(a - b) <= M * d ==> abs(b - a) <= M * &2`) THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`Fn:real^3->real`; `w0:real^3`; `&1`; `rho:real`; `&3 * Kc`]
        P2BX46_RAY_BOUND) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= M * &2 - M * d ==> abs(a - b) <= M * d ==> abs(a - b) <= M * &2`) THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN
  SUBGOAL_THEN `Kc * pi <= Kc * &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `z:real^3`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_LID]) THEN ASM_REAL_ARITH_TAC);;

(* The radial derivative z |-> dFn(z)(z) of a smooth function is continuous. *)

let P2BX46_RADIAL_DERIV_CONT = prove
 (`!(Fn:real^N->real) s.
     open s /\ smooth_map_on s (\z. lift(Fn z))
     ==> (\z. lift(drop(frechet_derivative (\v. lift(Fn v)) (at z) z))) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\z:real^N. vsum(1..dimindex(:N))
                (\i. z$i % frechet_derivative (\v. lift((Fn:real^N->real) v)) (at z) (basis i))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_VSUM_MUL THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]]);;

(* A continuous function bounded away from 0 on a connected set has a sign. *)

let P2BX46_CONNECTED_SIGN = prove
 (`!(D:real^N->real) s A.
     connected s /\ (\z. lift(D z)) continuous_on s /\ &0 < A /\
     (!z. z IN s ==> A <= abs(D z))
     ==> (!z. z IN s ==> A <= D z) \/ (!z. z IN s ==> D z <= --A)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[TAUT `p \/ q <=> ~p ==> q`; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:real^N` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `z2:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(D:real^N->real) z1 <= --A /\ A <= D z2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `z1:real^N` o check (fun th -> is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `z2:real^N` o check (fun th -> is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^N. z IN s /\ (D:real^N->real) z = &0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `is_interval(IMAGE (\z. lift((D:real^N->real) z)) s)` MP_TAC THENL
     [REWRITE_TAC[IS_INTERVAL_CONNECTED_1] THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IS_INTERVAL_1; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPECL [`lift((D:real^N->real) z1)`; `lift((D:real^N->real) z2)`;
                               `vec 0:real^1`]) THEN
    REWRITE_TAC[LIFT_DROP; DROP_VEC] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXISTS_TAC `z1:real^N` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `z2:real^N` THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
      REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th -> is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BX46_ANNULUS_CONNECTED = prove
 (`!r1 r2. connected(annulus r1 r2:real^3->bool)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[annulus] THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `r1:real`; `r2:real`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let P2BX46_SIGN_CONST = prove
 (`!(Fn:real^3->real) A.
     &0 < A /\ smooth_map_on (annulus (inv(&3)) (&3)) (\z. lift(Fn z)) /\
     (!z. z IN annulus (inv(&3)) (&3)
          ==> A <= abs(drop(frechet_derivative (\v. lift(Fn v)) (at z) z)))
     ==> (!z. z IN annulus (inv(&3)) (&3)
              ==> A <= drop(frechet_derivative (\v. lift(Fn v)) (at z) z)) \/
         (!z. z IN annulus (inv(&3)) (&3)
              ==> drop(frechet_derivative (\v. lift(Fn v)) (at z) z) <= --A)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\z:real^3. drop(frechet_derivative (\v. lift((Fn:real^3->real) v)) (at z) z)`;
     `annulus (inv(&3)) (&3):real^3->bool`; `A:real`] P2BX46_CONNECTED_SIGN)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[P2BX46_ANNULUS_CONNECTED] THEN
  MATCH_MP_TAC P2BX46_RADIAL_DERIV_CONT THEN ASM_REWRITE_TAC[OPEN_ANNULUS]);;

(* ========================================================================= *)
(* The shell lemma.  On a far eps-neck of the soliton the                    *)
(* function sg * sqrt(f o e + C0) (sg = +/-1) satisfies the shell           *)
(* hypotheses p2bx46_shell with constants A and A / 10, so its level sets   *)
(* in the neck are radial graphs (P2BX46_RADIAL_GRAPH).                      *)
(* ========================================================================= *)

(* The data of a neck far out on the soliton. *)

let p2bx46_nk = new_definition
 `p2bx46_nk (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (f:A->real)
            K C0 Rmax C1 eps alpha1 (x:A) (e:real^3->A) <=>
    p2bx46_hyp top atlas g f K /\
    (!p. p IN topspace top
         ==> &0 < mfd_scalar atlas g p /\ mfd_scalar atlas g p <= Rmax /\
             f p + C0 = mfd_scalar atlas g p + p2bx46_ngrad atlas g f p) /\
    &0 <= C1 /\
    (!p w. p IN topspace top
           ==> abs(&2 * mfd_ricci atlas g p (p2bx46_gradf atlas g f p) w) <=
               C1 * sqrt(w dot (g p ** w))) /\
    rfs_neck (top,atlas) g eps x e /\ eps <= inv(&100000) /\
    &0 <= alpha1 /\ alpha1 <= inv(&100000) /\
    (!y. y IN rfs_neck_dom eps
         ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
             <= alpha1 /\
             !w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))) /\
    inv(&2) <= mfd_scalar atlas g x /\ mfd_scalar atlas g x <= &2`;;

let P2BX46_E_LT_3 = prove
 (`exp(&1) < &3 /\ inv(&3) < inv(exp(&1))`,
  SUBGOAL_THEN `exp(&1) < &3` ASSUME_TAC THENL
   [MP_TAC E_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]);;

let P2BX46_PHI_SMOOTH = prove
 (`!s (Fo:real^N->real) C0 sg.
     open s /\ smooth_map_on s (\z. lift(Fo z)) /\ (!z. z IN s ==> &0 < Fo z + C0)
     ==> smooth_map_on s (\z. lift(sg * sqrt(Fo z + C0)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `sg:real`; `\z. lift(sqrt((Fo:real^N->real) z + C0))`]
    SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\z. lift((Fo:real^N->real) z + C0)`]
    SMOOTH_MAP_ON_LIFT_SQRT) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let P2BX46_CS_ABS = prove
 (`!a D (v:real^3) (y:real^3).
     inv(&2) <= a /\ a * D pow 2 <= &3 / &4 * ((v dot v) / (y dot y))
     ==> abs D <= &2 * norm v / norm y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(v dot v) / (y dot y) = (norm(v:real^3) / norm(y:real^3)) pow 2`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[REAL_POW_DIV; NORM_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= norm(v:real^3) / norm(y:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `t = norm(v:real^3) / norm(y:real^3)` THEN
  SUBGOAL_THEN `D pow 2 <= (&2 * t) pow 2` MP_TAC THENL
   [SUBGOAL_THEN `&0 <= D pow 2 /\ &0 <= t pow 2` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2) * D pow 2 <= a * D pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs(&2 * t) = &2 * t`]]);;

let P2BX46_TAN_ARITH = prove
 (`!a D (v:real^3) (y:real^3).
     &0 < a /\ &2000 * a * D pow 2 <= &3 / &4 * ((v dot v) / (y dot y))
     ==> abs D <= inv(sqrt(&8 * a)) / &10 * norm v / norm y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(v dot v) / (y dot y) = (norm(v:real^3) / norm(y:real^3)) pow 2`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[REAL_POW_DIV; NORM_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= norm(v:real^3) / norm(y:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `t = norm(v:real^3) / norm(y:real^3)` THEN
  SUBGOAL_THEN `&0 < sqrt(&8 * a) /\ sqrt(&8 * a) pow 2 = &8 * a` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `s = sqrt(&8 * a)` THEN
  SUBGOAL_THEN `&0 <= inv s / &10 * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs D <= abs y /\ &0 <= y ==> abs D <= y`) THEN
  ASM_REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN
  SUBGOAL_THEN `(inv s / &10 * t) pow 2 = t pow 2 / (&800 * a)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV; REAL_POW_INV] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &800 * a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= t pow 2` MP_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The constant a = (1 + c) R(x) of the neck estimates lies in [1/2, 3]. *)

let P2BX46_NK_A = prove
 (`!top atlas (g:A->real^3^3) f K C0 Rmax C1 eps alpha1 x (e:real^3->A).
     p2bx46_nk top atlas g f K C0 Rmax C1 eps alpha1 x e
     ==> inv(&2) <= (&1 + (eps + &2 * alpha1) / (&1 - eps)) * mfd_scalar atlas g x /\
         (&1 + (eps + &2 * alpha1) / (&1 - eps)) * mfd_scalar atlas g x <= &3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bx46_nk] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `alpha1:real`; `mfd_scalar atlas (g:A->real^3^3) x`; `&0`; `&1`;
                 `(eps + &2 * alpha1) / (&1 - eps)`] P2BX46_NECK_CONSTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `c = (eps + &2 * alpha1) / (&1 - eps)` THEN
  ABBREV_TAC `r = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 <= c * r /\ c * r <= inv(&20000) * &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Pointwise facts for Phi = sqrt(f o e + C0) on the annulus 1/3 <= |y| <= 3. *)

let P2BX46_NK_PHI = prove
 (`!top atlas (g:A->real^3^3) f K C0 Rmax C1 eps alpha1 x (e:real^3->A) a y.
     p2bx46_nk top atlas g f K C0 Rmax C1 eps alpha1 x e /\
     a = (&1 + (eps + &2 * alpha1) / (&1 - eps)) * mfd_scalar atlas g x /\
     inv(&3) <= norm y /\ norm y <= &3
     ==> y IN rfs_neck_dom eps /\ e y IN topspace top /\
         (\z. lift(sqrt(f(e z) + C0))) differentiable at y /\
         (!v. abs(drop(frechet_derivative (\z. lift(sqrt(f(e z) + C0))) (at y) v)) <=
              &2 * norm v / norm y) /\
         ((&16000 * C1 + &1) pow 2 <= p2bx46_ngrad atlas g f (e y) /\
          mfd_scalar atlas g (e y) <= p2bx46_ngrad atlas g f (e y)
          ==> &1 <= &8 * a *
                    drop(frechet_derivative (\z. lift(sqrt(f(e z) + C0))) (at y) y) pow 2 /\
              (!v. y dot v = &0
                   ==> &2000 * a *
                       drop(frechet_derivative (\z. lift(sqrt(f(e z) + C0))) (at y) v) pow 2
                       <= &3 / &4 * ((v dot v) / (y dot y))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                 `alpha1:real`; `x:A`; `e:real^3->A`] P2BX46_NK_A) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `a:real`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_nk]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `&0 < eps /\ mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_NECK_DOM_3 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET topspace top` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`;
                 `alpha1:real`; `C1:real`; `&16000 * C1 + &1`; `a:real`; `C0:real`]
    P2BX46_NECK_PHI_PT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `rfs_neck_dom eps`)) (concl th) &&
      can (find_term ((=) `alpha1:real`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^3` THEN
  MATCH_MP_TAC P2BX46_CS_ABS THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[]);;

(* Far out (f(x) + C0 >= (21 + M)^2), |grad f|^2 >= (1 + M)^2 - Rmax on the whole annulus. *)

let P2BX46_NK_FAR_GEN = prove
 (`!top atlas (g:A->real^3^3) f K C0 Rmax C1 eps alpha1 x (e:real^3->A) w0 z M.
     p2bx46_nk top atlas g f K C0 Rmax C1 eps alpha1 x e /\
     norm w0 = &1 /\ e w0 = x /\ &0 <= M /\
     (&21 + M) pow 2 <= f x + C0 /\
     inv(&3) <= norm z /\ norm z <= &3
     ==> (&1 + M) pow 2 - Rmax <= p2bx46_ngrad atlas g f (e z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = (&1 + (eps + &2 * alpha1) / (&1 - eps)) * mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN
   `!y. inv(&3) <= norm y /\ norm y <= &3
        ==> y IN rfs_neck_dom eps /\ (e:real^3->A) y IN topspace top /\
            (\z. lift(sqrt((f:A->real)(e z) + C0))) differentiable at y /\
            (!v. abs(drop(frechet_derivative (\z. lift(sqrt(f(e z) + C0))) (at y) v)) <=
                 &2 * norm v / norm y)`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                   `alpha1:real`; `x:A`; `e:real^3->A`; `a:real`; `y:real^3`] P2BX46_NK_PHI) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. sqrt((f:A->real)((e:real^3->A) z) + C0)`; `&2`; `w0:real^3`; `z:real^3`]
    P2BX46_SHELL_OSC) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "pt" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_nk]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  USE_THEN "pt" (MP_TAC o SPEC `z:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [USE_THEN "pt" (MP_TAC o SPEC `w0:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&21 + M <= sqrt((f:A->real) x + C0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(e:real^3->A) z` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Rmax:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `(f:A->real)((e:real^3->A) z) + C0`)) THEN
  SUBGOAL_THEN `&0 <= p2bx46_ngrad atlas (g:A->real^3^3) f ((e:real^3->A) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_NGRAD_POS THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (f:A->real)((e:real^3->A) z) + C0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + M) pow 2 <= (f:A->real)((e:real^3->A) z) + C0` MP_TAC THENL
   [MP_TAC(SPEC `(f:A->real)((e:real^3->A) z) + C0` SQRT_POW_2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Far out (f(x) + C0 large), |grad f| is large on the whole annulus. *)

let P2BX46_NK_FAR = prove
 (`!top atlas (g:A->real^3^3) f K C0 Rmax C1 eps alpha1 x (e:real^3->A) w0 z.
     p2bx46_nk top atlas g f K C0 Rmax C1 eps alpha1 x e /\
     norm w0 = &1 /\ e w0 = x /\
     (&21 + (&16000 * C1 + &1) + Rmax) pow 2 <= f x + C0 /\
     inv(&3) <= norm z /\ norm z <= &3
     ==> (&16000 * C1 + &1) pow 2 <= p2bx46_ngrad atlas g f (e z) /\
         mfd_scalar atlas g (e z) <= p2bx46_ngrad atlas g f (e z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_nk]) THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ (e:real^3->A) z IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                     `alpha1:real`; `x:A`; `e:real^3->A`;
                     `(&1 + (eps + &2 * alpha1) / (&1 - eps)) * mfd_scalar atlas (g:A->real^3^3) x`;
                     `w0:real^3`] P2BX46_NK_PHI) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                     `alpha1:real`; `x:A`; `e:real^3->A`;
                     `(&1 + (eps + &2 * alpha1) / (&1 - eps)) * mfd_scalar atlas (g:A->real^3^3) x`;
                     `z:real^3`] P2BX46_NK_PHI) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Rmax /\ mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) z) <= Rmax`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `x:A` th) THEN MP_TAC(SPEC `(e:real^3->A) z` th)) o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `Rmax:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                 `alpha1:real`; `x:A`; `e:real^3->A`; `w0:real^3`; `z:real^3`;
                 `(&16000 * C1 + &1) + Rmax`] P2BX46_NK_FAR_GEN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = &16000 * C1 + &1` THEN
  SUBGOAL_THEN `&0 <= L * Rmax /\ &0 <= L pow 2 /\ &0 <= Rmax pow 2 /\ &0 <= L`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BX46_RAD_ARITH = prove
 (`!a D. &0 < a /\ &1 <= &8 * a * D pow 2 ==> inv(sqrt(&8 * a)) <= abs D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&8 * a) /\ sqrt(&8 * a) pow 2 = &8 * a` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs y <= abs D /\ &0 <= y ==> y <= abs D`) THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_SQUARE_ABS; REAL_POW_INV] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
    SUBGOAL_THEN `&0 < &8 * a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]]);;

(* The shell lemma. *)

let P2BX46_NECK_SHELL = prove
 (`!top atlas (g:A->real^3^3) f K C0 Rmax C1 eps alpha1 x (e:real^3->A) w0.
     p2bx46_nk top atlas g f K C0 Rmax C1 eps alpha1 x e /\
     norm w0 = &1 /\ e w0 = x /\
     (&21 + (&16000 * C1 + &1) + Rmax) pow 2 <= f x + C0
     ==> ?sg A. (sg = &1 \/ sg = --(&1)) /\ &0 < A /\
                p2bx46_shell (\z. sg * sqrt(f(e z) + C0)) A (A / &10) /\
                smooth_map_on (annulus (inv(&3)) (&3)) (\z. lift(sg * sqrt(f(e z) + C0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = (&1 + (eps + &2 * alpha1) / (&1 - eps)) * mfd_scalar atlas (g:A->real^3^3) x` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                 `alpha1:real`; `x:A`; `e:real^3->A`] P2BX46_NK_A) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_nk]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  SUBGOAL_THEN
   `!y. inv(&3) <= norm y /\ norm y <= &3
        ==> (\z. lift(sqrt((f:A->real)((e:real^3->A) z) + C0))) differentiable at y /\
            &1 <= &8 * a *
                  drop(frechet_derivative (\z. lift(sqrt(f(e z) + C0))) (at y) y) pow 2 /\
            (!v. y dot v = &0
                 ==> &2000 * a *
                     drop(frechet_derivative (\z. lift(sqrt(f(e z) + C0))) (at y) v) pow 2
                     <= &3 / &4 * ((v dot v) / (y dot y))) /\
            &0 < f(e y) + C0 /\ y IN rfs_neck_dom eps`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                   `alpha1:real`; `x:A`; `e:real^3->A`; `a:real`; `y:real^3`] P2BX46_NK_PHI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                   `alpha1:real`; `x:A`; `e:real^3->A`; `w0:real^3`; `y:real^3`]
      P2BX46_NK_FAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term ((=) `&2000`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(e:real^3->A) y` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Rmax:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real`; `(e:real^3->A) y`] P2BX46_NGRAD_POS) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN annulus (inv(&3)) (&3) ==> inv(&3) <= norm z /\ norm z <= &3`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `A = inv(sqrt(&8 * a))` THEN
  SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Phi is smooth on the open annulus *)
  SUBGOAL_THEN
   `!sg. smooth_map_on (annulus (inv(&3)) (&3))
           (\z. lift(sg * sqrt((f:A->real)((e:real^3->A) z) + C0)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`annulus (inv(&3)) (&3):real^3->bool`; `\z. (f:A->real)((e:real^3->A) z)`;
                   `C0:real`; `sg:real`] P2BX46_PHI_SMOOTH) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[OPEN_ANNULUS] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `rfs_neck_dom eps` THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
        USE_THEN "pt" (MP_TAC o SPEC `z:real^3`) THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC P2BX46_PARAM_F_SMOOTH THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `g:A->real^3^3`] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
        SIMP_TAC[rfs_neck]];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      USE_THEN "pt" (MP_TAC o SPEC `z:real^3`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the sign of the radial derivative *)
  MP_TAC(ISPECL [`\z. sqrt((f:A->real)((e:real^3->A) z) + C0)`; `A:real`] P2BX46_SIGN_CONST) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_MUL_LID];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "A" THEN
      MATCH_MP_TAC P2BX46_RAD_ARITH THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "pt" (MP_TAC o SPEC `z:real^3`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the shell property for sg * Phi *)
  SUBGOAL_THEN
   `!sg. (sg = &1 \/ sg = --(&1)) /\
         (!z. z IN annulus (inv(&3)) (&3)
              ==> A <= sg * drop(frechet_derivative
                                   (\v. lift(sqrt((f:A->real)((e:real^3->A) v) + C0))) (at z) z))
         ==> p2bx46_shell (\z. sg * sqrt(f(e z) + C0)) A (A / &10)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sgn") ASSUME_TAC) THEN
    REWRITE_TAC[p2bx46_shell] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN STRIP_ASSUME_TAC P2BX46_E_LT_3 THEN
    SUBGOAL_THEN `(z:real^3) IN annulus (inv(&3)) (&3)` ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pt" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL [`\z. sqrt((f:A->real)((e:real^3->A) z) + C0)`; `z:real^3`;
                             `sg:real`] P2BX46_CMUL_FDERIV)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(sg:real) = &1` ASSUME_TAC THENL
     [USE_THEN "sgn" (DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_LID] THEN EXPAND_TAC "A" THEN
    MATCH_MP_TAC P2BX46_TAN_ARITH THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_TAC) THENL
   [MAP_EVERY EXISTS_TAC [`&1`; `A:real`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_MUL_LID];
    MAP_EVERY EXISTS_TAC [`--(&1)`; `A:real`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `--A`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The level sphere.  The radial graph sig of the level set                  *)
(* over the unit sphere, pushed into the manifold by the neck e, is a       *)
(* sphere S in the regular leaf N = {f = f x}: e o sig and z/|z| o e^-1 are *)
(* inverse diffeomorphisms between S^2 (with sphere2_atlas) and S.          *)
(* ========================================================================= *)

(* Restrictions to S^2 of smooth maps on a neighbourhood are smooth. *)

let P2BX46_SPHERE_SMOOTH_IN = prove
 (`!O (h:real^3->real^3).
     open O /\ sphere(vec 0,&1) SUBSET O /\ smooth_map_on O h
     ==> mfd_smooth_map sphere2_atlas (open_set_atlas (:real^3)) (sphere(vec 0,&1)) h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MFD_SMOOTH_MAP_INTO_EUCLIDEAN; mfd_smooth_on] THEN
  REWRITE_TAC[sphere2_atlas; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `c:(real^3->bool)#(real^3->real^2)` THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[FST; SND; STEX_SPHERE2_CHART_INV] THEN
  REWRITE_TAC[SET_RULE `!s a:real^3. (s DELETE a) INTER s = s DELETE a`;
              GBS2_STEREO2_IMAGES] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^3->bool` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; STEX_STEREO2_N_INV_SMOOTH; STEX_STEREO2_S_INV_SMOOTH] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^2` THEN
  UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET O` THEN REWRITE_TAC[SUBSET] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MESON_TAC[STEX_STEREO2_N_INV_IN; STEX_STEREO2_S_INV_IN; IN_DELETE]);;

(* The normalization map is smooth into S^2. *)

let P2BX46_SPHERE_SMOOTH_OUT = prove
 (`!W. open W /\ (!z:real^3. z IN W ==> ~(z = vec 0))
       ==> mfd_smooth_map (open_set_atlas (:real^3)) sphere2_atlas W (\z. inv(norm z) % z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^3. z IN W ==> norm(inv(norm z) % z) = &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[sphere2_atlas; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `c:(real^3->bool)#(real^3->real^2)` THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\x:real^3. stereo2_n(inv(norm x) % x)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^3 | ~(x = vec 0) /\ (inv(norm x) % x)$3 < &1}` THEN
    REWRITE_TAC[SMT_STEREO_NORMALIZED_SMOOTH; SUBSET; IN_ELIM_THM; IN_DELETE; IN_SPHERE_0] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`inv(norm z) % z:real^3`; `3`] STEX_SPHERE_COMPONENT_POLE) THEN
    MP_TAC(ISPECL [`inv(norm z) % z:real^3`; `3`] COMPONENT_LE_NORM) THEN
    ASM_SIMP_TAC[DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\x:real^3. stereo2_s(inv(norm x) % x)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^3 | ~(x = vec 0) /\ --(&1) < (inv(norm x) % x)$3}` THEN
    REWRITE_TAC[GBS2_STEREO_S_NORMALIZED_SMOOTH; SUBSET; IN_ELIM_THM; IN_DELETE; IN_SPHERE_0] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`inv(norm z) % z:real^3`; `3`] STEX_SPHERE_COMPONENT_POLE) THEN
    MP_TAC(ISPECL [`--(inv(norm z) % z):real^3`; `3`] COMPONENT_LE_NORM) THEN
    ASM_SIMP_TAC[DIMINDEX_3; ARITH; NORM_NEG; VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC]);;

(* The level sphere in a neck. *)

let P2BX46_NECK_LEVEL_SPHERE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f eps x (e:real^3->A) Fn A w0.
     smooth_manifold_atlas top atlas /\ rfs_neck (top,atlas) g eps x e /\ eps <= inv(&10) /\
     lvs_regular atlas (topspace top) f (f x) /\
     smooth_map_on (annulus (inv(&3)) (&3)) (\z. lift(Fn z)) /\
     p2bx46_shell Fn A (A / &10) /\ &0 < A /\ norm w0 = &1 /\ e w0 = x /\
     (!z. z IN annulus (inv(&3)) (&3) ==> (Fn z = Fn w0 <=> f(e z) = f x))
     ==> ?S (psi:real^3->A) psi'.
           mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                      (sphere(vec 0,&1))
                      (subtopology top (lvs_set (topspace top) f (f x)))
                      (lvs_atlas top atlas (topspace top) f (f x)) S psi psi' /\
           S SUBSET IMAGE e (annulus (inv(exp(&1))) (exp(&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps /\ mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN STRIP_ASSUME_TAC P2BX46_E_LT_3 THEN
  SUBGOAL_THEN
   `annulus (inv(exp(&1))) (exp(&1)) SUBSET (annulus (inv(&3)) (&3):real^3->bool) /\
    annulus (inv(&3)) (&3) SUBSET rfs_neck_dom eps /\
    open(annulus (inv(exp(&1))) (exp(&1)):real^3->bool) /\
    (!z:real^3. z IN annulus (inv(exp(&1))) (exp(&1)) ==> ~(z = vec 0)) /\
    (!z:real^3. inv(exp(&1)) <= norm z /\ norm z <= exp(&1) ==> z IN annulus (inv(&3)) (&3))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS; SUBSET; annulus; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC P2BX46_NECK_DOM_3 THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_REAL_ARITH_TAC;
      GEN_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Sh = annulus (inv(exp(&1))) (exp(&1)):real^3->bool` THEN
  (* the radial graph *)
  MP_TAC(ISPECL [`Fn:real^3->real`; `A:real`; `A / &10`; `annulus (inv(&3)) (&3):real^3->bool`;
                 `(Fn:real^3->real) w0`; `w0:real^3`] P2BX46_RADIAL_GRAPH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_ANNULUS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^3->bool` (X_CHOOSE_THEN `sig:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  (* the parametrization *)
  FIRST_ASSUM(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param"))
                         (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo"))
                         (concl th))) THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (e:real^3->A) Sh)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `V = IMAGE (e:real^3->A) Sh` THEN
  ABBREV_TAC `N = lvs_set (topspace top) (f:A->real) (f x)` THEN
  SUBGOAL_THEN `(N:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[lvs_set] THEN SET_TAC[]; ALL_TAC] THEN
  (* the two inverse maps *)
  SUBGOAL_THEN
   `!w:real^3. w IN sphere(vec 0,&1)
               ==> (sig:real^3->real^3) w IN Sh /\ (e:real^3->A)(sig w) IN N INTER V /\
                   (ei:A->real^3)(e(sig w)) = sig w /\ inv(norm(sig w)) % sig w = w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sig:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `sphere(vec 0:real^3,&1)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
    SUBGOAL_THEN `(sig:real^3->real^3) w IN rfs_neck_dom eps` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "N" THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `(sig:real^3->real^3) w` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `(Fn:real^3->real) w0`)) (concl th) &&
          can (find_term ((=) `(f:A->real) x`)) (concl th))) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]];
      EXPAND_TAC "V" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:A. p IN N INTER V
          ==> (ei:A->real^3) p IN Sh /\ inv(norm(ei p)) % ei p IN sphere(vec 0:real^3,&1) /\
              (e:real^3->A)((sig:real^3->real^3)(inv(norm(ei p)) % ei p)) = p`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:A` THEN REWRITE_TAC[IN_INTER] THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps /\ z IN annulus (inv(&3)) (&3)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `p:A`)) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
      ALL_TAC] THEN
    AP_TERM_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sig:real^3->real^3`)) (concl th) &&
      not(can (find_term ((=) `sphere(vec 0:real^3,&1)`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `(Fn:real^3->real) w0`)) (concl th) &&
      can (find_term ((=) `(f:A->real) x`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `(e:real^3->A) z IN N` THEN EXPAND_TAC "N" THEN
    REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* continuity *)
  SUBGOAL_THEN `(sig:real^3->real^3) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top)
                               ((e:real^3->A) o (sig:real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps):(real^3)topology` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `V SUBSET IMAGE (e:real^3->A) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!p:A. p IN V ==> (ei:A->real^3) p IN Sh` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_TAC THEN SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^3. inv(norm z) % z) continuous_on Sh` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    SIMP_TAC[SMOOTH_MAP_ON_NORMALIZE; SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology top V,subtopology euclidean (sphere(vec 0:real^3,&1)))
                   (\p:A. inv(norm((ei:A->real^3) p)) % ei p)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\p:A. inv(norm((ei:A->real^3) p)) % ei p) = (\z. inv(norm z) % z) o ei`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (Sh:real^3->bool)` THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[NORM_EQ_0]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`N INTER V:A->bool`; `(e:real^3->A) o (sig:real^3->real^3)`;
                        `\p:A. inv(norm((ei:A->real^3) p)) % ei p`] THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[INTER_SUBSET]] THEN
  REWRITE_TAC[mfd_diffeo] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `V:A->bool` THEN
    ASM_REWRITE_TAC[INTER_COMM];
    REWRITE_TAC[homeomorphic_maps; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
    REWRITE_TAC[SET_RULE `(n:A->bool) INTER (n INTER v) = n INTER v`] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    SUBGOAL_THEN `topspace top INTER (N INTER V:A->bool) = N INTER V` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN EXISTS_TAC `V:A->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]];
    (* smooth from the sphere into the leaf *)
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^3,&1))`; `sphere2_atlas`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `topspace top:A->bool`; `f:A->real`; `(f:A->real) x`;
                   `sphere(vec 0:real^3,&1)`; `(e:real^3->A) o (sig:real^3->real^3)`]
      P2BX46_LEAF_INTO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SPHERE2_ATLAS; OPEN_IN_TOPSPACE; OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN;
                SUBSET_UNIV; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^3,&1))`; `sphere2_atlas`;
                     `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `sphere(vec 0:real^3,&1)`; `rfs_neck_dom eps`;
                     `sig:real^3->real^3`; `e:real^3->A`] MFD_SMOOTH_MAP_COMPOSE) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SPHERE2_ATLAS; MFD_EUCLIDEAN_ATLAS; OPEN_IN_SUBTOPOLOGY_REFL;
                      TOPSPACE_EUCLIDEAN; SUBSET_UNIV; GSYM OPEN_IN; APX_NECK_DOM_OPEN;
                      SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
        REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P2BX46_SPHERE_SMOOTH_IN THEN EXISTS_TAC `O:real^3->bool` THEN
        ASM_REWRITE_TAC[]];
      EXPAND_TAC "N" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(ei:A->real^3)`)) (concl th) &&
        can (find_term ((=) `sphere(vec 0:real^3,&1)`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN EXPAND_TAC "N" THEN SIMP_TAC[]];
    (* smooth from the leaf onto the sphere *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `subtopology euclidean (sphere(vec 0:real^3,&1))`; `sphere2_atlas`;
                   `topspace top:A->bool`; `f:A->real`; `(f:A->real) x`; `V:A->bool`;
                   `\p:A. inv(norm((ei:A->real^3) p)) % ei p`] P2BX46_LEAF_FROM) THEN
    ASM_REWRITE_TAC[SPHERE2_ATLAS; OPEN_IN_TOPSPACE] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `(\p:A. inv(norm((ei:A->real^3) p)) % ei p) = (\z. inv(norm z) % z) o ei`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `subtopology euclidean (sphere(vec 0:real^3,&1))`; `sphere2_atlas`;
                   `V:A->bool`; `Sh:real^3->bool`;
                   `ei:A->real^3`; `\z:real^3. inv(norm z) % z`] MFD_SMOOTH_MAP_COMPOSE) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SPHERE2_ATLAS; MFD_EUCLIDEAN_ATLAS; GSYM OPEN_IN] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[NORM_EQ_0];
      MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
      EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BX46_SPHERE_SMOOTH_OUT THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The area of the level sphere.  On S the intrinsic scalar                  *)
(* curvature is >= R(x)(1 - alpha1) - C1/M - Rmax/(2 M^2) (Gauss equation,  *)
(* P2BX46_LEVEL_RN_GE, with |grad f| >= M on the neck), so the reverse      *)
(* Gauss-Bonnet inequality bounds its area.                                 *)
(* ========================================================================= *)

let P2BX46_NORMAL_GRADF = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f x.
     smooth_manifold_atlas top atlas /\ x IN topspace top
     ==> lvs_normal atlas g f x =
         inv(sqrt(p2bx46_ngrad atlas g f x)) % p2bx46_gradf atlas g f x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[lvs_normal; p2bx46_ngrad; p2bx46_gradf; p3s_cgrad] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(f:A->real) o chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) x) =
                (\y. f(chart_inv (chart_at atlas x) y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[lvs_df; jacobian; matrix; CART_EQ; LAMBDA_BETA; DIMINDEX_1; ARITH; LE_REFL; drop]);;

let P2BX46_LRICCI_SCALE2 = prove
 (`!U (G:real^N->real^N^N) y c u.
     metric_field U G /\ y IN U ==> lricci G y (c % u) (c % u) = c pow 2 * lricci G y u u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2BX46_LRIC_MATRIX_DOT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPECL [`c % u:real^N`; `c % u:real^N`] th) THEN
                       MP_TAC(SPECL [`u:real^N`; `u:real^N`] th)) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN REAL_ARITH_TAC);;

(* 2 Ric(n,n) <= C1 / M where |grad f| >= M. *)

let P2BX46_RIC_NORMAL_BOUND = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f C1 x M.
     p2b_shrinker (top,atlas) g f /\ x IN topspace top /\ &0 < M /\
     M pow 2 <= p2bx46_ngrad atlas g f x /\ &0 <= C1 /\
     (!p w. p IN topspace top
            ==> abs(&2 * mfd_ricci atlas g p (p2bx46_gradf atlas g f p) w) <=
                C1 * sqrt(w dot (g p ** w)))
     ==> &2 * mfd_ricci atlas g x (lvs_normal atlas g f x) (lvs_normal atlas g f x) <= C1 / M`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `x:A`] P2BX46_NORMAL_GRADF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x)))
                 (metric_local atlas (chart_at atlas x) (g:A->real^3^3))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_ricci] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                 `inv(sqrt(p2bx46_ngrad atlas (g:A->real^3^3) f (x:A)))`;
                 `p2bx46_gradf atlas (g:A->real^3^3) f (x:A)`] P2BX46_LRICCI_SCALE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM mfd_ricci] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `p2bx46_gradf atlas (g:A->real^3^3) f (x:A)`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `C1:real`)) (concl th))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `x:A`] P2BX46_GRADF_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `q = p2bx46_ngrad atlas (g:A->real^3^3) f (x:A)` THEN
  ABBREV_TAC `R2 = mfd_ricci atlas (g:A->real^3^3) x (p2bx46_gradf atlas g f x)
                             (p2bx46_gradf atlas g f x)` THEN
  SUBGOAL_THEN `M <= sqrt q /\ &0 < sqrt q /\ sqrt q pow 2 = q` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `M pow 2` THEN
      ASM_SIMP_TAC[REAL_POW_LT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s = sqrt q` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 * inv s pow 2 * R2 <= inv s pow 2 * (C1 * s)` MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&2 * a * r = a * (&2 * r)`] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv s pow 2 * (C1 * s) = C1 / s` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `C1 / s <= C1 / M` MP_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* The intrinsic scalar curvature on the part of the leaf inside the neck. *)

let P2BX46_NECK_RS = prove
 (`!top atlas (g:A->real^3^3) f K C0 Rmax C1 eps alpha1 x (e:real^3->A) w0 M p.
     p2bx46_nk top atlas g f K C0 Rmax C1 eps alpha1 x e /\
     norm w0 = &1 /\ e w0 = x /\ &1 + Rmax <= M /\ (&21 + M) pow 2 <= f x + C0 /\
     (!p u v. p IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g p u v) /\
     lvs_regular atlas (topspace top) f (f x) /\
     p IN lvs_set (topspace top) f (f x) INTER IMAGE e (annulus (inv(exp(&1))) (exp(&1)))
     ==> mfd_scalar atlas g x * (&1 - alpha1) - C1 / M - Rmax / (&2 * M pow 2) <=
         mfd_scalar (lvs_atlas top atlas (topspace top) f (f x))
                    (lvs_metric top atlas g (topspace top) f (f x)) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTER; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC))))))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `p:A`)) THEN
  STRIP_ASSUME_TAC P2BX46_E_PI_BOUNDS THEN STRIP_ASSUME_TAC P2BX46_E_LT_3 THEN
  SUBGOAL_THEN `inv(&3) <= norm(z:real^3) /\ norm z <= &3` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN annulus (inv(exp(&1))) (exp(&1))` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                 `alpha1:real`; `x:A`; `e:real^3->A`;
                 `(&1 + (eps + &2 * alpha1) / (&1 - eps)) * mfd_scalar atlas (g:A->real^3^3) x`;
                 `z:real^3`] P2BX46_NK_PHI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Rmax` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `(e:real^3->A) z` o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [p2bx46_nk] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bx46_nk")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                 `alpha1:real`; `x:A`; `e:real^3->A`; `w0:real^3`; `z:real^3`; `M:real`]
    P2BX46_NK_FAR_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_nk]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `&0 < eps /\ mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(e:real^3->A) z` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Rmax:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `q = p2bx46_ngrad atlas (g:A->real^3^3) f ((e:real^3->A) z)` THEN
  SUBGOAL_THEN `M pow 2 <= q /\ &0 < M /\ &0 <= Rmax` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the Gauss equation bound *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `topspace top:A->bool`; `(f:A->real) x`; `(e:real^3->A) z`;
                 `Rmax:real`] P2BX46_LEVEL_RN_GE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(f:A->real) o chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool)
                                                      ((e:real^3->A) z)) =
                    (\y. f(chart_inv (chart_at atlas (e z)) y))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      REWRITE_TAC[GSYM p2bx46_ngrad] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `M pow 2` THEN
      ASM_SIMP_TAC[REAL_POW_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->real) o chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool)
                                                  ((e:real^3->A) z)) =
                (\y. f(chart_inv (chart_at atlas (e z)) y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM p2bx46_ngrad] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= R /\ n2 <= c /\ d <= m ==> R - n2 - d <= x ==> a - c - m <= x`) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `alpha1:real`)) (concl th) &&
      can (find_term ((=) `rfs_neck_dom eps`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                   `mfd_scalar atlas (g:A->real^3^3) x`; `z:real^3`] LSCALAR_SCALE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `rfs_neck_dom eps`; `e:real^3->A`; `z:real^3`] APX_PULLBACK_SCALAR_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `abs(t - &1) <= a ==> &1 - a <= t`)) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC P2BX46_RIC_NORMAL_BOUND THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* The area bound for the level sphere. *)

let P2BX46_NECK_AREA = prove
 (`!top atlas (g:A->real^3^3) f K C0 Rmax C1 eps alpha1 x (e:real^3->A) w0 M S
    (psi:real^3->A) psi'.
     p2bx46_nk top atlas g f K C0 Rmax C1 eps alpha1 x e /\
     norm w0 = &1 /\ e w0 = x /\ &1 + Rmax <= M /\ (&21 + M) pow 2 <= f x + C0 /\
     (!p u v. p IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g p u v) /\
     lvs_regular atlas (topspace top) f (f x) /\
     mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                (sphere(vec 0,&1))
                (subtopology top (lvs_set (topspace top) f (f x)))
                (lvs_atlas top atlas (topspace top) f (f x)) S psi psi' /\
     S SUBSET IMAGE e (annulus (inv(exp(&1))) (exp(&1))) /\
     &0 < mfd_scalar atlas g x * (&1 - alpha1) - C1 / M - Rmax / (&2 * M pow 2)
     ==> ?A. mfd_has_volume (subtopology top (lvs_set (topspace top) f (f x)),
                             lvs_atlas top atlas (topspace top) f (f x))
                            (lvs_metric top atlas g (topspace top) f (f x)) S A /\
             (mfd_scalar atlas g x * (&1 - alpha1) - C1 / M - Rmax / (&2 * M pow 2)) * A <=
             &8 * pi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_nk]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN
   `hausdorff_space (subtopology top (lvs_set (topspace top) (f:A->real) (f x))) /\
    smooth_manifold_atlas (subtopology top (lvs_set (topspace top) f (f x)))
                          (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f (f x)) /\
    riemannian_metric (lvs_atlas top atlas (topspace top) f (f x))
                      (lvs_metric top atlas (g:A->real^3^3) (topspace top) f (f x))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LVS_HAUSDORFF; LVS_MANIFOLD; LVS_RIEMANNIAN; OPEN_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (f:A->real) (f x))`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f (f x)`;
                 `S:A->bool`; `psi:real^3->A`; `psi':A->real^3`] GBS2_SPHERE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (f:A->real) (f x))`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f (f x)`;
                 `lvs_metric top atlas (g:A->real^3^3) (topspace top) f (f x)`; `S:A->bool`]
    MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `A:real`) THEN
  EXISTS_TAC `A:real` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = mfd_scalar atlas (g:A->real^3^3) x * (&1 - alpha1) - C1 / M -
                  Rmax / (&2 * M pow 2)` THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (f:A->real) (f x))`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f (f x)`;
                 `lvs_metric top atlas (g:A->real^3^3) (topspace top) f (f x)`; `S:A->bool`;
                 `psi:real^3->A`; `psi':A->real^3`; `k / &2`; `A:real`]
    P2BX46_GB_SPHERE_AREA_REV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ARITH `&2 * k / &2 = k`] THEN EXPAND_TAC "k" THEN
    MATCH_MP_TAC P2BX46_NECK_RS THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `C0:real`; `eps:real`; `e:real^3->A`; `w0:real^3`] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(S:A->bool) SUBSET topspace (subtopology top (lvs_set (topspace top) f (f x)))` THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Distances for the far necks.  The cylinder models of                      *)
(* p2b_cyl_model are complete at time 0 (via the standard models of         *)
(* pc_p2a_cylm and the length lower bound P2ACM_STD_CURVE_LOWER), distances *)
(* only see the metric on topspace, and points at bounded distance from a   *)
(* sequence going to infinity have f -> infinity (f proper).                 *)
(* ========================================================================= *)

(* Continuity is local. *)

let P2BX46_LOCAL_CONT = prove
 (`!(q:real^N->A) s top.
     open s /\ IMAGE q s SUBSET topspace top /\
     (!y. y IN s ==> ?t. open t /\ y IN t /\ t SUBSET s /\
                         continuous_map (subtopology euclidean t,top) q)
     ==> continuous_map (subtopology euclidean s,top) q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN
  ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x:real^N | x IN t /\ (q:real^N->A) x IN u}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [continuous_map] o
      check (fun th -> can (find_term ((=) `t:real^N->bool`)) (concl th) &&
                       is_comb(concl th))) THEN
    DISCH_THEN(MP_TAC o SPEC `u:A->bool`) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ASM SET_TAC[]]);;

(* The cylinder models are complete at time 0. *)

let P2BX46_CYL_COMPLETE = prove
 (`!top atlas (g:real->B->real^3^3).
     p2b_cyl_model (top,atlas) g /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas (g(&0))
     ==> mfd_complete (top,atlas) (g(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) o REWRITE_RULE[p2b_cyl_model]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(&0)`; `p:real^3->B`; `lam:real`; `&0`] P2ACM_CYL_STD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `y:real^3`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfs_pullback" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN(X_CHOOSE_TAC `q:real^3->B`) THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o GEN_REWRITE_RULE I [p2acm_std]) THEN
  (* q is continuous on real^3 minus 0 *)
  SUBGOAL_THEN `continuous_map (subtopology euclidean {y:real^3 | ~(y = vec 0)},top)
                               (q:real^3->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_LOCAL_CONT THEN ASM_REWRITE_TAC[OPEN_NONZERO; SUBSET_REFL] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_param" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(y:real^3,r)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; dist] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_SUB_RZERO]) THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
        check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "mfd_param"
                                                 with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_complete] THEN MAP_EVERY X_GEN_TAC [`x:B`; `r:real`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(&0)`; `q:real^3->B`; `lam:real`; `x:B`]
    P2ACM_STD_PREIM) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z0 = @z:real^3. ~(z = vec 0) /\ (q:real^3->B) z = x` THEN STRIP_TAC THEN
  ABBREV_TAC `S = abs(apx_sval(z0:real^3)) + (abs r + &1) / sqrt lam` THEN
  SUBGOAL_THEN `&0 <= S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `IMAGE (q:real^3->B)
                (cball(vec 0:real^3,exp(S / sqrt(&2))) DIFF ball(vec 0,exp(--(S / sqrt(&2)))))` THEN
  ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean {z:real^3 | ~(z = vec 0)}` THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_BALL_0] THEN X_GEN_TAC `z:real^3` THEN
        STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN
        MP_TAC(SPEC `--(S / sqrt(&2))` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM; IN_IMAGE; IN_DIFF; IN_BALL_0; IN_CBALL_0] THEN
  X_GEN_TAC `y:B` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(&0)`; `q:real^3->B`; `lam:real`; `y:B`]
    P2ACM_STD_PREIM) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z1 = @z:real^3. ~(z = vec 0) /\ (q:real^3->B) z = y` THEN STRIP_TAC THEN
  EXISTS_TAC `z1:real^3` THEN ASM_REWRITE_TAC[] THEN
  (* a curve of length < d + 1 *)
  SUBGOAL_THEN
   `?gam. mfd_c1_curve (top,atlas) gam (&0) (&1) /\ gam(&0) = (x:B) /\ gam(&1) = y /\
          mfd_length atlas ((g:real->B->real^3^3)(&0)) gam (&0) (&1) < abs r + &1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{mfd_length atlas ((g:real->B->real^3^3)(&0)) gam (&0) (&1) | gam |
                     mfd_c1_curve (top,atlas) gam (&0) (&1) /\ gam(&0) = (x:B) /\ gam(&1) = y}`;
                   `abs r + &1`] INF_APPROACH) THEN
    REWRITE_TAC[GSYM mfd_dist] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        UNDISCH_TAC `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (x:B) y` THEN REWRITE_TAC[mfd_joinable] THEN
        MESON_TAC[];
        EXISTS_TAC `&0` THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_LENGTH_POS_LE THEN
        EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(&0)`; `q:real^3->B`; `lam:real`; `gam:real->B`;
                 `z0:real^3`; `z1:real^3`] P2ACM_STD_CURVE_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(apx_sval(z1:real^3)) <= S` MP_TAC THENL
   [EXPAND_TAC "S" THEN
    SUBGOAL_THEN `&0 < sqrt lam` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `abs(abs(apx_sval(z1:real^3)) - abs(apx_sval(z0:real^3))) <=
                  (abs r + &1) / sqrt lam` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LT] THEN
  ASM_SIMP_TAC[apx_sval; APX_EXP_LT_NORM] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 < x ==> --(S / x) = (--S) / x`] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  REAL_ARITH_TAC);;

(* Lengths and distances only see the metric on topspace. *)

let P2BX46_LENGTH_CONG = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (G1:A->real^N^N) G2 gamma a b.
     (!x. x IN topspace top ==> G1 x = G2 x) /\ mfd_c1_curve (top,atlas) gamma a b
     ==> mfd_length atlas G1 gamma a b = mfd_length atlas G2 gamma a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_length] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_speed] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` (fun th -> ASM_SIMP_TAC[th]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o CONJUNCT1 o
    CONJUNCT2 o GEN_REWRITE_RULE I [mfd_c1_curve]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2BX46_DIST_CONG = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (G1:A->real^N^N) G2 x y.
     (!z. z IN topspace top ==> G1 z = G2 z)
     ==> mfd_dist (top,atlas) G1 x y = mfd_dist (top,atlas) G2 x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `l:real` THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gam:real->A` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BX46_LENGTH_CONG THEN EXISTS_TAC `top:A topology` THEN
  ASM_MESON_TAC[]);;

(* Points within bounded distance of a sequence going to infinity have      *)
(* f -> infinity, for f with compact sublevel sets.                          *)

let P2BX46_FAR_ESCAPE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real) (a:num->A) b D.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ connected_space top /\
     (!c. compact_in top {x | x IN topspace top /\ f x <= c}) /\
     (!k. a k IN topspace top) /\ (?k1. !k. k1 <= k ==> b k IN topspace top) /\
     (!S. compact_in top S ==> ?N. !k. N <= k ==> ~(a k IN S)) /\
     (?k0. !k. k0 <= k ==> mfd_dist (top,atlas) g (a k) (b k) <= D)
     ==> !V. ?N. !k. N <= k ==> V < f(b k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `k1:num`)
   (CONJUNCTS_THEN2 (LABEL_TAC "esc") (X_CHOOSE_TAC `k0:num`))))))))) THEN
  X_GEN_TAC `V:real` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `(a:num->A) 0`; `{x:A | x IN topspace top /\ f x <= V}`]
    LIM_COMPACT_DIST_BOUND) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `D1:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "esc" (MP_TAC o SPEC `top closure_of (mfd_ball (top,atlas) (g:A->real^N^N) ((a:num->A) 0)
                                                 (D1 + D + &1))`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC P2BX46_BALL_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN EXISTS_TAC `N1 + k0 + k1:num` THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(b:num->A) k IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `top closure_of
       mfd_ball (top,atlas) (g:A->real^N^N) ((a:num->A) 0) (D1 + D + &1)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `!s t (x:A). x IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) ((a:num->A) 0) (D1 + D + &1)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]] THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
  SUBGOAL_THEN `!u v:A. u IN topspace top /\ v IN topspace top
                       ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) u v`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_CONNECTED]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(b:num->A) k` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `D1:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `D:real`)) (concl th) && not(can (find_term ((=) `D1:real`)) (concl th)))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `(a:num->A) 0`; `(b:num->A) k`; `(a:num->A) k`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `(a:num->A) k`; `(b:num->A) k`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Far necks.  From the cylinder limit of the soliton flow at points pp k    *)
(* going to infinity with R(pp k) -> 1 (X2s, in the form with points         *)
(* realizing the limsup of R): for every eps <= 1/2, s1 > 0 and V there is   *)
(* an eps-neck of g centred at x with |R(x) - 1| <= s1 and f(x) >= V (model  *)
(* neck, P2BSK_LIMIT_NECK, LIM_CURV, LIM_DIST, P2BX46_FAR_ESCAPE).           *)
(* ========================================================================= *)

let P2BX46_CYL_CONNECTED = prove
 (`!top atlas (g:real->B->real^3^3).
     p2b_cyl_model (top,atlas) g ==> connected_space top`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) o REWRITE_RULE[p2b_cyl_model]) THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean {y:real^3 | ~(y = vec 0)},top)
                               (p:real^3->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_LOCAL_CONT THEN ASM_REWRITE_TAC[OPEN_NONZERO; SUBSET_REFL] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_param" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(y:real^3,r)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; dist] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_SUB_RZERO]) THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
        check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "mfd_param"
                                                 with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CONNECTED_IN_TOPSPACE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `topspace (top:B topology)`)) THEN
  MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
  EXISTS_TAC `subtopology euclidean {y:real^3 | ~(y = vec 0)}` THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN; SUBSET_REFL] THEN
  SUBGOAL_THEN `{y:real^3 | ~(y = vec 0)} = (:real^3) DIFF {vec 0}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_PUNCTURED_UNIVERSE THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC);;

(* The scalar curvature only sees the metric on topspace. *)

let P2BX46_SCALAR_CONG = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (G1:A->real^N^N) G2 z.
     smooth_manifold_atlas top atlas /\ (!x. x IN topspace top ==> G1 x = G2 x) /\
     z IN topspace top
     ==> mfd_scalar atlas G1 z = mfd_scalar atlas G2 z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_scalar] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `G1:A->real^N^N`; `G2:A->real^N^N`; `topspace top:A->bool`; `z:A`]
    P2B9S_METRIC_LOCAL_EQ_ON) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let P2BX46_PROD_CLOSE = prove
 (`!r Q s1. &0 < Q /\ Q <= &2 /\ abs(r - &1) < s1 / &4 /\ abs(Q - &1) < s1 / &4
            ==> abs(r * Q - &1) <= s1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(r - &1) * Q <= s1 / &4 * &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(r * Q - &1) <= abs(r - &1) * Q + abs(Q - &1)` MP_TAC THENL
   [SUBGOAL_THEN `r * Q - &1 = (r - &1) * Q + (Q - &1)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `abs a = b ==> abs(a + c) <= b + abs c`) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < Q ==> abs Q = Q`];
    ASM_REAL_ARITH_TAC]);;

(* The far necks. *)

let P2BX46_FAR_NECKS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K (pp:num->A) sub
    (top':A topology) atlas' g' xl W phi.
     p2bx46_hyp top atlas g f K /\
     (!k. pp k IN topspace top) /\
     (!S. compact_in top S ==> ?N. !k. N <= k ==> ~(pp k IN S)) /\
     ((\k. mfd_scalar atlas g (pp k)) ---> &1) sequentially /\
     p3_subseq sub /\
     p2c_flow_limit_with
       (\k. rfs_flow_view (top,atlas) {t | t < &0} (p2bx46_G top atlas g f))
       (pp o sub) (\k. --(&1))
       (\k. mfd_scalar atlas (p2bx46_G top atlas g f (--(&1))) (pp(sub k)))
       {s | s <= &0} (top',atlas') g' xl W phi /\
     mfd_scalar atlas' (g'(&0)) xl = &1 /\
     (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
     p2b_cyl_model (top',atlas') g'
     ==> !eps s1 V. &0 < eps /\ eps <= &1 / &2 /\ &0 < s1
                    ==> ?x e. rfs_neck (top,atlas) g eps x e /\
                              abs(mfd_scalar atlas g x - &1) <= s1 /\ V <= f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  ABBREV_TAC `G = p2bx46_G top atlas (g:A->real^3^3) f` THEN
  ABBREV_TAC `V0 = \k:num. rfs_flow_view (top,atlas) {t | t < &0} (G:real->A->real^3^3)` THEN
  (* the limit data *)
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "p2c_flow_limit_with"
                                              with Failure _ -> false)) (concl th))) THEN
  MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                 `g':real->A->real^3^3`; `xl:A`] P2BX46_CYL_LIMIT_R) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->A->real^3^3)(&0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "riemannian_metric"
                               with Failure _ -> false)) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the views *)
  SUBGOAL_THEN
   `!n tau. ~(topspace(rfs_vtop ((V0:num->(real->A topology)#
                                    (real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) tau) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V0 n) tau) (rfs_vatlas (V0 n) tau) /\
                riemannian_metric (rfs_vatlas (V0 n) tau) (rfs_vmetric (V0 n) tau)`
  ASSUME_TAC THENL
   [EXPAND_TAC "V0" THEN REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN COND_CASES_TAC THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    EXPAND_TAC "G" THEN MATCH_MP_TAC P2BX46_SOL_RIEM THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. rfs_vtop ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) k) (--(&1)) = top /\
        rfs_vatlas (V0 k) (--(&1)) = atlas /\ rfs_vmetric (V0 k) (--(&1)) = G(--(&1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "V0" THEN REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> (G:real->A->real^3^3) (--(&1)) x = g x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "G" THEN
    MATCH_MP_TAC P2BX46_G_M1 THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a neck in the model, and in the soliton *)
  MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                 `g':real->A->real^3^3`; `eps:real`] P2BSK_MODEL_NECK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xn:A` (X_CHOOSE_THEN `en:real^3->A` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `(pp:num->A) o (sub:num->num)`; `\k:num. --(&1)`;
                 `\k. mfd_scalar atlas ((G:real->A->real^3^3)(--(&1))) ((pp:num->A)((sub:num->num) k))`;
                 `{s:real | s <= &0}`; `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                 `g':real->A->real^3^3`; `xl:A`; `W:num->A->bool`; `phi:num->A->A`;
                 `eps:real`; `xn:A`; `en:real^3->A`] P2BSK_LIMIT_NECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
    UNDISCH_TAC `p2c_flow_limit_with
       (\k. rfs_flow_view (top,atlas) {t | t < &0} (p2bx46_G top atlas (g:A->real^3^3) f))
       ((pp:num->A) o (sub:num->num)) (\k. --(&1))
       (\k. mfd_scalar atlas (p2bx46_G top atlas g f (--(&1))) (pp(sub k)))
       {s | s <= &0} (top',atlas') (g':real->A->real^3^3) xl W phi` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  SUBGOAL_THEN `!k. N1 <= k ==> rfs_neck (top,atlas) (g:A->real^3^3) eps
                                         ((phi:num->A->A) k xn) (phi k o en) /\
                                (phi k xn) IN topspace top`
  (LABEL_TAC "nk") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N1:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX46_NECK_CONG THEN EXISTS_TAC `(G:real->A->real^3^3)(--(&1))` THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `(phi:num->A->A) k o (en:real^3->A)`;
                     `sphere(vec 0:real^3,&1)`] MFD_PARAM_IMAGE_SUBSET) THEN
      ASM_SIMP_TAC[APX_UNIT_SPHERE_NECK_DOM] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* R at the neck centres tends to 1 *)
  SUBGOAL_THEN `(xn:A) IN topspace top'` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top',atlas') ((g':real->A->real^3^3)(&0)) eps xn en` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `en:real^3->A`; `sphere(vec 0:real^3,&1)`]
      MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_SIMP_TAC[APX_UNIT_SPHERE_NECK_DOM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = \k. mfd_scalar atlas ((G:real->A->real^3^3)(--(&1))) ((pp:num->A)((sub:num->num) k))` THEN
  SUBGOAL_THEN `((Q:num->real) ---> &1) sequentially` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `mfd_scalar atlas (g:A->real^3^3)`; `pp:num->A`; `&1`;
                   `sub:num->num`] P2BX46_SUBSEQ_POINTS) THEN
    ASM_REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\k. mfd_scalar atlas (g:A->real^3^3) ((pp:num->A)((sub:num->num) k))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `k:num` THEN
    EXPAND_TAC "Q" THEN REWRITE_TAC[] THEN MATCH_MP_TAC P2BX46_SCALAR_CONG THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. &0 < (Q:num->real) k` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Q:num->real`)) (concl th) &&
      can (find_term ((=) `&0 < (Q:num->real) k`)) (concl th)));
    ALL_TAC] THEN
  (* LIM_CURV: R(phi k xn) / Q k -> 1 *)
  MP_TAC(ISPECL [`(:A)`; `(:A)`] LIM_CURV) THEN REWRITE_TAC[LIM_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `(pp:num->A) o (sub:num->num)`; `\k:num. --(&1)`; `Q:num->real`; `{s:real | s <= &0}`;
    `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':real->A->real^3^3`;
    `xl:A`; `W:num->A->bool`; `phi:num->A->A`; `&0`; `xn:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[REAL_ARITH `&0 / x = &0`; REAL_ADD_RID] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_REFL; REAL_SUB_RZERO; REAL_DIV_1] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `s1 / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N2:num`)] THEN
  UNDISCH_TAC `((Q:num->real) ---> &1) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `min (s1 / &4) (&3 / &4)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N3:num`)] THEN
  (* LIM_DIST: phi k xn stays at bounded distance from pp(sub k) *)
  SUBGOAL_THEN `connected_space (top':A topology) /\
                mfd_complete (top',atlas') ((g':real->A->real^3^3)(&0)) /\
                compact_in top' {xl:A, xn}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BX46_CYL_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`atlas':((A->bool)#(A->real^3))->bool`; `g':real->A->real^3^3`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BX46_CYL_COMPLETE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:A)`; `(:A)`] LIM_DIST) THEN REWRITE_TAC[LIM_DIST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `(pp:num->A) o (sub:num->num)`; `\k:num. --(&1)`; `Q:num->real`; `{s:real | s <= &0}`;
    `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':real->A->real^3^3`;
    `xl:A`; `W:num->A->bool`; `phi:num->A->A`; `&0`; `{xl:A, xn}`; `&1`]) THEN
  REWRITE_TAC[REAL_ARITH `&0 / x = &0`; REAL_ADD_RID] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL; REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "ld")) THEN
  SUBGOAL_THEN `!S. compact_in top S ==> ?N. !k. N <= k ==> ~(((pp:num->A) o (sub:num->num)) k IN S)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `mfd_scalar atlas (g:A->real^3^3)`; `pp:num->A`; `&1`;
                   `sub:num->num`] P2BX46_SUBSEQ_POINTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `(pp:num->A) o (sub:num->num)`; `\k. (phi:num->A->A) k xn`;
                 `&2 * (mfd_dist (top',atlas') ((g':real->A->real^3^3)(&0)) xl xn + &1)`]
    P2BX46_FAR_ESCAPE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real`; `K:real`] P2BX46_F_PROPER) THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `N1:num` THEN ASM_SIMP_TAC[];
      EXISTS_TAC `k0 + N3:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      USE_THEN "ld" (MP_TAC o SPECL [`k:num`; `xl:A`; `xn:A`]) THEN
      ANTS_TAC THENL [REWRITE_TAC[IN_INSERT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) ((pp:num->A)((sub:num->num) k))
                              ((phi:num->A->A) k xn) =
                    mfd_dist (top,atlas) ((G:real->A->real^3^3)(--(&1))) (pp(sub k)) (phi k xn)`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX46_DIST_CONG THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) ((G:real->A->real^3^3)(--(&1)))
                            ((pp:num->A)((sub:num->num) k)) ((phi:num->A->A) k xn)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "G" THEN MATCH_MP_TAC P2BX46_SOL_RIEM THEN EXISTS_TAC `K:real` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(&2) <= sqrt((Q:num->real) k)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `N3:num`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ABBREV_TAC `dd = mfd_dist (top,atlas) ((G:real->A->real^3^3)(--(&1)))
                        ((pp:num->A)((sub:num->num) k)) ((phi:num->A->A) k xn)` THEN
      SUBGOAL_THEN `inv(&2) * dd <= sqrt((Q:num->real) k) * dd` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o BETA_RULE o SPEC `V:real`) THEN DISCH_THEN(X_CHOOSE_TAC `N4:num`)] THEN
  (* the choice of k *)
  ABBREV_TAC `k = N1 + N2 + N3 + N4:num` THEN
  MAP_EVERY EXISTS_TAC [`(phi:num->A->A) k xn`; `(phi:num->A->A) k o (en:real^3->A)`] THEN
  USE_THEN "nk" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N4:num`)) (concl th))) THEN
    EXPAND_TAC "k" THEN ARITH_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((phi:num->A->A) k xn) =
                (mfd_scalar atlas ((G:real->A->real^3^3)(--(&1))) (phi k xn) / Q k) * Q k`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `~((Q:num->real) k = &0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL] THEN MATCH_MP_TAC P2BX46_SCALAR_CONG THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BX46_PROD_CLOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N3:num`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N2:num`)) (concl th))) THEN
  ANTS_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The output of this unit.  For every delta > 0 and V0 there is             *)
(* a level v >= V0 of f containing a sphere S (diffeomorphic to S^2 in the  *)
(* leaf) of area at most 8 pi + delta: a far eps-neck with R(x) close to 1, *)
(* the shell lemma, the level sphere and the reverse Gauss-Bonnet bound.    *)
(* ========================================================================= *)

let P2BX46_K_ARITH = prove
 (`!r alpha C1 M Rmax t.
     &0 < t /\ t <= &1 /\ abs(r - &1) <= t / &4 /\ &0 <= alpha /\ alpha <= t / &4 /\
     &0 <= C1 /\ &0 <= Rmax /\ &1 <= M /\ &4 * C1 <= t * M /\ &2 * Rmax <= t * M
     ==> &1 - t <= r * (&1 - alpha) - C1 / M - Rmax / (&2 * M pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C1 / M <= t / &4` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Rmax / (&2 * M pow 2) <= t / &4` ASSUME_TAC THENL
   [SUBGOAL_THEN `M <= M pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 * M pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `t * M <= t * M pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t / &4) * (&1 - t / &4) <= r * (&1 - alpha)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t * t` MP_TAC THENL [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BX46_AREA_ARITH = prove
 (`!delta A k. &0 < delta /\ &0 <= A /\ &1 - delta / (&8 * pi + delta) <= k /\
               k * A <= &8 * pi
               ==> A <= &8 * pi + delta`,
  REPEAT STRIP_TAC THEN MP_TAC PI_POS THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &8 * pi + delta` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - delta / (&8 * pi + delta) = (&8 * pi) / (&8 * pi + delta)` SUBST_ALL_TAC
  THENL [UNDISCH_TAC `&0 < &8 * pi + delta` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(&8 * pi) / (&8 * pi + delta) * A <= k * A` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(&8 * pi) * A <= (&8 * pi) * (&8 * pi + delta)` MP_TAC THENL
   [SUBGOAL_THEN `(&8 * pi) / (&8 * pi + delta) * A <= &8 * pi` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(a / b) * c = (a * c) / b`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &8 * pi` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ]);;

(* The output of this unit. *)

let P2BX46_I_OUTPUT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f K C0 Rmax C1.
     p2bx46_hyp top atlas g f K /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v) /\
     (!p. p IN topspace top
          ==> &0 < mfd_scalar atlas g p /\ mfd_scalar atlas g p <= Rmax /\
              f p + C0 = mfd_scalar atlas g p + p2bx46_ngrad atlas g f p) /\
     &0 <= C1 /\
     (!p w. p IN topspace top
            ==> abs(&2 * mfd_ricci atlas g p (p2bx46_gradf atlas g f p) w) <=
                C1 * sqrt(w dot (g p ** w))) /\
     (!eps s1 V. &0 < eps /\ eps <= &1 / &2 /\ &0 < s1
                 ==> ?x e. rfs_neck (top,atlas) g eps x e /\
                           abs(mfd_scalar atlas g x - &1) <= s1 /\ V <= f x)
     ==> !delta V0. &0 < delta
                    ==> ?v S (psi:real^3->A) psi' A.
                          V0 <= v /\
                          mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1)))
                                     sphere2_atlas (sphere(vec 0,&1))
                                     (subtopology top (lvs_set (topspace top) f v))
                                     (lvs_atlas top atlas (topspace top) f v) S psi psi' /\
                          mfd_has_volume (subtopology top (lvs_set (topspace top) f v),
                                          lvs_atlas top atlas (topspace top) f v)
                                         (lvs_metric top atlas g (topspace top) f v) S A /\
                          A <= &8 * pi + delta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`delta:real`; `V0:real`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bx46_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC PI_POS THEN DISCH_TAC THEN
  ABBREV_TAC `t = delta / (&8 * pi + delta)` THEN
  SUBGOAL_THEN `&0 < t /\ t < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    SUBGOAL_THEN `&0 < &8 * pi + delta` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `alpha = min (t / &4) (inv(&100000))` THEN
  SUBGOAL_THEN `&0 < alpha /\ alpha <= t / &4 /\ alpha <= inv(&100000)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "alpha" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[APX_NECK_CURV_STATEMENT] (ISPEC `(:A)` APX_NECK_CURV)) THEN
  DISCH_THEN(MP_TAC o SPEC `alpha:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv"))) THEN
  ABBREV_TAC `eps = min eps1 (inv(&100000))` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= eps1 /\ eps <= inv(&100000) /\ eps <= &1 / &2 /\
                eps <= inv(&10)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `M = &16000 * C1 + &1 + Rmax + &4 * (C1 / t) + &2 * (Rmax / t) + &1` THEN
  (* the neck *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`eps:real`; `t / &4`; `max V0 ((&21 + M) pow 2 - C0)`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfs_neck" with Failure _ -> false))
          (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?w0:real^3. norm w0 = &1 /\ e w0 = (x:A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE; IN_SPHERE_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `x:A`)) THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET topspace top` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Rmax` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Rmax:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + Rmax <= M /\ &16000 * C1 + &1 + Rmax <= M /\ &1 <= M /\
                &4 * C1 <= t * M /\ &2 * Rmax <= t * M` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= C1 / t /\ &0 <= Rmax / t` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&4 * (C1 / t) <= M /\ &2 * (Rmax / t) <= M` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `t * (&4 * (C1 / t)) <= t * M` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
      UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `t * (&2 * (Rmax / t)) <= t * M` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
      UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* the neck data *)
  SUBGOAL_THEN `p2bx46_nk top atlas g f K C0 Rmax C1 eps alpha (x:A) (e:real^3->A)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bx46_nk] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "curv" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                                    `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&21 + M) pow 2 <= (f:A->real) x + C0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the shell *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                 `alpha:real`; `x:A`; `e:real^3->A`; `w0:real^3`] P2BX46_NECK_SHELL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&21 + M) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` (X_CHOOSE_THEN `A0:real`
    (CONJUNCTS_THEN2 (LABEL_TAC "sgn") STRIP_ASSUME_TAC))) THEN
  (* the level of x is regular *)
  SUBGOAL_THEN `lvs_regular atlas (topspace top) (f:A->real) (f x)` ASSUME_TAC THENL
   [MATCH_MP_TAC LVS_REGULAR_GRAD2 THEN EXISTS_TAC `g:A->real^3^3` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:A` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:A->real) o chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) p) =
                  (\y. f(chart_inv (chart_at atlas p) y))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM p2bx46_ngrad] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Rmax:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&21 + M <= (&21 + M) pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the level sphere *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `eps:real`; `x:A`; `e:real^3->A`;
                 `\z. sg * sqrt((f:A->real)((e:real^3->A) z) + C0)`; `A0:real`; `w0:real^3`]
    P2BX46_NECK_LEVEL_SPHERE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(sg = &0)` ASSUME_TAC THENL
     [USE_THEN "sgn" (DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_EQ_MUL_LCANCEL; SQRT_INJ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `psi:real^3->A`
    (X_CHOOSE_THEN `psi':A->real^3` STRIP_ASSUME_TAC))) THEN
  (* the area *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `K:real`; `C0:real`; `Rmax:real`; `C1:real`; `eps:real`;
                 `alpha:real`; `x:A`; `e:real^3->A`; `w0:real^3`; `M:real`; `S:A->bool`;
                 `psi:real^3->A`; `psi':A->real^3`] P2BX46_NECK_AREA) THEN
  SUBGOAL_THEN `&1 - t <= mfd_scalar atlas (g:A->real^3^3) x * (&1 - alpha) - C1 / M -
                          Rmax / (&2 * M pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX46_K_ARITH THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(f:A->real) x`; `S:A->bool`; `psi:real^3->A`; `psi':A->real^3`;
                        `A:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2BX46_AREA_ARITH THEN
  EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) x * (&1 - alpha) - C1 / M -
              Rmax / (&2 * M pow 2)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set (topspace top) (f:A->real) (f x))`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) (topspace top) f (f x)`;
                 `lvs_metric top atlas (g:A->real^3^3) (topspace top) f (f x)`;
                 `S:A->bool`; `A:real`] MFD_HAS_VOLUME_POS_LE) THEN
  ASM_SIMP_TAC[LVS_MANIFOLD; LVS_RIEMANNIAN; OPEN_IN_TOPSPACE]);;

