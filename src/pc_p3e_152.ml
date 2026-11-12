(* ========================================================================= *)
(* Unit pc_p3e_152: MT Prop 15.2 (p. 353), gluing an evolving beta eps-neck  *)
(* with a strong beta eps/2-neck at the earlier time, for the statement      *)
(* P3_PROP_15_2_STATEMENT (!eps ?beta: beta depends on eps, since MT's proof *)
(* by contradiction works for a fixed eps; MT fixes beta after eps in Sec    *)
(* 15.1.1).  First an abstract core on Euclidean annuli (p3e_gdata: the      *)
(* rescaled families of the two necks, the transition map psi, the junction  *)
(* identity, continuity at the junction and the evolution of the scalar      *)
(* curvature at the centre), proved by contradiction with sequences          *)
(* (pc_p3e_cylrig, pc_p3e_mapcpt).  Main theorem: P3E_GLUE_CORE.  The        *)
(* translation to histories and P3E_PROP_15_2 are in unit pc_p3e_152h.       *)
(* ========================================================================= *)

needs "src/pc_p3e_mapcpt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Orders and domains along sequences of necks with beta n -> 0              *)
(* (rfs_kreg (beta n eps) -> infinity, rfs_neck_dom (beta n eps) eventually *)
(* contains every closed ball avoiding the origin).                          *)
(* ------------------------------------------------------------------------- *)

let P3E_KREG_TENDSTO = prove
 (`!eps betas.
     &0 < eps /\ (!n. &0 < betas n) /\ ((\n. lift(betas n)) --> vec 0) sequentially
     ==> !m. ?N. !n. N <= n ==> m <= rfs_kreg (betas n * eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m:num` THEN
  UNDISCH_TAC `((\n. lift(betas n)) --> vec 0) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0; NORM_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `inv((&m + &1) * eps)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (betas:num->real) n * eps` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&m + &1 <= inv((betas:num->real) n * eps)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(betas:num->real) n * eps <= inv(&m + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv((&m + &1) * eps) * eps` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN
        UNDISCH_TAC `abs((betas:num->real) n) < inv((&m + &1) * eps)` THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[REAL_INV_MUL] THEN
        SUBGOAL_THEN `~(eps = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `(betas:num->real) n * eps` RFS_KREG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MP_TAC(SPEC `inv((betas:num->real) n * eps)` FLOOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&m < &(rfs_kreg ((betas:num->real) n * eps)) + &1` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC);;

let P3E_NECK_DOM_EVENTUALLY = prove
 (`!eps betas (z0:real^3) r.
     &0 < eps /\ (!n. &0 < betas n) /\ ((\n. lift(betas n)) --> vec 0) sequentially /\
     &0 <= r /\ r < norm z0
     ==> ?N. !n. N <= n ==> cball(z0,r) SUBSET rfs_neck_dom (betas n * eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L0 = abs(log(norm(z0:real^3) - r)) + abs(log(norm z0 + r)) + &1` THEN
  SUBGOAL_THEN `&1 <= L0` ASSUME_TAC THENL
   [EXPAND_TAC "L0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) * eps * L0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `((\n. lift(betas n)) --> vec 0) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0; NORM_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(sqrt(&2) * eps * L0)`) THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2) * ((betas:num->real) n * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `L0 < inv(sqrt(&2) * ((betas:num->real) n * eps))` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(sqrt(&2) * ((betas:num->real) n * eps)) =
                  &1 / (sqrt(&2) * (betas n * eps))` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    SUBGOAL_THEN `(betas:num->real) n < &1 / (sqrt(&2) * eps * L0)` MP_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID] THEN
      UNDISCH_TAC `abs((betas:num->real) n) < inv(sqrt(&2) * eps * L0)` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_neck_dom; annulus; SUBSET; IN_CBALL; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(z0:real^3) - r <= norm(y:real^3) /\ norm y <= norm z0 + r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dist(z0:real^3,y) <= r` THEN CONV_TAC NORM_ARITH; ALL_TAC] THEN
  ABBREV_TAC `L = inv(sqrt(&2) * ((betas:num->real) n * eps))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `norm(z0:real^3) - r` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < norm(z0:real^3) - r` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP EXP_LOG th)]) THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    UNDISCH_TAC `L0 < L` THEN EXPAND_TAC "L0" THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(z0:real^3) + r` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < norm(z0:real^3) + r` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP EXP_LOG th)]) THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    UNDISCH_TAC `L0 < L` THEN EXPAND_TAC "L0" THEN REAL_ARITH_TAC]);;

let P3E_UNIT_SPHERE_NECK_DOM = prove
 (`!eps. &0 < eps ==> sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfs_neck_dom; annulus; SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_EXP_0] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_EXP_0] THEN
  REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The abstract data of MT Prop 15.2 and the first half of the               *)
(* core: along any sequence of data with beta n -> 0, eventually            *)
(* r (1 - t0) < 1 (MT p. 354: on a beta eps-neck dR/dt > 0, so            *)
(* R(x,t') < R(x,t) and the strong neck at t' reaches back past t - 1/R). *)
(* P s is the rescaled family of the evolving neck (s in [-t0,0]), H s that *)
(* of the strong neck at t' (s in (-1,0]), psi the transition map,          *)
(* r = R'/R, yx the centre; P (s/r - t0) = r^-1 psi pullback of H s.        *)
(* ------------------------------------------------------------------------- *)

let p3e_gdata = new_definition
 `p3e_gdata (eps:real) (beta:real) (t0:real) (r:real)
            (P:real->real^3->real^3^3) (H:real->real^3->real^3^3)
            (psi:real^3->real^3) (psi':real^3->real^3) (yx:real^3) <=>
    &0 < t0 /\ t0 < &1 /\ &0 < r /\
    diffeomorphism_on (rfs_neck_dom (beta * eps)) (IMAGE psi (rfs_neck_dom (beta * eps)))
                      psi psi' /\
    IMAGE psi (rfs_neck_dom (beta * eps)) SUBSET rfs_neck_dom (beta * eps / &2) /\
    norm yx = &1 /\ norm(psi yx) = &1 /\
    (!s. --t0 <= s /\ s <= &0 ==> metric_field (rfs_neck_dom (beta * eps)) (P s)) /\
    (?d. d < (beta * eps) pow 2 /\
         !s y. --t0 < s /\ s <= &0 /\ y IN rfs_neck_dom (beta * eps)
               ==> lck_dist2 (rfs_kreg (beta * eps)) (cylinder_flow s) (P s) y <= d) /\
    (!s. --(&1) < s /\ s <= &0 ==> metric_field (rfs_neck_dom (beta * eps / &2)) (H s)) /\
    (?d. d < (beta * eps / &2) pow 2 /\
         !s y. --(&1) < s /\ s <= &0 /\ y IN rfs_neck_dom (beta * eps / &2)
               ==> lck_dist2 (rfs_kreg (beta * eps / &2)) (cylinder_flow s) (H s) y <= d) /\
    (!s y. --(&1) < s /\ s <= &0 /\ y IN rfs_neck_dom (beta * eps)
           ==> P (s / r - t0) y = inv r %% mpullback psi (H s) y) /\
    (!K m e. compact K /\ K SUBSET rfs_neck_dom (beta * eps) /\ &0 < e
             ==> ?dl. &0 < dl /\
                      !s y l. --t0 < s /\ s < --t0 + dl /\ y IN K /\
                              l IN pde_index_lists m (:3)
                              ==> norm(iterated_partial l
                                         ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                          P s) y -
                                       iterated_partial l (vectorize o P (--t0)) y) < e) /\
    lscalar (P (&0)) yx = &1 /\ lscalar (P (--t0)) yx = r /\
    (\s. lscalar (P s) yx) real_continuous_on real_interval[--t0,&0] /\
    (!s. --t0 < s /\ s < &0
         ==> ((\s. lscalar (P s) yx) has_real_derivative
              (llap (P s) (lscalar (P s)) yx + &2 * ltnorm2 2 (P s) (lric2 (P s)) yx))
             (atreal s))`;;

let P3E_SUBSEQ_REAL = prove
 (`!(x:num->real) a b.
     (!n. a <= x n /\ x n <= b)
     ==> ?l sub. a <= l /\ l <= b /\ (!m n. m < n ==> sub m < sub n) /\
                 ((\n. lift(x(sub n))) --> lift l) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `interval[lift a,lift b]` compact) THEN
  REWRITE_TAC[COMPACT_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. lift((x:num->real) n)`) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^1` (X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`drop l`; `sub:num->num`] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  UNDISCH_TAC `(((\n. lift((x:num->real) n)) o sub) --> l) sequentially` THEN
  REWRITE_TAC[o_DEF]);;

let P3E_SUBSEQ_SPHERE = prove
 (`!(y:num->real^N).
     (!n. norm(y n) = &1)
     ==> ?l sub. norm l = &1 /\ (!m n. m < n ==> sub m < sub n) /\
                 ((\n. y(sub n)) --> l) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `sphere(vec 0:real^N,&1)` compact) THEN
  REWRITE_TAC[COMPACT_SPHERE] THEN
  DISCH_THEN(MP_TAC o SPEC `y:num->real^N`) THEN
  ASM_REWRITE_TAC[IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N` (X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`l:real^N`; `sub:num->num`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(((y:num->real^N) o sub) --> l) sequentially` THEN
  REWRITE_TAC[o_DEF; ETA_AX]);;

let P3E_BETA_SUBSEQ = prove
 (`!(betas:num->real) sub.
     (!n. &0 < betas n) /\ ((\n. lift(betas n)) --> vec 0) sequentially /\
     (!m n. m < n ==> sub m < sub n)
     ==> (!n. &0 < betas(sub n)) /\ ((\n. lift(betas(sub n))) --> vec 0) sequentially`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\n. lift((betas:num->real) n)`; `sub:num->num`; `vec 0:real^1`]
         LIM_SUBSEQUENCE) THEN
  ASM_REWRITE_TAC[o_DEF]);;

let P3E_ERR_NULL = prove
 (`!(betas:num->real) eps ds.
     &0 < eps /\ (!n. &0 < betas n /\ betas n < &1) /\
     ((\n. lift(betas n)) --> vec 0) sequentially /\
     (!n. &0 <= ds n /\ ds n < (betas n * eps) pow 2)
     ==> ((\n. lift(ds n)) --> vec 0) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. eps pow 2 * (betas:num->real) n` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[NORM_LIFT] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MATCH_MP_TAC(REAL_ARITH `!d x y. &0 <= d /\ d < x /\ x <= y ==> abs d <= y`) THEN
    EXISTS_TAC `((betas:num->real) n * eps) pow 2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[LIFT_CMUL] THEN
    SUBGOAL_THEN `vec 0:real^1 = eps pow 2 % vec 0` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
    MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[]]);;

let P3E_GDATA_SEQ_C1 = prove
 (`!eps (betas:num->real) t0s rs (Ps:num->real->real^3->real^3^3) Hs psis psis' yxs.
     &0 < eps /\ eps < &1 /\
     (!n. &0 < betas n /\ betas n < &1 / &2 /\
          p3e_gdata eps (betas n) (t0s n) (rs n) (Ps n) (Hs n) (psis n) (psis' n) (yxs n)) /\
     ((\n. lift(betas n)) --> vec 0) sequentially
     ==> ?n. rs n * (&1 - t0s n) < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; REAL_NOT_LT]) THEN
  SUBGOAL_THEN
   `!n. ?xi. --(t0s n) < xi /\ xi < &0 /\
             llap ((Ps:num->real->real^3->real^3^3) n xi) (lscalar (Ps n xi)) (yxs n) +
             &2 * ltnorm2 2 (Ps n xi) (lric2 (Ps n xi)) (yxs n) < &0`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> can (find_term (fun t ->
      is_var t && fst(dest_var t) = "rs")) (concl th) && is_forall(concl th))) THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> can (find_term (fun t ->
      is_const t && fst(dest_const t) = "p3e_gdata")) (concl th))) THEN
    REWRITE_TAC[p3e_gdata] THEN
    STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\s. lscalar ((Ps:num->real->real^3->real^3^3) n s) (yxs n)`;
                   `\s. llap ((Ps:num->real->real^3->real^3^3) n s) (lscalar (Ps n s)) (yxs n) +
                        &2 * ltnorm2 2 (Ps n s) (lric2 (Ps n s)) (yxs n)`;
                   `--((t0s:num->real) n)`; `&0`] REAL_MVT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THEN
      TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `xi:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lscalar ((Ps:num->real->real^3->real^3^3) n (&0)) (yxs n) -
                 lscalar (Ps n (--(t0s n))) (yxs n) =
                 (llap (Ps n xi) (lscalar (Ps n xi)) (yxs n) +
                  &2 * ltnorm2 2 (Ps n xi) (lric2 (Ps n xi)) (yxs n)) *
                 (&0 - --(t0s n))` THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `F0 = llap ((Ps:num->real->real^3->real^3^3) n xi) (lscalar (Ps n xi)) (yxs n) +
                     &2 * ltnorm2 2 (Ps n xi) (lric2 (Ps n xi)) (yxs n)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&1 < (rs:num->real) n` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `!y. &1 <= y /\ y < r ==> &1 < r`) THEN
      EXISTS_TAC `(rs:num->real) n * (&1 - t0s n)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < r * t ==> r * (&1 - t) < r`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!t. &0 < t /\ (F0 * t < &0 ==> F0 < &0) /\ F0 * t < &0
                               ==> F0 < &0`) THEN
    EXISTS_TAC `(t0s:num->real) n` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `~(&0 <= x) ==> x < &0`) THEN DISCH_TAC THEN
      UNDISCH_TAC `F0 * (t0s:num->real) n < &0` THEN REWRITE_TAC[REAL_NOT_LT] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&1 - (rs:num->real) n = F0 * (&0 - --t0s n)` THEN
      UNDISCH_TAC `&1 < (rs:num->real) n` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `xis:num->real` (LABEL_TAC "XI")) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `rs:num->real`)) (concl th) &&
                                              is_forall(concl th))) THEN
  SUBGOAL_THEN
   `!n. &0 < (t0s:num->real) n /\ t0s n < &1 /\ norm((yxs:num->real^3) n) = &1 /\
        (!s. --(t0s n) <= s /\ s <= &0
             ==> metric_field (rfs_neck_dom (betas n * eps))
                              ((Ps:num->real->real^3->real^3^3) n s)) /\
        (?d. d < (betas n * eps) pow 2 /\
             !s y. --(t0s n) < s /\ s <= &0 /\ y IN rfs_neck_dom (betas n * eps)
                   ==> lck_dist2 (rfs_kreg (betas n * eps)) (cylinder_flow s) (Ps n s) y
                       <= d)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> can (find_term (fun t ->
      is_const t && fst(dest_const t) = "p3e_gdata")) (concl th))) THEN
    REWRITE_TAC[p3e_gdata] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_AND_THM; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "T0") (CONJUNCTS_THEN2 (LABEL_TAC "T1")
    (CONJUNCTS_THEN2 (LABEL_TAC "YX") (CONJUNCTS_THEN2 (LABEL_TAC "MF")
      (X_CHOOSE_THEN `ds:num->real` (CONJUNCTS_THEN2 (LABEL_TAC "DS1") (LABEL_TAC "DS"))))))) THEN
  MP_TAC(ISPECL [`xis:num->real`; `--(&1)`; `&0`] P3E_SUBSEQ_REAL) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "XI" (MP_TAC o SPEC `n:num`) THEN
    USE_THEN "T1" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xi0:real` (X_CHOOSE_THEN `s1:num->num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `\n:num. (yxs:num->real^3) ((s1:num->num) n)` P3E_SUBSEQ_SPHERE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (X_CHOOSE_THEN `s2:num->num`
    (STRIP_ASSUME_TAC o BETA_RULE))) THEN
  ABBREV_TAC `sub = \n. (s1:num->num) ((s2:num->num) n)` THEN
  SUBGOAL_THEN `!m n. m < n ==> (sub:num->num) m < sub n` ASSUME_TAC THENL
   [EXPAND_TAC "sub" THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((\n. lift((xis:num->real) ((sub:num->num) n))) --> lift xi0) sequentially`
  ASSUME_TAC THENL
   [EXPAND_TAC "sub" THEN
    MP_TAC(ISPECL [`\n. lift((xis:num->real) ((s1:num->num) n))`; `s2:num->num`;
                   `lift xi0`] LIM_SUBSEQUENCE) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. (yxs:num->real^3) ((sub:num->num) n)) --> y0) sequentially` ASSUME_TAC THENL
   [EXPAND_TAC "sub" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`betas:num->real`; `sub:num->num`] P3E_BETA_SUBSEQ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`\n. (Ps:num->real->real^3->real^3^3) ((sub:num->num) n) (xis((sub:num->num) n))`;
    `\n. rfs_neck_dom ((betas:num->real) ((sub:num->num) n) * eps)`;
    `\n. (xis:num->real) ((sub:num->num) n)`; `xi0:real`;
    `\n. rfs_kreg ((betas:num->real) ((sub:num->num) n) * eps)`; `\n. (ds:num->real) ((sub:num->num) n)`;
    `y0:real^3`; `&1 / &2`] P3E_NECK_SEQ_MNEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_CBALL; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `w:real^3` THEN
      DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `dist(y0:real^3,vec 0) <= &1 / &2` THEN
      UNDISCH_TAC `norm(y0:real^3) = &1` THEN CONV_TAC NORM_ARITH;
      MP_TAC(ISPECL [`eps:real`; `\n. (betas:num->real) ((sub:num->num) n)`] P3E_KREG_TENDSTO) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3E_ERR_NULL THEN
      MAP_EVERY EXISTS_TAC [`\n. (betas:num->real) ((sub:num->num) n)`; `eps:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `n:num` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> can (find_term (fun t ->
          is_const t && fst(dest_const t) = "p3e_gdata")) (concl th))) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "DS1" (ASSUME_TAC o SPEC `(sub:num->num) n`) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg ((betas:num->real) ((sub:num->num) n) * eps))
                    (cylinder_flow ((xis:num->real) ((sub:num->num) n)))
                    ((Ps:num->real->real^3->real^3^3) ((sub:num->num) n) (xis((sub:num->num) n)))
                    ((yxs:num->real^3) ((sub:num->num) n))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P3E_LCK_DIST2_POS THEN
        EXISTS_TAC `rfs_neck_dom ((betas:num->real) ((sub:num->num) n) * eps)` THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
          REWRITE_TAC[APX_NECK_DOM_NONZERO; rfs_neck_dom; OPEN_ANNULUS] THEN
          MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN
          USE_THEN "XI" (MP_TAC o SPEC `(sub:num->num) n`) THEN REAL_ARITH_TAC;
          USE_THEN "MF" MATCH_MP_TAC THEN
          USE_THEN "XI" (MP_TAC o SPEC `(sub:num->num) n`) THEN REAL_ARITH_TAC;
          MP_TAC(SPEC `(betas:num->real) ((sub:num->num) n) * eps` P3E_UNIT_SPHERE_NECK_DOM) THEN
          ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_MUL]; ALL_TAC] THEN
          REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[]];
        USE_THEN "DS" (MATCH_MP_TAC o SPEC `(sub:num->num) n`) THEN
        USE_THEN "XI" (MP_TAC o SPEC `(sub:num->num) n`) THEN
        SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
        MP_TAC(SPEC `(betas:num->real) ((sub:num->num) n) * eps` P3E_UNIT_SPHERE_NECK_DOM) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_MUL]; ALL_TAC] THEN
        REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`eps:real`; `\n. (betas:num->real) ((sub:num->num) n)`; `y0:real^3`; `&1 / &2`]
           P3E_NECK_DOM_EVENTUALLY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "XI" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) n`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "MF" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "DS" (MATCH_MP_TAC o SPEC `(sub:num->num) n`) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`xi0:real`; `y0:real^3`;
                 `\n. (Ps:num->real->real^3->real^3^3) ((sub:num->num) n) (xis((sub:num->num) n))`;
                 `\n. (yxs:num->real^3) ((sub:num->num) n)`] P3E_MNEAR_CYL_EVOL_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `norm(vec 0:real^3) = &1` THEN
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  USE_THEN "XI" (MP_TAC o SPEC `(sub:num->num) N`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The junction.  The rescaled family of the evolving neck is                *)
(* close to the cylinder flow only for s in (-t0 n,0]; jet continuity of   *)
(* the family at -t0 n (a per-n choice of times sts n with errors below     *)
(* 1/(n+1) on exhausting compacts) transfers the convergence to the        *)
(* junction metrics Ps n (-t0 n) -> cyl(-t0).                               *)
(* ------------------------------------------------------------------------- *)

let P3E_JUNCTION_SEQ = prove
 (`!(Ps:num->real->real^3->real^3^3) (t0s:num->real) t0 (ks:num->num) ds
    (Ds:num->real^3->bool) Ks.
     ((\n. lift(t0s n)) --> lift t0) sequentially /\ &0 <= t0 /\
     (!n. &0 < t0s n) /\
     (!m. ?N. !n. N <= n ==> m <= ks n) /\
     ((\n. lift(ds n)) --> vec 0) sequentially /\
     (!n. open (Ds n) /\ Ds n SUBSET (:real^3) DELETE vec 0) /\
     (!n s. --(t0s n) <= s /\ s <= &0 ==> metric_field (Ds n) (Ps n s)) /\
     (!n s y. --(t0s n) < s /\ s <= &0 /\ y IN Ds n
              ==> lck_dist2 (ks n) (cylinder_flow s) (Ps n s) y <= ds n) /\
     (!n. compact (Ks n) /\ Ks n SUBSET Ds n) /\
     (!z r. &0 <= r /\ r < norm z ==> ?N. !n. N <= n ==> cball(z,r) SUBSET Ks n) /\
     (!n K m e. compact K /\ K SUBSET Ds n /\ &0 < e
                ==> ?dl. &0 < dl /\
                         !s y l. --(t0s n) < s /\ s < --(t0s n) + dl /\ y IN K /\
                                 l IN pde_index_lists m (:3)
                                 ==> norm(iterated_partial l
                                            ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                             Ps n s) y -
                                          iterated_partial l (vectorize o Ps n (--(t0s n))) y)
                                     < e)
     ==> !z. ~(z = vec 0)
             ==> p2cm_mnear z (\n. Ps n (--(t0s n))) (cylinder_flow (--t0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "T0") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TP") (CONJUNCTS_THEN2 (LABEL_TAC "KS")
    (CONJUNCTS_THEN2 (LABEL_TAC "DS") (CONJUNCTS_THEN2 (LABEL_TAC "OD")
    (CONJUNCTS_THEN2 (LABEL_TAC "MF") (CONJUNCTS_THEN2 (LABEL_TAC "CL")
    (CONJUNCTS_THEN2 (LABEL_TAC "KC") (CONJUNCTS_THEN2 (LABEL_TAC "EX")
      (LABEL_TAC "CT"))))))))))) THEN
  (* the per-n times *)
  SUBGOAL_THEN
   `?sts:num->real.
      !n. --(t0s n) < sts n /\ sts n < &0 /\ sts n < --(t0s n) + inv(&n + &1) /\
          !y l. y IN (Ks:num->real^3->bool) n /\ l IN pde_index_lists n (:3)
                ==> norm(iterated_partial l
                           ((vectorize:real^3^3->real^(3,3)finite_prod) o
                            (Ps:num->real->real^3->real^3^3) n (sts n)) y -
                         iterated_partial l (vectorize o Ps n (--(t0s n))) y)
                    < inv(&n + &1)`
  (X_CHOOSE_THEN `sts:num->real` (LABEL_TAC "ST")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    USE_THEN "CT" (MP_TAC o SPECL [`n:num`; `(Ks:num->real^3->bool) n`; `n:num`;
                                   `inv(&n + &1)`]) THEN
    ANTS_TAC THENL
     [USE_THEN "KC" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[] THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `--((t0s:num->real) n) + min dl (min (t0s n) (inv(&n + &1))) / &2` THEN
    SUBGOAL_THEN `&0 < (t0s:num->real) n /\ &0 < inv(&n + &1)` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_MIN_LT] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_min] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_min] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_min] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. lift((sts:num->real) n)) --> lift(--t0)) sequentially` ASSUME_TAC THENL
   [SUBGOAL_THEN `!n. lift((sts:num->real) n) =
                      --lift(t0s n) + lift(sts n + t0s n)` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[GSYM LIFT_NEG; GSYM LIFT_ADD] THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `lift(--t0) = --lift t0 + vec 0` SUBST1_TAC THENL
     [REWRITE_TAC[LIFT_NEG; VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIM_NEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LIM_NULL_COMPARISON THEN EXISTS_TAC `\n. inv(&n + &1)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[NORM_LIFT] THEN
      USE_THEN "ST" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REAL_ARITH_TAC;
      ACCEPT_TAC(SPEC `&1` SEQ_HARMONIC_OFFSET)];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n. (Ps:num->real->real^3->real^3^3) n (sts n)`; `Ds:num->real^3->bool`;
    `sts:num->real`; `--t0:real`; `ks:num->num`; `ds:num->real`; `z:real^3`;
    `norm(z:real^3) / &2`] P3E_NECK_SEQ_MNEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_CBALL; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `w:real^3` THEN
      DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `dist(z:real^3,vec 0) <= norm z / &2` THEN
      UNDISCH_TAC `&0 < norm(z:real^3)` THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    USE_THEN "EX" (MP_TAC o SPECL [`z:real^3`; `norm(z:real^3) / &2`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "ST" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(Ks:num->real^3->bool) n` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "KC" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]];
      USE_THEN "MF" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "CL" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2CI_NEAR_PARTIALS o CONJUNCT2 o
              GEN_REWRITE_RULE I [p2cm_mnear]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PC"))) THEN
  USE_THEN "EX" (MP_TAC o SPECL [`z:real^3`; `norm(z:real^3) / &2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "N0")) THEN
  ABBREV_TAC `r0 = min r1 (norm(z:real^3) / &2)` THEN
  SUBGOAL_THEN `&0 < r0` ASSUME_TAC THENL
   [EXPAND_TAC "r0" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. N0 <= n ==> ball(z:real^3,r0) SUBSET (Ks:num->real^3->bool) n /\
                               ball(z,r0) SUBSET ball(z,r1)` (LABEL_TAC "BK") THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z:real^3,norm z / &2)` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "r0" THEN REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN REAL_ARITH_TAC;
        USE_THEN "N0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      EXPAND_TAC "r0" THEN REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (ball(z:real^3,r0)) (cylinder_flow (--t0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `dist(z:real^3,vec 0) < r0` THEN EXPAND_TAC "r0" THEN
    UNDISCH_TAC `&0 < norm(z:real^3)` THEN REWRITE_TAC[REAL_LT_MIN] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. N0 <= n ==> metric_field (ball(z:real^3,r0))
                      ((Ps:num->real->real^3->real^3^3) n (--(t0s n)))`
  (LABEL_TAC "MQ") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(Ds:num->real^3->bool) n` THEN REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [USE_THEN "MF" MATCH_MP_TAC THEN USE_THEN "TP" (MP_TAC o SPEC `n:num`) THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(Ks:num->real^3->bool) n` THEN
      CONJ_TAC THENL
       [USE_THEN "BK" (MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[];
        USE_THEN "KC" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[p2cm_mnear] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`r0:real`; `N0:num`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "MQ" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `r0:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `N0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "MQ" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[metric_field]];
    UNDISCH_TAC `metric_field (ball(z:real^3,r0)) (cylinder_flow (--t0))` THEN
    SIMP_TAC[metric_field];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "PC" (MP_TAC o SPEC `l:num list`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:num` (LABEL_TAC "K1")) THEN
  MP_TAC(SPEC `e / &2` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N0 + K1 + M + LENGTH(l:num list)` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
  USE_THEN "K1" (MP_TAC o SPECL [`n:num`; `y:real^3`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "BK" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  USE_THEN "ST" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `n:num`) THEN
  DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `l:num list`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "BK" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
      REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `inv(&n + &1) < e / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&M)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `~(M = 0)` THEN
    UNDISCH_TAC `N0 + K1 + M + LENGTH(l:num list) <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN
  UNDISCH_TAC `norm(iterated_partial l
                  ((vectorize:real^3^3->real^(3,3)finite_prod) o
                   (Ps:num->real->real^3->real^3^3) n (sts n)) y -
                iterated_partial l (vectorize o Ps n (--(t0s n))) y) < inv(&n + &1)` THEN
  UNDISCH_TAC `norm(iterated_partial l
                  ((\n. (vectorize:real^3^3->real^(3,3)finite_prod) o
                   (\n. (Ps:num->real->real^3->real^3^3) n (sts n)) n) n) y -
                iterated_partial l (vectorize o cylinder_flow (--t0)) y) < e / &2` THEN
  UNDISCH_TAC `inv(&n + &1) < e / &2` THEN REWRITE_TAC[] THEN CONV_TAC NORM_ARITH);;

(* ------------------------------------------------------------------------- *)
(* Quadratic-form bounds.  Uniform near-convergence on a compact set gives   *)
(* uniform closeness of the quadratic forms; the cylinder                    *)
(* metrics have the conformal bounds (2/|z|^2) |a|^2 <= a cyl(b) a <=       *)
(* (1 - b) (2/|z|^2) |a|^2 for b <= 0.                                       *)
(* ------------------------------------------------------------------------- *)

let P3E_QF_VEC = prove
 (`!(M:real^N^N) a. abs(a dot (M ** a)) <= norm(vectorize M) * (a dot a)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(a:real^N) * norm((M:real^N^N) ** a)` THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(a:real^N) * norm(vectorize(M:real^N^N)) * norm a` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE; COMPATIBLE_NORM_VECTORIZE];
    REWRITE_TAC[GSYM NORM_POW_2; REAL_POW_2] THEN REAL_ARITH_TAC]);;

let P3E_NEAR_QF_UNIF = prove
 (`!K (Gs:num->real^N->real^N^N) G0.
     compact K /\ (!z. z IN K ==> p2ci_near z (\n. vectorize o Gs n) (vectorize o G0))
     ==> !e. &0 < e
             ==> ?N. !n z a. N <= n /\ z IN K
                             ==> abs(a dot (Gs n z ** a) - a dot (G0 z ** a)) <=
                                 e * (a dot a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2CI_NEAR_COMPACT) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N`; `a:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `z:real^N`]) THEN ASM_REWRITE_TAC[o_THM] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(Gs:num->real^N->real^N^N) n z - G0 z`; `a:real^N`] P3E_QF_VEC) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RSUB; VECTORIZE_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN ASM_REAL_ARITH_TAC);;

let P3E_CYL0_QF = prove
 (`!(z:real^3) a. a dot (cylinder_flow (&0) z ** a) = (&2 / norm z pow 2) * (a dot a)`,
  REWRITE_TAC[LRG_CYL_FLOW_DOT] THEN REAL_ARITH_TAC);;

let P3E_CYL_QF_BOUNDS = prove
 (`!b (z:real^3) a.
     b <= &0 /\ ~(z = vec 0)
     ==> (&2 / norm z pow 2) * (a dot a) <= a dot (cylinder_flow b z ** a) /\
         a dot (cylinder_flow b z ** a) <= (&1 - b) * (&2 / norm z pow 2) * (a dot a)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`b:real`; `&0`; `z:real^3`; `a:real^3`] P3E_CYL_COMPARE2) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P3E_CYL0_QF] THEN
    SUBGOAL_THEN `max (&1) ((&1 - &0) / (&1 - b)) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> max (&1) x = &1`) THEN
      SUBGOAL_THEN `&0 < &1 - b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_LID]];
    MP_TAC(ISPECL [`&0`; `b:real`; `z:real^3`; `a:real^3`] P3E_CYL_COMPARE2) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P3E_CYL0_QF; REAL_SUB_RZERO; REAL_DIV_1] THEN
    SUBGOAL_THEN `max (&1) (&1 - b) = &1 - b` SUBST1_TAC THENL
     [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[]]]);;

let P3E_PSI_LOCATION = prove
 (`!(psi:real^3->real^3) (Q:real^3->real^3^3) (B:real^3->real^3^3) U yx al be.
     (!z. z IN U ==> ~(z = vec 0) /\ Q z = mpullback psi B z /\
                     psi differentiable at z /\ ~(psi z = vec 0)) /\
     &0 <= al /\ &0 < be /\
     (!z a. z IN U ==> a dot (Q z ** a) <= al * (&2 / norm z pow 2) * (a dot a)) /\
     (!z a. z IN U ==> be * (&2 / norm(psi z) pow 2) * (a dot a) <=
                       a dot (B (psi z) ** a)) /\
     norm yx = &1 /\ norm(psi yx) = &1
     ==> !y. ~(y = vec 0) /\
             {z | min (norm y) (inv(sqrt(&2))) <= norm z /\ norm z <= max (norm y) (&1)}
             SUBSET U
             ==> abs(log(norm(psi y))) <=
                 sqrt(al / be) * (abs(norm y - &1) / min (norm y) (&1) + &6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `U:real^3->bool`; `sqrt(al / be)`;
                 `yx:real^3`; `y:real^3`] P3E_LOGNORM_PATH) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH; LOG_1; REAL_SUB_RZERO] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC P3E_CONFORMAL_ISOM_DERIV THEN
  MAP_EVERY EXISTS_TAC [`Q:real^3->real^3^3`; `B:real^3->real^3^3`] THEN
  ASM_SIMP_TAC[]);;

let P3E_MPULLBACK_CMUL = prove
 (`!(h:real^N->real^N) (G:real^N->real^N^N) c z.
     mpullback h (\w. c %% G w) z = c %% mpullback h G z`,
  REWRITE_TAC[mpullback; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

let P3E_ANNULUS_COMPACT = prove
 (`!a b. compact {z:real^N | a <= norm z /\ norm z <= b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{z:real^N | a <= norm z /\ norm z <= b} = cball(vec 0,b) DIFF ball(vec 0,a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]]);;

let P3E_INV_SQ_BOUNDS = prove
 (`!a b (z:real^N).
     &0 < a /\ a <= norm z /\ norm z <= b
     ==> &2 / b pow 2 <= &2 / norm z pow 2 /\ &2 / norm z pow 2 <= &2 / a pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  (CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A convergent subsequence of the transition maps.  psis n                  *)
(* pulls inv(rs n) Hs0 n back to Qs n, with Qs n -> cyl(-t0) and            *)
(* Hs0 n -> cyl(0) in the near calculus and Hs0 n C^0-close to cyl(0) on   *)
(* the images; both necks are centred at x, so psis n maps the centre yxs n *)
(* of the unit sphere into the unit sphere.  Conformal bounds give the      *)
(* location of psis n on a ball around y0 (P3E_PSI_LOCATION), then jets     *)
(* and a subsequence (P3E_ISOM_SUBSEQ).                                     *)
(* ------------------------------------------------------------------------- *)

let P3E_MIN_MUL_LE = prove
 (`!e k c1 c2 A q.
     &0 <= k /\ c1 <= c2 /\ &0 <= A /\ k * c2 * A <= q ==> min e (k * c1) * A <= q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k * c2 * A` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k * c1` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let P3E_PSI_SUBSEQ = prove
 (`!(psis:num->real^3->real^3) psis' (Ds:num->real^3->bool) (Qs:num->real^3->real^3^3)
    (Hs0:num->real^3->real^3^3) rs r0 t0 (y0:real^3) yxs ds2.
     ~(y0 = vec 0) /\ &0 <= t0 /\ t0 <= &1 /\ &0 < r0 /\
     (!n. open (Ds n) /\ Ds n SUBSET (:real^3) DELETE vec 0 /\
          diffeomorphism_on (Ds n) (IMAGE (psis n) (Ds n)) (psis n) (psis' n) /\
          IMAGE (psis n) (Ds n) SUBSET (:real^3) DELETE vec 0 /\
          metric_field (Ds n) (Qs n) /\
          metric_field (IMAGE (psis n) (Ds n)) (Hs0 n) /\
          (!z. z IN Ds n ==> Qs n z = mpullback (psis n) (\w. inv(rs n) %% Hs0 n w) z) /\
          (!w. w IN IMAGE (psis n) (Ds n)
               ==> lck_dist2 0 (cylinder_flow (&0)) (Hs0 n) w <= ds2 n) /\
          &0 < rs n /\ norm(yxs n) = &1 /\ norm(psis n (yxs n)) = &1) /\
     (!z. ~(z = vec 0) ==> p2cm_mnear z Qs (cylinder_flow (--t0))) /\
     (!w. ~(w = vec 0) ==> p2cm_mnear w Hs0 (cylinder_flow (&0))) /\
     ((\n. lift(ds2 n)) --> vec 0) sequentially /\
     ((\n. lift(rs n)) --> lift r0) sequentially /\
     (!a b. &0 < a /\ a <= b
            ==> ?N. !n. N <= n ==> {z | a <= norm z /\ norm z <= b} SUBSET Ds n)
     ==> ?sub psi. (!m n. m < n ==> sub m < sub n) /\
                   p2ci_near y0 (\n. psis (sub n)) psi /\ ~(psi y0 = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "D") (CONJUNCTS_THEN2 (LABEL_TAC "QN")
    (CONJUNCTS_THEN2 (LABEL_TAC "HN") (CONJUNCTS_THEN2 (LABEL_TAC "D2")
    (CONJUNCTS_THEN2 (LABEL_TAC "RN") (LABEL_TAC "EX")))))))))) THEN
  ABBREV_TAC `a0 = min (norm(y0:real^3) / &2) (&1 / &2)` THEN
  ABBREV_TAC `b0 = max (&2 * norm(y0:real^3)) (&2)` THEN
  SUBGOAL_THEN `&0 < norm(y0:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a0 /\ a0 <= &1 / &2 /\ a0 <= norm(y0:real^3) / &2 /\
                &2 <= b0 /\ &2 * norm(y0:real^3) <= b0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a0"; "b0"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `KU = {z:real^3 | a0 / &2 <= norm z /\ norm z <= &2 * b0}` THEN
  ABBREV_TAC `U = {z:real^3 | a0 / &2 < norm z /\ norm z < &2 * b0}` THEN
  SUBGOAL_THEN `compact(KU:real^3->bool) /\ (U:real^3->bool) SUBSET KU /\
                (!z:real^3. z IN KU ==> ~(z = vec 0))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["KU"; "U"] THEN REWRITE_TAC[P3E_ANNULUS_COMPACT] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `a0 / &2 <= norm(vec 0:real^3)` THEN REWRITE_TAC[NORM_0] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* eventually KU inside Ds n *)
  USE_THEN "EX" (MP_TAC o SPECL [`a0 / &2`; `&2 * b0`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  (* uniform closeness of Qs n to cyl(-t0) on KU *)
  MP_TAC(ISPECL [`KU:real^3->bool`; `Qs:num->real^3->real^3^3`; `cylinder_flow (--t0)`]
         P3E_NEAR_QF_UNIF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "QN" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[]; SIMP_TAC[p2cm_mnear]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&4 * b0 pow 2)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  SUBGOAL_THEN
   `!n z a. N2 <= n /\ z IN KU
            ==> a dot ((Qs:num->real^3->real^3^3) n z ** a) <=
                &3 * (&2 / norm z pow 2) * (a dot a) /\
                inv(&4 * b0 pow 2) * (a dot a) <= a dot (Qs n z ** a) /\
                a dot (Qs n z ** a) <= (&24 / a0 pow 2) * (a dot a)`
  (LABEL_TAC "QB") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`; `a:real^3`] THEN STRIP_TAC THEN
    USE_THEN "N2" (MP_TAC o SPECL [`n:num`; `z:real^3`; `a:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`--t0:real`; `z:real^3`; `a:real^3`] P3E_CYL_QF_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`a0 / &2`; `&2 * b0`; `z:real^3`] P3E_INV_SQ_BOUNDS) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN KU` THEN EXPAND_TAC "KU" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    SUBGOAL_THEN `~(b0 = &0) /\ ~(a0 = &0)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 / (&2 * b0) pow 2 = &2 * inv(&4 * b0 pow 2) /\
                  &2 / (a0 / &2) pow 2 = &8 / a0 pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[real_div] THEN
      UNDISCH_TAC `~(b0 = &0)` THEN UNDISCH_TAC `~(a0 = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ABBREV_TAC `c = &2 / norm(z:real^3) pow 2` THEN
    ABBREV_TAC `A = (a:real^3) dot a` THEN
    ABBREV_TAC `et = inv(&4 * b0 pow 2)` THEN
    SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * et) * A <= c * A /\ t0 * (c * A) <= &1 * (c * A) /\
                  c * A <= (&8 / a0 pow 2) * A /\ &0 <= c * A`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_MESON_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_MESON_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= et * A` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "et" THEN
      REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `abs(a dot ((Qs:num->real^3->real^3^3) n z ** a) -
                     a dot (cylinder_flow (--t0) z ** a)) <= et * A` THEN
    UNDISCH_TAC `c * A <= a dot (cylinder_flow (--t0) z ** a)` THEN
    UNDISCH_TAC `a dot (cylinder_flow (--t0) z ** a) <= (&1 - --t0) * c * A` THEN
    UNDISCH_TAC `t0 * (c * A) <= &1 * (c * A)` THEN
    UNDISCH_TAC `(&2 * et) * A <= c * A` THEN
    UNDISCH_TAC `c * A <= (&8 / a0 pow 2) * A` THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the lower conformal bound for inv(rs n) Hs0 n on the images *)
  SUBGOAL_THEN
   `?N3. !n w a. N3 <= n /\ w IN IMAGE ((psis:num->real^3->real^3) n) (Ds n)
                 ==> inv(&4 * r0) * (&2 / norm w pow 2) * (a dot a) <=
                     a dot ((\w. inv(rs n) %% (Hs0:num->real^3->real^3^3) n w) w ** a)`
  (X_CHOOSE_THEN `N3:num` (LABEL_TAC "BB")) THENL
   [USE_THEN "D2" (MP_TAC o SPEC `&1 / &4` o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
    REWRITE_TAC[DIST_0; NORM_LIFT] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `M1:num` (LABEL_TAC "M1")) THEN
    USE_THEN "RN" (MP_TAC o SPEC `r0:real` o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
    REWRITE_TAC[DIST_LIFT] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `M2:num` (LABEL_TAC "M2")) THEN
    EXISTS_TAC `M1 + M2:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `w:real^3`; `a:real^3`] THEN STRIP_TAC THEN
    USE_THEN "D" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN `~(w:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `metric_field (IMAGE ((psis:num->real^3->real^3) n) (Ds n))
                               (cylinder_flow (&0))` ASSUME_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_LT_01] THEN
      UNDISCH_TAC `diffeomorphism_on ((Ds:num->real^3->bool) n)
                     (IMAGE ((psis:num->real^3->real^3) n) (Ds n)) (psis n)
                     ((psis':num->real^3->real^3) n)` THEN
      SIMP_TAC[diffeomorphism_on];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`0`; `IMAGE ((psis:num->real^3->real^3) n) (Ds n)`; `cylinder_flow (&0)`;
                   `(Hs0:num->real^3->real^3^3) n`; `w:real^3`; `a:real^3`] LCK_DIST_C0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[P3E_CYL0_QF] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(lck_dist2 0 (cylinder_flow (&0)) ((Hs0:num->real^3->real^3^3) n) w)
                  <= &1 / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(ds2:num->real) n` THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "M1" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "M2" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    ABBREV_TAC `c = &2 / norm(w:real^3) pow 2` THEN
    ABBREV_TAC `A = (a:real^3) dot a` THEN
    ABBREV_TAC `h = (a:real^3) dot ((Hs0:num->real^3->real^3^3) n w ** a)` THEN
    SUBGOAL_THEN `&0 <= c * A` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN MAP_EVERY EXPAND_TAC ["c"; "A"] THEN
      REWRITE_TAC[DOT_POS_LE] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 / &2) * (c * A) <= h` ASSUME_TAC THENL
     [SUBGOAL_THEN
       `sqrt(lck_dist2 0 (cylinder_flow (&0)) ((Hs0:num->real^3->real^3^3) n) w) * (c * A)
        <= (&1 / &2) * (c * A)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `abs(h - c * A) <=
                   sqrt(lck_dist2 0 (cylinder_flow (&0)) ((Hs0:num->real^3->real^3^3) n) w) *
                   c * A` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2 * r0) <= inv((rs:num->real) n)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs((rs:num->real) n - r0) < r0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * r0) * h` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * r0) * ((&1 / &2) * (c * A))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* location of psis n on the ball around y0 *)
  ABBREV_TAC `C2 = sqrt(&3 / inv(&4 * r0)) * ((b0 + &1) / a0 + &6)` THEN
  SUBGOAL_THEN `&0 < inv(sqrt(&2)) /\ &1 / &4 < inv(sqrt(&2))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&1 / &4 = inv(&4)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n y. N1 + N2 + N3 <= n /\ y IN ball(y0:real^3,norm y0 / &4)
          ==> exp(--C2) <= norm((psis:num->real^3->real^3) n y) /\
              norm(psis n y) <= exp C2`
  (LABEL_TAC "LOC") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "D" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN `&3 / &4 * norm(y0:real^3) <= norm(y:real^3) /\
                  norm y <= &5 / &4 * norm y0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN ball(y0,norm y0 / &4)` THEN REWRITE_TAC[IN_BALL] THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `KU SUBSET (Ds:num->real^3->bool) n` ASSUME_TAC THENL
     [USE_THEN "N1" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`(psis:num->real^3->real^3) n`; `(Qs:num->real^3->real^3^3) n`;
                   `\w. inv((rs:num->real) n) %% (Hs0:num->real^3->real^3^3) n w`;
                   `U:real^3->bool`; `(yxs:num->real^3) n`; `&3`; `inv(&4 * r0)`]
                  P3E_PSI_LOCATION) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN
      CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]]]] THENL
       [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(z:real^3) IN KU /\ z IN (Ds:num->real^3->bool) n` STRIP_ASSUME_TAC
        THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[];
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term (fun t ->
            t = `mpullback:(real^3->real^3)->(real^3->real^3^3)->real^3->real^3^3`))
            (concl th) && is_forall(concl th))) THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
          EXISTS_TAC `(Ds:num->real^3->bool) n` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `diffeomorphism_on ((Ds:num->real^3->bool) n)
                         (IMAGE ((psis:num->real^3->real^3) n) (Ds n)) (psis n)
                         ((psis':num->real^3->real^3) n)` THEN
          SIMP_TAC[diffeomorphism_on];
          SUBGOAL_THEN `(psis:num->real^3->real^3) n z IN IMAGE (psis n) (Ds n)` MP_TAC THENL
           [ASM SET_TAC[]; ASM SET_TAC[]]];
        MAP_EVERY X_GEN_TAC [`z:real^3`; `a:real^3`] THEN DISCH_TAC THEN
        USE_THEN "QB" (MP_TAC o SPECL [`n:num`; `z:real^3`; `a:real^3`]) THEN
        ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]; SIMP_TAC[]];
        MAP_EVERY X_GEN_TAC [`z:real^3`; `a:real^3`] THEN DISCH_TAC THEN
        USE_THEN "BB" (MATCH_MP_TAC o BETA_RULE) THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&3 / &4 * norm(y0:real^3) <= norm(vec 0:real^3)` THEN
        REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
        REWRITE_TAC[real_min; real_max] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(norm(y:real^3) - &1) / min (norm y) (&1) <= (b0 + &1) / a0` ASSUME_TAC
    THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(norm(y:real^3) - &1) / a0` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[REAL_LE_MIN] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `abs(log(norm((psis:num->real^3->real^3) n y))) <= C2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt(&3 / inv(&4 * r0)) *
                  (abs(norm(y:real^3) - &1) / min (norm y) (&1) + &6)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "C2" THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LE; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm((psis:num->real^3->real^3) n y)` ASSUME_TAC THENL
     [REWRITE_TAC[NORM_POS_LT] THEN
      SUBGOAL_THEN `(psis:num->real^3->real^3) n y IN IMAGE (psis n) (Ds n)` MP_TAC THENL
       [SUBGOAL_THEN `(y:real^3) IN (Ds:num->real^3->bool) n` MP_TAC THENL
         [SUBGOAL_THEN `(y:real^3) IN KU` MP_TAC THENL
           [EXPAND_TAC "KU" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
            ASM SET_TAC[]];
          SET_TAC[]];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [GSYM(MATCH_MP EXP_LOG th)]) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* jets of Qs n on KU and of the rescaled Hs0 n on the annulus L *)
  ABBREV_TAC `L = {w:real^3 | exp(--C2) <= norm w /\ norm w <= exp C2}` THEN
  SUBGOAL_THEN `compact(L:real^3->bool) /\ (!w:real^3. w IN L ==> ~(w = vec 0))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[P3E_ANNULUS_COMPACT; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `exp(--C2) <= norm(vec 0:real^3)` THEN REWRITE_TAC[NORM_0] THEN
    MP_TAC(SPEC `--C2` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. ?B N. !n z. N <= n /\ z IN KU
        ==> pde_jetn m ((vectorize:real^3^3->real^(3,3)finite_prod) o
                        (Qs:num->real^3->real^3^3) n) z <= B`
  (LABEL_TAC "JQ") THENL
   [MP_TAC(ISPECL [`KU:real^3->bool`;
                   `\n. (vectorize:real^3^3->real^(3,3)finite_prod) o (Qs:num->real^3->real^3^3) n`;
                   `(vectorize:real^3^3->real^(3,3)finite_prod) o cylinder_flow (--t0)`]
                  P3E_NEAR_UNIF_JETN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "QN" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[]; SIMP_TAC[p2cm_mnear]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. ?B N. !n w. N <= n /\ w IN L
        ==> pde_jetn m ((vectorize:real^3^3->real^(3,3)finite_prod) o
                        (\w. inv((rs:num->real) n) %% (Hs0:num->real^3->real^3^3) n w)) w <= B`
  (LABEL_TAC "JB") THENL
   [MP_TAC(ISPECL [`L:real^3->bool`;
                   `\n. (vectorize:real^3^3->real^(3,3)finite_prod) o
                        (\w. inv((rs:num->real) n) %% (Hs0:num->real^3->real^3^3) n w)`;
                   `(vectorize:real^3^3->real^(3,3)finite_prod) o
                    (\w:real^3. inv r0 %% cylinder_flow (&0) w)`]
                  P3E_NEAR_UNIF_JETN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w:real^3`; `\n:num. inv((rs:num->real) n)`; `inv r0`;
                   `Hs0:num->real^3->real^3^3`; `cylinder_flow (&0)`] P3E_NEAR_MAT_CMUL_SEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`sequentially`; `rs:num->real`; `r0:real`] LIM_INV) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "HN" (MP_TAC o SPEC `w:real^3`) THEN ANTS_TAC THENL
       [ASM_MESON_TAC[]; SIMP_TAC[p2cm_mnear]]];
    ALL_TAC] THEN
  (* the subsequence *)
  MP_TAC(ISPECL [`psis:num->real^3->real^3`; `psis':num->real^3->real^3`;
                 `Ds:num->real^3->bool`; `\n. IMAGE ((psis:num->real^3->real^3) n) (Ds n)`;
                 `Qs:num->real^3->real^3^3`;
                 `\n w. inv((rs:num->real) n) %% (Hs0:num->real^3->real^3^3) n w`;
                 `y0:real^3`; `norm(y0:real^3) / &8`] P3E_ISOM_SUBSEQ) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 * (norm(y0:real^3) / &8) = norm y0 / &4` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(y0:real^3,norm y0 / &4) SUBSET KU` ASSUME_TAC THENL
   [EXPAND_TAC "KU" THEN REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(NORM_ARITH `dist(y0:real^3,z) < norm y0 / &4
       ==> &3 / &4 * norm y0 <= norm z /\ norm z <= &5 / &4 * norm y0`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN USE_THEN "D" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ; ETA_AX];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `N1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `KU:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN
      USE_THEN "JQ" (X_CHOOSE_THEN `B1:real` (X_CHOOSE_THEN `M1:num` (LABEL_TAC "J1")) o
                     SPEC `m:num`) THEN
      USE_THEN "JB" (X_CHOOSE_THEN `B2:real` (X_CHOOSE_THEN `M2:num` (LABEL_TAC "J2")) o
                     SPEC `m:num`) THEN
      EXISTS_TAC `max B1 B2` THEN EXISTS_TAC `(M1:num) + M2 + N1 + N2 + N3` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN
        USE_THEN "J1" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
        MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max a b`) THEN
        USE_THEN "J2" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        USE_THEN "LOC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `&24 / a0 pow 2` THEN
      EXISTS_TAC `min (inv(&4 * b0 pow 2)) (inv(&4 * r0) * (&2 / exp C2 pow 2))` THEN
      EXISTS_TAC `(N1:num) + N2 + N3` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_LT_MUL THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
           [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
             [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_EXP_POS_LT]]]];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`; `a:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN KU /\ z IN (Ds:num->real^3->bool) n` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `KU SUBSET (Ds:num->real^3->bool) n` MP_TAC THENL
         [USE_THEN "N1" MATCH_MP_TAC THEN ASM_ARITH_TAC; ASM SET_TAC[]];
        ALL_TAC] THEN
      USE_THEN "QB" (MP_TAC o SPECL [`n:num`; `z:real^3`; `a:real^3`]) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; STRIP_TAC] THEN
      USE_THEN "BB" (MP_TAC o BETA_RULE o
        SPECL [`n:num`; `(psis:num->real^3->real^3) n z`; `a:real^3`]) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]; DISCH_TAC] THEN
      USE_THEN "LOC" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`exp(--C2)`; `exp C2`; `(psis:num->real^3->real^3) n z`]
                    P3E_INV_SQ_BOUNDS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_EXP_POS_LT]; STRIP_TAC] THEN
      SUBGOAL_THEN `&0 <= (a:real^3) dot a` ASSUME_TAC THENL
       [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `inv(&4 * b0 pow 2) * ((a:real^3) dot a)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC P3E_MIN_MUL_LE THEN
        EXISTS_TAC `&2 / norm((psis:num->real^3->real^3) n z) pow 2` THEN
        ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `exp C2` THEN EXISTS_TAC `(N1:num) + N2 + N3` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "LOC" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the limit map does not vanish at y0 *)
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `psi:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `psi:real^3->real^3`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM NORM_POS_LT] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `exp(--C2)` THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_LBOUND) THEN
  EXISTS_TAC `\n. (psis:num->real^3->real^3) ((sub:num->num) n) y0` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`y0:real^3`; `\n. (psis:num->real^3->real^3) ((sub:num->num) n)`;
                   `psi:real^3->real^3`] P2CM_NEAR_POINT) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `(N1:num) + N2 + N3` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o SPECL [`(sub:num->num) n`; `y0:real^3`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(SPEC `sub:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC;
        REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC];
      SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Subsequences in the near calculus, neck domains that exhaust              *)
(* the punctured space, and neck families with a general domain parameter   *)
(* es n -> 0 converging to cylinders at every nonzero point.                 *)
(* ------------------------------------------------------------------------- *)

let P3E_NEAR_SUBSEQ = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f sub.
     p2ci_near z0 Fs f /\ (!m n. m < n ==> sub m < sub n)
     ==> p2ci_near z0 (\n. Fs (sub n)) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `N:num` THEN ASM_MESON_TAC[LE_TRANS];
    X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `B:real` (X_CHOOSE_TAC `M:num`) o SPEC `m:num`) THEN
    MAP_EVERY EXISTS_TAC [`B:real`; `M:num`] THEN ASM_MESON_TAC[LE_TRANS];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `M:num` o C MATCH_MP (ASSUME `&0 < e`)) THEN
    EXISTS_TAC `M:num` THEN ASM_MESON_TAC[LE_TRANS]]);;

let P3E_MNEAR_SUBSEQ = prove
 (`!(z0:real^N) (As:num->real^N->real^N^N) A0 sub.
     p2cm_mnear z0 As A0 /\ (!m n. m < n ==> sub m < sub n)
     ==> p2cm_mnear z0 (\n. As (sub n)) A0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cm_mnear] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real`
    (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)) ASSUME_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`r:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LE_TRANS];
    MP_TAC(ISPECL [`z0:real^N`;
                   `\n. (vectorize:real^N^N->real^(N,N)finite_prod) o
                        (As:num->real^N->real^N^N) n`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) o (A0:real^N->real^N^N)`;
                   `sub:num->num`] P3E_NEAR_SUBSEQ) THEN
    ASM_REWRITE_TAC[]]);;

let P3E_ANNULUS_NECK_DOM_ES = prove
 (`!(es:num->real) a b.
     (!n. &0 < es n) /\ ((\n. lift(es n)) --> vec 0) sequentially /\ &0 < a /\ a <= b
     ==> ?N. !n. N <= n
                 ==> {z:real^3 | a <= norm z /\ norm z <= b} SUBSET rfs_neck_dom (es n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L0 = abs(log a) + abs(log b) + &1` THEN
  SUBGOAL_THEN `&1 <= L0` ASSUME_TAC THENL
   [EXPAND_TAC "L0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) * L0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `((\n. lift((es:num->real) n)) --> vec 0) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0; NORM_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(sqrt(&2) * L0)`) THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2) * (es:num->real) n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `L0 < inv(sqrt(&2) * (es:num->real) n)` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(sqrt(&2) * (es:num->real) n) = &1 / (sqrt(&2) * es n)`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    SUBGOAL_THEN `(es:num->real) n < &1 / (sqrt(&2) * L0)` MP_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID] THEN
      UNDISCH_TAC `abs((es:num->real) n) < inv(sqrt(&2) * L0)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_neck_dom; annulus; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  ABBREV_TAC `L = inv(sqrt(&2) * (es:num->real) n)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP EXP_LOG th)]) THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    UNDISCH_TAC `L0 < L` THEN EXPAND_TAC "L0" THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP EXP_LOG th)]) THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    UNDISCH_TAC `L0 < L` THEN EXPAND_TAC "L0" THEN REAL_ARITH_TAC]);;

let P3E_NECK_DOM_CLOSED = prove
 (`!e. &0 < e
       ==> {z:real^3 | exp(--(inv(sqrt(&2) * (&2 * e)))) <= norm z /\
                       norm z <= exp(inv(sqrt(&2) * (&2 * e)))} SUBSET rfs_neck_dom e /\
           rfs_neck_dom (&2 * e) SUBSET
           {z:real^3 | exp(--(inv(sqrt(&2) * (&2 * e)))) <= norm z /\
                       norm z <= exp(inv(sqrt(&2) * (&2 * e)))}`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv(sqrt(&2) * (&2 * e)) < inv(sqrt(&2) * e)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_neck_dom; annulus; SUBSET; IN_ELIM_THM] THEN CONJ_TAC THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(--(inv(sqrt(&2) * (&2 * e))))` THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp(inv(sqrt(&2) * (&2 * e)))` THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LT]]);;

let P3E_CYL_METRIC_NECK = prove
 (`!s e. s < &1 ==> metric_field (rfs_neck_dom e) (cylinder_flow s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `(:real^3) DELETE vec 0` THEN
  REWRITE_TAC[APX_NECK_DOM_NONZERO; rfs_neck_dom; OPEN_ANNULUS] THEN
  MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REWRITE_TAC[]);;

let P3E_LCK_BOUND_NONNEG = prove
 (`!U (G0:real^N->real^N^N) G k y d.
     metric_field U G0 /\ metric_field U G /\ y IN U /\ lck_dist2 k G0 G y <= d
     ==> &0 <= d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 k (G0:real^N->real^N^N) G y` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3E_LCK_DIST2_POS THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P3E_NECKSEQ_ES_MNEAR = prove
 (`!(es:num->real) (Gs:num->real^3->real^3^3) ss s ds.
     (!n. &0 < es n /\ es n < &1) /\ ((\n. lift(es n)) --> vec 0) sequentially /\
     (!n. ss n < &1 /\ metric_field (rfs_neck_dom (es n)) (Gs n) /\
          &0 <= ds n /\ ds n < es n pow 2 /\
          !y. y IN rfs_neck_dom (es n)
              ==> lck_dist2 (rfs_kreg (es n)) (cylinder_flow (ss n)) (Gs n) y <= ds n) /\
     ((\n. lift(ss n)) --> lift s) sequentially /\ s < &1
     ==> !z. ~(z = vec 0) ==> p2cm_mnear z Gs (cylinder_flow s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MATCH_MP_TAC P3E_NECK_SEQ_MNEAR THEN
  MAP_EVERY EXISTS_TAC [`\n. rfs_neck_dom((es:num->real) n)`; `ss:num->real`;
                        `\n. rfs_kreg((es:num->real) n)`; `ds:num->real`;
                        `norm(z:real^3) / &2`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_CBALL; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `dist(z:real^3,vec 0) <= norm z / &2` THEN REWRITE_TAC[DIST_0] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`&1`; `es:num->real`] P3E_KREG_TENDSTO) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; REAL_LT_01];
    MATCH_MP_TAC P3E_ERR_NULL THEN MAP_EVERY EXISTS_TAC [`es:num->real`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; REAL_LT_01];
    MP_TAC(ISPECL [`es:num->real`; `norm(z:real^3) / &2`; `&3 / &2 * norm(z:real^3)`]
                  P3E_ANNULUS_NECK_DOM_ES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{w:real^3 | norm(z:real^3) / &2 <= norm w /\ norm w <= &3 / &2 * norm z}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
      CONV_TAC NORM_ARITH;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Sequences of gluing data.  Unpacking p3e_gdata (with                      *)
(* nonnegative error bounds), the later necks H_n(sig_n) converge to         *)
(* cyl(sig), the junction metrics P_n(-t0_n) converge to cyl(-t0), the       *)
(* curvature ratios r_n converge to 1/(1+t0), and the transition maps have   *)
(* a convergent subsequence at any nonzero point.                           *)
(* ------------------------------------------------------------------------- *)

let P3E_LIM_SCALE = prove
 (`!(xs:num->real) c.
     ((\n. lift(xs n)) --> vec 0) sequentially
     ==> ((\n. lift(xs n * c)) --> vec 0) sequentially`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
  SUBGOAL_THEN `vec 0:real^1 = c % vec 0` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[]);;

let P3E_BETA_EPS_LT = prove
 (`!eps beta.
     &0 < eps /\ eps < &1 /\ &0 < beta /\ beta < &1 / &2
     ==> beta * eps < &1 / &2 /\ beta * eps / &2 < &1 / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `beta * eps <= beta * &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3E_GDATA_UNPACK = prove
 (`!eps beta t0 r (P:real->real^3->real^3^3) H psi psi' yx.
     &0 < eps /\ &0 < beta /\ p3e_gdata eps beta t0 r P H psi psi' yx
     ==> ?dP dH.
         &0 < t0 /\ t0 < &1 /\ &0 < r /\ &0 < beta * eps /\ &0 < beta * eps / &2 /\
         open (rfs_neck_dom (beta * eps)) /\
         rfs_neck_dom (beta * eps) SUBSET (:real^3) DELETE vec 0 /\
         diffeomorphism_on (rfs_neck_dom (beta * eps)) (IMAGE psi (rfs_neck_dom (beta * eps)))
                           psi psi' /\
         IMAGE psi (rfs_neck_dom (beta * eps)) SUBSET rfs_neck_dom (beta * eps / &2) /\
         IMAGE psi (rfs_neck_dom (beta * eps)) SUBSET (:real^3) DELETE vec 0 /\
         norm yx = &1 /\ norm(psi yx) = &1 /\ yx IN rfs_neck_dom (beta * eps) /\
         (!s. --t0 <= s /\ s <= &0 ==> metric_field (rfs_neck_dom (beta * eps)) (P s)) /\
         &0 <= dP /\ dP < (beta * eps) pow 2 /\
         (!s y. --t0 < s /\ s <= &0 /\ y IN rfs_neck_dom (beta * eps)
                ==> lck_dist2 (rfs_kreg (beta * eps)) (cylinder_flow s) (P s) y <= dP) /\
         (!s. --(&1) < s /\ s <= &0 ==> metric_field (rfs_neck_dom (beta * eps / &2)) (H s)) /\
         &0 <= dH /\ dH < (beta * eps / &2) pow 2 /\
         (!s y. --(&1) < s /\ s <= &0 /\ y IN rfs_neck_dom (beta * eps / &2)
                ==> lck_dist2 (rfs_kreg (beta * eps / &2)) (cylinder_flow s) (H s) y <= dH) /\
         (!s y. --(&1) < s /\ s <= &0 /\ y IN rfs_neck_dom (beta * eps)
                ==> P (s / r - t0) y = inv r %% mpullback psi (H s) y) /\
         (!y. y IN rfs_neck_dom (beta * eps)
              ==> P (--t0) y = mpullback psi (\w. inv r %% H (&0) w) y) /\
         (!K m e. compact K /\ K SUBSET rfs_neck_dom (beta * eps) /\ &0 < e
                  ==> ?dl. &0 < dl /\
                           !s y l. --t0 < s /\ s < --t0 + dl /\ y IN K /\
                                   l IN pde_index_lists m (:3)
                                   ==> norm(iterated_partial l
                                              ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                               P s) y -
                                            iterated_partial l (vectorize o P (--t0)) y) < e) /\
         lscalar (P (--t0)) yx = r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3e_gdata] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < beta * eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < beta * eps / &2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(yx:real^3) IN rfs_neck_dom (beta * eps) /\ yx IN rfs_neck_dom (beta * eps / &2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t /\ x IN s ==> x IN t`) THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
    ASM_SIMP_TAC[P3E_UNIT_SPHERE_NECK_DOM; IN_SPHERE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (rfs_neck_dom (beta * eps)) ((P:real->real^3->real^3^3) (&0)) /\
    metric_field (rfs_neck_dom (beta * eps / &2)) ((H:real->real^3->real^3^3) (&0)) /\
    lck_dist2 (rfs_kreg (beta * eps)) (cylinder_flow (&0)) (P (&0)) yx <= d /\
    lck_dist2 (rfs_kreg (beta * eps / &2)) (cylinder_flow (&0)) (H (&0)) yx <= d'`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(rfs_neck_dom (beta * eps))` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->real^3) (rfs_neck_dom (beta * eps)) SUBSET
                (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `rfs_neck_dom (beta * eps / &2)` THEN
    ASM_REWRITE_TAC[APX_NECK_DOM_NONZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d /\ &0 <= d'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P3E_LCK_BOUND_NONNEG) THENL
     [MAP_EVERY EXISTS_TAC [`rfs_neck_dom (beta * eps)`; `cylinder_flow (&0)`;
                            `(P:real->real^3->real^3^3) (&0)`; `rfs_kreg (beta * eps)`;
                            `yx:real^3`];
      MAP_EVERY EXISTS_TAC [`rfs_neck_dom (beta * eps / &2)`; `cylinder_flow (&0)`;
                            `(H:real->real^3->real^3^3) (&0)`; `rfs_kreg (beta * eps / &2)`;
                            `yx:real^3`]] THEN
    ASM_SIMP_TAC[P3E_CYL_METRIC_NECK; REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN rfs_neck_dom (beta * eps)
        ==> (P:real->real^3->real^3^3) (--t0) y =
            mpullback (psi:real^3->real^3) (\w. inv r %% (H:real->real^3->real^3^3) (&0) w) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[P3E_MPULLBACK_CMUL; ETA_AX] THEN
    SUBGOAL_THEN `--t0 = &0 / r - t0` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `d':real`] THEN
  ASM_REWRITE_TAC[APX_NECK_DOM_NONZERO]);;

let P3E_GDATA_SEQ_TAC =
  SUBGOAL_THEN
   `!n. &0 < eps /\ &0 < (betas:num->real) n /\
        p3e_gdata eps (betas n) (t0s n) (rs n) ((Ps:num->real->real^3->real^3^3) n)
                  ((Hs:num->real->real^3->real^3^3) n) ((psis:num->real^3->real^3) n)
                  ((psis':num->real^3->real^3) n) ((yxs:num->real^3) n)`
  (X_CHOOSE_THEN `dP:num->real` (X_CHOOSE_THEN `dH:num->real` STRIP_ASSUME_TAC) o
   REWRITE_RULE[SKOLEM_THM; FORALL_AND_THM] o GEN `n:num` o
   MATCH_MP P3E_GDATA_UNPACK o SPEC `n:num`) THENL
  [ASM_REWRITE_TAC[]; ALL_TAC];;

let P3E_GDATA_H_MNEAR = prove
 (`!eps (betas:num->real) t0s rs (Ps:num->real->real^3->real^3^3) Hs psis psis' yxs sigs sig.
     &0 < eps /\ eps < &1 /\
     (!n. &0 < betas n /\ betas n < &1 / &2 /\
          p3e_gdata eps (betas n) (t0s n) (rs n) (Ps n) (Hs n) (psis n) (psis' n) (yxs n) /\
          --(&1) < sigs n /\ sigs n <= &0) /\
     ((\n. lift(betas n)) --> vec 0) sequentially /\
     ((\n. lift(sigs n)) --> lift sig) sequentially /\ sig < &1
     ==> !w. ~(w = vec 0) ==> p2cm_mnear w (\n. Hs n (sigs n)) (cylinder_flow sig)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN P3E_GDATA_SEQ_TAC THEN
  MATCH_MP_TAC P3E_NECKSEQ_ES_MNEAR THEN
  MAP_EVERY EXISTS_TAC [`\n. (betas:num->real) n * eps / &2`; `sigs:num->real`;
                        `dH:num->real`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`eps:real`; `(betas:num->real) n`] P3E_BETA_EPS_LT) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC P3E_LIM_SCALE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> x < &1`) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let P3E_GDATA_JUNCTION = prove
 (`!eps (betas:num->real) t0s rs (Ps:num->real->real^3->real^3^3) Hs psis psis' yxs t0.
     &0 < eps /\ eps < &1 /\
     (!n. &0 < betas n /\ betas n < &1 / &2 /\
          p3e_gdata eps (betas n) (t0s n) (rs n) (Ps n) (Hs n) (psis n) (psis' n) (yxs n)) /\
     ((\n. lift(betas n)) --> vec 0) sequentially /\
     ((\n. lift(t0s n)) --> lift t0) sequentially /\ &0 <= t0
     ==> !z. ~(z = vec 0) ==> p2cm_mnear z (\n. Ps n (--(t0s n))) (cylinder_flow (--t0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN P3E_GDATA_SEQ_TAC THEN
  SUBGOAL_THEN `!n. (betas:num->real) n < &1` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC(REAL_ARITH `x < &1 / &2 ==> x < &1`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P3E_JUNCTION_SEQ THEN
  MAP_EVERY EXISTS_TAC
   [`\n. rfs_kreg((betas:num->real) n * eps)`; `dP:num->real`;
    `\n. rfs_neck_dom((betas:num->real) n * eps)`;
    `\n. {z:real^3 | exp(--(inv(sqrt(&2) * (&2 * ((betas:num->real) n * eps))))) <= norm z /\
                     norm z <= exp(inv(sqrt(&2) * (&2 * (betas n * eps))))}`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3E_KREG_TENDSTO THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3E_ERR_NULL THEN
    MAP_EVERY EXISTS_TAC [`betas:num->real`; `eps:real`] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[P3E_ANNULUS_COMPACT] THEN
    MP_TAC(SPEC `(betas:num->real) n * eps` P3E_NECK_DOM_CLOSED) THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`z:real^3`; `r:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\n. &2 * ((betas:num->real) n * eps)`; `norm(z:real^3) - r`;
                   `norm(z:real^3) + r`] P3E_ANNULUS_NECK_DOM_ES) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[LIFT_CMUL] THEN
        SUBGOAL_THEN `vec 0:real^1 = &2 % vec 0` SUBST1_TAC THENL
         [REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
        MATCH_MP_TAC LIM_CMUL THEN MATCH_MP_TAC P3E_LIM_SCALE THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{w:real^3 | norm(z:real^3) - r <= norm w /\ norm w <= norm z + r}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
      CONV_TAC NORM_ARITH;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `rfs_neck_dom (&2 * ((betas:num->real) n * eps))` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MP_TAC(SPEC `(betas:num->real) n * eps` P3E_NECK_DOM_CLOSED) THEN ASM_SIMP_TAC[]]];
    ASM_REWRITE_TAC[]]);;

let P3E_GDATA_R_LIMIT = prove
 (`!eps (betas:num->real) t0s rs (Ps:num->real->real^3->real^3^3) Hs psis psis' yxs t0 yx0.
     &0 < eps /\ eps < &1 /\
     (!n. &0 < betas n /\ betas n < &1 / &2 /\
          p3e_gdata eps (betas n) (t0s n) (rs n) (Ps n) (Hs n) (psis n) (psis' n) (yxs n)) /\
     ((\n. lift(betas n)) --> vec 0) sequentially /\
     ((\n. lift(t0s n)) --> lift t0) sequentially /\ &0 <= t0 /\
     (yxs --> yx0) sequentially /\ ~(yx0 = vec 0)
     ==> ((\n. lift(rs n)) --> lift(inv(&1 + t0))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN P3E_GDATA_SEQ_TAC THEN
  SUBGOAL_THEN `p2cm_mnear (yx0:real^3) (\n. (Ps:num->real->real^3->real^3^3) n (--(t0s n)))
                           (cylinder_flow (--t0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`eps:real`; `betas:num->real`; `t0s:num->real`; `rs:num->real`;
                   `Ps:num->real->real^3->real^3^3`; `Hs:num->real->real^3->real^3^3`;
                   `psis:num->real^3->real^3`; `psis':num->real^3->real^3`;
                   `yxs:num->real^3`; `t0:real`] P3E_GDATA_JUNCTION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`yx0:real^3`;
                 `\(n:num) (z:real^3). lift(lscalar ((Ps:num->real->real^3->real^3^3) n
                                                       (--(t0s n))) z)`;
                 `\z:real^3. lift(lscalar (cylinder_flow (--t0)) z)`; `yxs:num->real^3`]
                P3E_NEAR_SEQ_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`yx0:real^3`; `\n. (Ps:num->real->real^3->real^3^3) n (--(t0s n))`;
                   `cylinder_flow (--t0)`] P3E_MNEAR_LSCALAR) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `lscalar (cylinder_flow (--t0)) (yx0:real^3) = inv(&1 + t0)` SUBST1_TAC THENL
   [MP_TAC(SPECL [`--t0`; `yx0:real^3`] RFB_CYL_SCALAR) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LID; REAL_SUB_RNEG];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let P3E_GDATA_PSI = prove
 (`!eps (betas:num->real) t0s rs (Ps:num->real->real^3->real^3^3) Hs psis psis' yxs t0 yx0
    (y0:real^3).
     &0 < eps /\ eps < &1 /\
     (!n. &0 < betas n /\ betas n < &1 / &2 /\
          p3e_gdata eps (betas n) (t0s n) (rs n) (Ps n) (Hs n) (psis n) (psis' n) (yxs n)) /\
     ((\n. lift(betas n)) --> vec 0) sequentially /\
     ((\n. lift(t0s n)) --> lift t0) sequentially /\ &0 <= t0 /\ t0 <= &1 /\
     (yxs --> yx0) sequentially /\ ~(yx0 = vec 0) /\ ~(y0 = vec 0)
     ==> ?sub psi. (!m n. m < n ==> sub m < sub n) /\
                   p2ci_near y0 (\n. psis (sub n)) psi /\ ~(psi y0 = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN P3E_GDATA_SEQ_TAC THEN
  SUBGOAL_THEN `!n. (betas:num->real) n < &1 /\ (dH:num->real) n < (betas n * eps) pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&0 < (betas:num->real) n` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x < &1 / &2 ==> x < &1`) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `((betas:num->real) n * eps / &2) pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`psis:num->real^3->real^3`; `psis':num->real^3->real^3`;
                 `\n. rfs_neck_dom((betas:num->real) n * eps)`;
                 `\n. (Ps:num->real->real^3->real^3^3) n (--(t0s n))`;
                 `\n. (Hs:num->real->real^3->real^3^3) n (&0)`;
                 `rs:num->real`; `inv(&1 + t0)`; `t0:real`; `y0:real^3`; `yxs:num->real^3`;
                 `dH:num->real`] P3E_PSI_SUBSEQ) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&0 < (t0s:num->real) n /\
                  IMAGE ((psis:num->real^3->real^3) n) (rfs_neck_dom ((betas:num->real) n * eps))
                  SUBSET rfs_neck_dom (betas n * eps / &2) /\
                  open(IMAGE ((psis:num->real^3->real^3) n) (rfs_neck_dom ((betas:num->real) n * eps)))`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `rfs_neck_dom ((betas:num->real) n * eps / &2)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg ((betas:num->real) n * eps / &2)) (cylinder_flow (&0))
                    ((Hs:num->real->real^3->real^3^3) n (&0)) w` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LCK_DIST_MONO THEN
        EXISTS_TAC `rfs_neck_dom ((betas:num->real) n * eps / &2)` THEN
        REWRITE_TAC[LE_0] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC P3E_CYL_METRIC_NECK THEN REAL_ARITH_TAC;
          FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
          ASM SET_TAC[]];
        FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ASM SET_TAC[]]]];
    MP_TAC(ISPECL [`eps:real`; `betas:num->real`; `t0s:num->real`; `rs:num->real`;
                   `Ps:num->real->real^3->real^3^3`; `Hs:num->real->real^3->real^3^3`;
                   `psis:num->real^3->real^3`; `psis':num->real^3->real^3`;
                   `yxs:num->real^3`; `t0:real`] P3E_GDATA_JUNCTION) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`eps:real`; `betas:num->real`; `t0s:num->real`; `rs:num->real`;
                   `Ps:num->real->real^3->real^3^3`; `Hs:num->real->real^3->real^3^3`;
                   `psis:num->real^3->real^3`; `psis':num->real^3->real^3`;
                   `yxs:num->real^3`; `\n:num. &0`; `&0`] P3E_GDATA_H_MNEAR) THEN
    REWRITE_TAC[LIM_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    MATCH_MP_TAC P3E_ERR_NULL THEN
    MAP_EVERY EXISTS_TAC [`betas:num->real`; `eps:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3E_GDATA_R_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `betas:num->real`; `t0s:num->real`;
                          `Ps:num->real->real^3->real^3^3`; `Hs:num->real->real^3->real^3^3`;
                          `psis:num->real^3->real^3`; `psis':num->real^3->real^3`;
                          `yxs:num->real^3`; `yx0:real^3`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\n. (betas:num->real) n * eps`; `a:real`; `b:real`]
                  P3E_ANNULUS_NECK_DOM_ES) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P3E_LIM_SCALE THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The core of Lemma B.  Along a sequence of gluing data with                *)
(* beta_n -> 0, earlier times s_n in (-1,-t0_n] and points y_n converging   *)
(* to y0 <> 0, the metrics P_n(s_n) are (along a subsequence) the pullbacks *)
(* inv(r_n) psi_n^* H_n(sig_n), sig_n = r_n (s_n + t0_n), which converge to *)
(* cyl(s0) near y0 by the rigidity of the cylinder (P3E_CYL_PULLBACK_LIMIT). *)
(* So the lck distance to the cylinder at (s_n,y_n) tends to 0.             *)
(* ------------------------------------------------------------------------- *)

let P3E_SIG_ARITH = prove
 (`!r t0 s. &0 < r /\ r * (&1 - t0) < &1 /\ --(&1) < s /\ s <= --t0
            ==> --(&1) < r * (s + t0) /\ r * (s + t0) <= &0 /\
                (r * (s + t0)) / r - t0 = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < r * (s + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `r * (&1 - t0) < &1` THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 <= r * --(s + t0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `~(r = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD]);;

let P3E_LIM_BOUNDS = prove
 (`!(xs:num->real) l a b.
     ((\n. lift(xs n)) --> lift l) sequentially /\ (!n. a <= xs n /\ xs n <= b)
     ==> a <= l /\ l <= b`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`sequentially`; `\n. lift((xs:num->real) n)`; `lift l`; `a:real`]
                  LIM_DROP_LBOUND);
    MP_TAC(ISPECL [`sequentially`; `\n. lift((xs:num->real) n)`; `lift l`; `b:real`]
                  LIM_DROP_UBOUND)] THEN
  ASM_REWRITE_TAC[LIFT_DROP; TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE]);;

let P3E_GDATA_C2_CORE = prove
 (`!eps (betas:num->real) t0s rs (Ps:num->real->real^3->real^3^3) Hs psis psis' yxs
    ss (ys:num->real^3) t0 s0 y0 yx0.
     &0 < eps /\ eps < &1 /\
     (!n. &0 < betas n /\ betas n < &1 / &2 /\
          p3e_gdata eps (betas n) (t0s n) (rs n) (Ps n) (Hs n) (psis n) (psis' n) (yxs n) /\
          rs n * (&1 - t0s n) < &1 /\ --(&1) < ss n /\ ss n <= --(t0s n)) /\
     ((\n. lift(betas n)) --> vec 0) sequentially /\
     ((\n. lift(t0s n)) --> lift t0) sequentially /\
     ((\n. lift(ss n)) --> lift s0) sequentially /\
     (ys --> y0) sequentially /\ ~(y0 = vec 0) /\
     (yxs --> yx0) sequentially /\ ~(yx0 = vec 0)
     ==> ?n. lck_dist2 (rfs_kreg eps) (cylinder_flow (ss n)) (Ps n (ss n)) (ys n) <
             eps pow 2 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN P3E_GDATA_SEQ_TAC THEN
  SUBGOAL_THEN `&0 < norm(y0:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  (* bounds of the limit times *)
  SUBGOAL_THEN `&0 <= t0 /\ t0 <= &1` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_LIM_BOUNDS THEN EXISTS_TAC `t0s:num->real` THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. lift((ss:num->real) n + t0s n)) --> lift(s0 + t0)) sequentially`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--(&1) <= s0 + t0 /\ s0 + t0 <= &0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_LIM_BOUNDS THEN EXISTS_TAC `\n. (ss:num->real) n + t0s n` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `--(&1) < (ss:num->real) n /\ ss n <= --(t0s n) /\ &0 < t0s n`
    MP_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the rescaled later times sig_n *)
  ABBREV_TAC `sigs = \n. (rs:num->real) n * ((ss:num->real) n + t0s n)` THEN
  SUBGOAL_THEN `!n. --(&1) < (sigs:num->real) n /\ sigs n <= &0 /\
                    sigs n / rs n - t0s n = (ss:num->real) n`
  (LABEL_TAC "SIG") THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "sigs" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P3E_SIG_ARITH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. lift((rs:num->real) n)) --> lift(inv(&1 + t0))) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_GDATA_R_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `betas:num->real`; `t0s:num->real`;
                          `Ps:num->real->real^3->real^3^3`; `Hs:num->real->real^3->real^3^3`;
                          `psis:num->real^3->real^3`; `psis':num->real^3->real^3`;
                          `yxs:num->real^3`; `yx0:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. lift((sigs:num->real) n)) --> lift(inv(&1 + t0) * (s0 + t0))) sequentially`
  ASSUME_TAC THENL
   [EXPAND_TAC "sigs" THEN REWRITE_TAC[LIFT_CMUL; LIFT_ADD] THEN
    MATCH_MP_TAC LIM_MUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[o_DEF];
      MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&1 + t0) * (s0 + t0) <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a * --b ==> a * b <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the subsequence of transition maps at y0 *)
  MP_TAC(ISPECL [`eps:real`; `betas:num->real`; `t0s:num->real`; `rs:num->real`;
                 `Ps:num->real->real^3->real^3^3`; `Hs:num->real->real^3->real^3^3`;
                 `psis:num->real^3->real^3`; `psis':num->real^3->real^3`;
                 `yxs:num->real^3`; `t0:real`; `yx0:real^3`; `y0:real^3`] P3E_GDATA_PSI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `psi:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* a ball around y0 inside the domains *)
  MP_TAC(ISPECL [`\n. (betas:num->real) n * eps`; `norm(y0:real^3) / &2`;
                 `&3 / &2 * norm(y0:real^3)`] P3E_ANNULUS_NECK_DOM_ES) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3E_LIM_SCALE THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_TAC `N0:num`)] THEN
  SUBGOAL_THEN `!n. N0 <= n ==> ball(y0:real^3,norm y0 / &2) SUBSET
                                rfs_neck_dom ((betas:num->real) ((sub:num->num) n) * eps)`
  (LABEL_TAC "BALL") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{z:real^3 | norm(y0:real^3) / &2 <= norm z /\ norm z <= &3 / &2 * norm y0}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
      CONV_TAC NORM_ARITH;
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the inputs of the pullback limit *)
  SUBGOAL_THEN
   `?r N. &0 < r /\
          !n. N <= n
              ==> ball(y0:real^3,r) SUBSET
                  rfs_neck_dom ((betas:num->real) ((sub:num->num) n) * eps) /\
                  !z. z IN ball(y0,r)
                      ==> (Ps:num->real->real^3->real^3^3) (sub n) (--(t0s (sub n))) z =
                          inv((rs:num->real) (sub n)) %%
                          mpullback ((psis:num->real^3->real^3) (sub n))
                                    ((Hs:num->real->real^3->real^3^3) (sub n) (&0)) z`
  ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`norm(y0:real^3) / &2`; `N0:num`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "BALL" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM P3E_MPULLBACK_CMUL] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2cm_mnear (y0:real^3)
                  (\n. (Ps:num->real->real^3->real^3^3) ((sub:num->num) n) (--(t0s (sub n))))
                  (cylinder_flow (--t0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y0:real^3`; `\n. (Ps:num->real->real^3->real^3^3) n (--(t0s n))`;
                   `cylinder_flow (--t0)`; `sub:num->num`] P3E_MNEAR_SUBSEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`eps:real`; `betas:num->real`; `t0s:num->real`; `rs:num->real`;
                   `Ps:num->real->real^3->real^3^3`; `Hs:num->real->real^3->real^3^3`;
                   `psis:num->real^3->real^3`; `psis':num->real^3->real^3`;
                   `yxs:num->real^3`; `t0:real`] P3E_GDATA_JUNCTION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!sgs sg. (!n. --(&1) < sgs n /\ sgs n <= &0) /\
             ((\n. lift(sgs n)) --> lift sg) sequentially /\ sg < &1
             ==> p2ci_near ((psi:real^3->real^3) y0)
                   (\n. (vectorize:real^3^3->real^(3,3)finite_prod) o
                        (Hs:num->real->real^3->real^3^3) ((sub:num->num) n) (sgs (sub n)))
                   (vectorize o cylinder_flow sg)`
  (LABEL_TAC "HL") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`eps:real`; `betas:num->real`; `t0s:num->real`; `rs:num->real`;
                   `Ps:num->real->real^3->real^3^3`; `Hs:num->real->real^3->real^3^3`;
                   `psis:num->real^3->real^3`; `psis':num->real^3->real^3`;
                   `yxs:num->real^3`; `sgs:num->real`; `sg:real`] P3E_GDATA_H_MNEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `(psi:real^3->real^3) y0`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o REWRITE_RULE[p2cm_mnear]) THEN
    DISCH_THEN(MP_TAC o SPEC `sub:num->num` o
               MATCH_MP (REWRITE_RULE[IMP_CONJ] P3E_NEAR_SUBSEQ)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2ci_near ((psi:real^3->real^3) y0)
                  (\n. (vectorize:real^3^3->real^(3,3)finite_prod) o
                       (Hs:num->real->real^3->real^3^3) ((sub:num->num) n) (&0))
                  (vectorize o cylinder_flow (&0))` ASSUME_TAC THENL
   [USE_THEN "HL" (MP_TAC o SPECL [`\n:num. &0`; `&0`]) THEN
    REWRITE_TAC[LIM_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2ci_near ((psi:real^3->real^3) y0)
                  (\n. (vectorize:real^3^3->real^(3,3)finite_prod) o
                       (Hs:num->real->real^3->real^3^3) ((sub:num->num) n) (sigs (sub n)))
                  (vectorize o cylinder_flow (inv(&1 + t0) * (s0 + t0)))` ASSUME_TAC THENL
   [USE_THEN "HL" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. lift(inv((rs:num->real) ((sub:num->num) n)))) --> lift(&1 + t0))
                sequentially` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sequentially`; `\n. (rs:num->real) ((sub:num->num) n)`; `inv(&1 + t0)`]
                  LIM_INV) THEN
    REWRITE_TAC[o_DEF; REAL_INV_INV] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\n. lift((rs:num->real) n)`; `sub:num->num`; `lift(inv(&1 + t0))`]
                    LIM_SUBSEQUENCE) THEN
      ASM_REWRITE_TAC[o_DEF];
      REWRITE_TAC[REAL_INV_EQ_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. lift((sigs:num->real) ((sub:num->num) n))) -->
                 lift(inv(&1 + t0) * (s0 + t0))) sequentially` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\n. lift((sigs:num->real) n)`; `sub:num->num`;
                   `lift(inv(&1 + t0) * (s0 + t0))`] LIM_SUBSEQUENCE) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < inv((rs:num->real) ((sub:num->num) n))` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--t0 < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the pullback limit *)
  MP_TAC(ISPECL
   [`\n. (psis:num->real^3->real^3) ((sub:num->num) n)`;
    `\n. (psis':num->real^3->real^3) ((sub:num->num) n)`;
    `\n. rfs_neck_dom((betas:num->real) ((sub:num->num) n) * eps)`;
    `\n. IMAGE ((psis:num->real^3->real^3) ((sub:num->num) n))
               (rfs_neck_dom((betas:num->real) (sub n) * eps))`;
    `psi:real^3->real^3`; `y0:real^3`;
    `\n. (Ps:num->real->real^3->real^3^3) ((sub:num->num) n) (--(t0s (sub n)))`;
    `\n. (Hs:num->real->real^3->real^3^3) ((sub:num->num) n) (&0)`;
    `\n. (Hs:num->real->real^3->real^3^3) ((sub:num->num) n) (sigs (sub n))`;
    `\n. inv((rs:num->real) ((sub:num->num) n))`; `&1 + t0`; `--t0`;
    `\n. (sigs:num->real) ((sub:num->num) n)`; `inv(&1 + t0) * (s0 + t0)`]
   P3E_CYL_PULLBACK_LIMIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--t0 + (&1 + t0) * (inv(&1 + t0) * (s0 + t0)) = s0` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(&1 + t0 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  DISCH_TAC THEN
  (* P_n(s_n) is that pullback near y0 *)
  SUBGOAL_THEN `p2ci_near (y0:real^3)
                  (\n. (vectorize:real^3^3->real^(3,3)finite_prod) o
                       (Ps:num->real->real^3->real^3^3) ((sub:num->num) n) (ss (sub n)))
                  (vectorize o cylinder_flow s0)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CI_NEAR_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`\n. (vectorize:real^3^3->real^(3,3)finite_prod) o
           (\z. inv((rs:num->real) ((sub:num->num) n)) %%
                mpullback ((psis:num->real^3->real^3) (sub n))
                          ((Hs:num->real->real^3->real^3^3) (sub n) (sigs (sub n))) z)`;
      `(vectorize:real^3^3->real^(3,3)finite_prod) o cylinder_flow s0`;
      `norm(y0:real^3) / &2`; `N0:num`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom ((betas:num->real) ((sub:num->num) n) * eps)`
    ASSUME_TAC THENL
     [USE_THEN "BALL" (MP_TAC o SPEC `n:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    USE_THEN "SIG" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV)
      [GSYM(CONJUNCT2(CONJUNCT2(SPEC `(sub:num->num) n` th)))]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "SIG" (MP_TAC o SPEC `(sub:num->num) n`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the lck distance to the cylinder tends to 0 at y_n *)
  MP_TAC(ISPECL [`y0:real^3`; `\n. cylinder_flow ((ss:num->real) ((sub:num->num) n))`;
                 `\n. (Ps:num->real->real^3->real^3^3) ((sub:num->num) n) (ss (sub n))`;
                 `cylinder_flow s0`; `rfs_kreg eps`] P2CM_LCK_NEAR2) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`y0:real^3`; `\n. (ss:num->real) ((sub:num->num) n)`; `s0:real`]
                  P3E_CYL_SEQ_MNEAR) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`\n. lift((ss:num->real) n)`; `sub:num->num`; `lift s0`]
                    LIM_SUBSEQUENCE) THEN
      ASM_REWRITE_TAC[o_DEF]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. (ys:num->real^3) ((sub:num->num) n)` o
             MATCH_MP (REWRITE_RULE[IMP_CONJ] P3E_NEAR_SEQ_POINT)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`ys:num->real^3`; `sub:num->num`; `y0:real^3`] LIM_SUBSEQUENCE) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0; NORM_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `eps pow 2 / &2`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `M:num`)) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_TAC THEN EXISTS_TAC `(sub:num->num) M` THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemma B (closeness on (-1,-t0] for some member of any                     *)
(* sequence of gluing data with beta_n -> 0 and r_n (1 - t0_n) < 1), the    *)
(* closeness on (-t0,0] from the evolving neck itself, and the abstract     *)
(* core of MT Prop 15.2: for each eps there is beta such that all gluing    *)
(* data satisfy r (1 - t0) < 1 and eps-closeness on (-1,0] x rfs_neck_dom   *)
(* eps.  Proof by contradiction with beta_n = 1/(n+3) (Lemmas A and B).     *)
(* ------------------------------------------------------------------------- *)

let P3E_GDATA_SEQ_C2 = prove
 (`!eps (betas:num->real) t0s rs (Ps:num->real->real^3->real^3^3) Hs psis psis' yxs.
     &0 < eps /\ eps < &1 /\
     (!n. &0 < betas n /\ betas n < &1 / &2 /\
          p3e_gdata eps (betas n) (t0s n) (rs n) (Ps n) (Hs n) (psis n) (psis' n) (yxs n) /\
          rs n * (&1 - t0s n) < &1) /\
     ((\n. lift(betas n)) --> vec 0) sequentially
     ==> ?n d. d < eps pow 2 /\
               !s y. --(&1) < s /\ s <= --(t0s n) /\ y IN rfs_neck_dom eps
                     ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s) (Ps n s) y <= d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN P3E_GDATA_SEQ_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!n. ?s y. --(&1) < s /\ s <= --((t0s:num->real) n) /\ y IN rfs_neck_dom eps /\
              eps pow 2 / &2 <
              lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                        ((Ps:num->real->real^3->real^3^3) n s) y`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `eps pow 2 / &2`]) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; DE_MORGAN_THM; REAL_NOT_LE; REAL_NOT_LT;
                GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC(TAUT `~a ==> a \/ b ==> b`) THEN REWRITE_TAC[REAL_NOT_LE] THEN
    MP_TAC(SPECL [`eps:real`; `2`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `ss:num->real` (X_CHOOSE_THEN `ys:num->real^3` (LABEL_TAC "BAD"))) THEN
  (* subsequence 1: the times t0 *)
  MP_TAC(ISPECL [`t0s:num->real`; `&0`; `&1`] P3E_SUBSEQ_REAL) THEN
  ANTS_TAC THENL [GEN_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `s1:num->num` STRIP_ASSUME_TAC)) THEN
  (* subsequence 2: the bad times *)
  MP_TAC(BETA_RULE(ISPECL [`\n. (ss:num->real) ((s1:num->num) n)`; `--(&1)`; `&0`]
                         P3E_SUBSEQ_REAL)) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "BAD" (MP_TAC o SPEC `(s1:num->num) n`) THEN
    SUBGOAL_THEN `&0 < (t0s:num->real) ((s1:num->num) n)` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `s2:num->num` STRIP_ASSUME_TAC)) THEN
  (* subsequence 3: the bad points, in the closed annulus *)
  MP_TAC(REWRITE_RULE[IN_ELIM_THM]
          (SPEC `\n. (ys:num->real^3) ((s1:num->num) ((s2:num->num) n))`
            (REWRITE_RULE[P3E_ANNULUS_COMPACT]
              (ISPEC `{z:real^3 | exp(--(inv(sqrt(&2) * eps))) <= norm z /\
                                  norm z <= exp(inv(sqrt(&2) * eps))}` compact)))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "BAD" (MP_TAC o SPEC `(s1:num->num) ((s2:num->num) n)`) THEN
    REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (X_CHOOSE_THEN `s3:num->num` STRIP_ASSUME_TAC)) THEN
  (* subsequence 4: the centre points *)
  MP_TAC(BETA_RULE(ISPEC
    `\n. (yxs:num->real^3) ((s1:num->num) ((s2:num->num) ((s3:num->num) n)))`
    P3E_SUBSEQ_SPHERE)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `yx0:real^3` (X_CHOOSE_THEN `s4:num->num` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `sub = \n. (s1:num->num) ((s2:num->num) ((s3:num->num) ((s4:num->num) n)))` THEN
  SUBGOAL_THEN `!m n. m < n ==> (sub:num->num) m < sub n` ASSUME_TAC THENL
   [EXPAND_TAC "sub" THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. lift((t0s:num->real) ((sub:num->num) n))) --> lift t0) sequentially /\
    ((\n. lift((ss:num->real) ((sub:num->num) n))) --> lift s0) sequentially /\
    ((\n. (ys:num->real^3) ((sub:num->num) n)) --> y0) sequentially /\
    ((\n. (yxs:num->real^3) ((sub:num->num) n)) --> yx0) sequentially`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sub" THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`\n. lift((t0s:num->real) ((s1:num->num) n))`;
                     `\n. (s2:num->num) ((s3:num->num) ((s4:num->num) n))`; `lift t0`]
                    LIM_SUBSEQUENCE) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`\n. lift((ss:num->real) ((s1:num->num) ((s2:num->num) n)))`;
                     `\n. (s3:num->num) ((s4:num->num) n)`; `lift s0`] LIM_SUBSEQUENCE) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`(\n. (ys:num->real^3) ((s1:num->num) ((s2:num->num) n))) o (s3:num->num)`;
                     `s4:num->num`; `y0:real^3`] LIM_SUBSEQUENCE) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y0:real^3 = vec 0) /\ ~(yx0:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THENL
     [MP_TAC(SPEC `--(inv(sqrt(&2) * eps))` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the core along the subsequence *)
  MP_TAC(ISPECL [`eps:real`; `\n. (betas:num->real) ((sub:num->num) n)`;
                 `\n. (t0s:num->real) ((sub:num->num) n)`; `\n. (rs:num->real) ((sub:num->num) n)`;
                 `\n. (Ps:num->real->real^3->real^3^3) ((sub:num->num) n)`;
                 `\n. (Hs:num->real->real^3->real^3^3) ((sub:num->num) n)`;
                 `\n. (psis:num->real^3->real^3) ((sub:num->num) n)`;
                 `\n. (psis':num->real^3->real^3) ((sub:num->num) n)`;
                 `\n. (yxs:num->real^3) ((sub:num->num) n)`;
                 `\n. (ss:num->real) ((sub:num->num) n)`;
                 `\n. (ys:num->real^3) ((sub:num->num) n)`;
                 `t0:real`; `s0:real`; `y0:real^3`; `yx0:real^3`] P3E_GDATA_C2_CORE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`betas:num->real`; `sub:num->num`] P3E_BETA_SUBSEQ) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  USE_THEN "BAD" (MP_TAC o SPEC `(sub:num->num) n`) THEN ASM_REAL_ARITH_TAC);;

let P3E_GDATA_LATE_CLOSE = prove
 (`!eps beta t0 r (P:real->real^3->real^3^3) H psi psi' yx.
     &0 < eps /\ eps < &1 /\ &0 < beta /\ beta < &1 / &2 /\
     p3e_gdata eps beta t0 r P H psi psi' yx
     ==> ?d. d < eps pow 2 /\
             !s y. --t0 < s /\ s <= &0 /\ y IN rfs_neck_dom eps
                   ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s) (P s) y <= d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`eps:real`; `beta:real`; `t0:real`; `r:real`; `P:real->real^3->real^3^3`;
                `H:real->real^3->real^3^3`; `psi:real^3->real^3`; `psi':real^3->real^3`;
                `yx:real^3`] P3E_GDATA_UNPACK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `beta * eps <= eps` ASSUME_TAC THENL
   [SUBGOAL_THEN `beta * eps <= &1 * eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `dP:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(beta * eps) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom (beta * eps)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`beta * eps`; `eps:real`] APX_NECK_DOM_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg (beta * eps)) (cylinder_flow s)
                        ((P:real->real^3->real^3^3) s) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom (beta * eps)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3E_CYL_METRIC_NECK THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P3E_GLUE_CORE = prove
 (`!eps. &0 < eps /\ eps < &1
         ==> ?beta. &0 < beta /\ beta < &1 / &2 /\
               !t0 r (P:real->real^3->real^3^3) H psi psi' yx.
                  p3e_gdata eps beta t0 r P H psi psi' yx
                  ==> r * (&1 - t0) < &1 /\
                      ?d. d < eps pow 2 /\
                          !s y. --(&1) < s /\ s <= &0 /\ y IN rfs_neck_dom eps
                                ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s) (P s) y <= d`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `!n. &0 < inv(&n + &3) /\ inv(&n + &3) < &1 / &2` (LABEL_TAC "BINV") THENL
   [X_GEN_TAC `n:num` THEN MP_TAC(SPEC `n:num` REAL_POS) THEN DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&1 / &2 = inv(&2)` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?t0 r (P:real->real^3->real^3^3) H psi psi' yx.
          p3e_gdata eps (inv(&n + &3)) t0 r P H psi psi' yx /\
          ~(r * (&1 - t0) < &1 /\
            ?d. d < eps pow 2 /\
                !s y. --(&1) < s /\ s <= &0 /\ y IN rfs_neck_dom eps
                      ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s) (P s) y <= d)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `inv(&n + &3)`) THEN
    MATCH_MP_TAC(TAUT `(a /\ b) /\ (~c ==> d) ==> ~(a /\ b /\ c) ==> d`) THEN
    CONJ_TAC THENL [USE_THEN "BINV" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0s:num->real` (X_CHOOSE_THEN `rs:num->real`
    (X_CHOOSE_THEN `Ps:num->real->real^3->real^3^3`
    (X_CHOOSE_THEN `Hs:num->real->real^3->real^3^3`
    (X_CHOOSE_THEN `psis:num->real^3->real^3` (X_CHOOSE_THEN `psis':num->real^3->real^3`
    (X_CHOOSE_THEN `yxs:num->real^3` (LABEL_TAC "DN")))))))) THEN
  SUBGOAL_THEN `((\n. lift(inv(&n + &3))) --> vec 0) sequentially` ASSUME_TAC THENL
   [REWRITE_TAC[SEQ_HARMONIC_OFFSET]; ALL_TAC] THEN
  (* Lemma A: r (1 - t0) < 1 for all large n *)
  SUBGOAL_THEN `?K. !n. K <= n ==> (rs:num->real) n * (&1 - t0s n) < &1`
  (X_CHOOSE_THEN `K:num` (LABEL_TAC "KA")) THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP]) THEN
    MP_TAC(BETA_RULE(ISPEC `\n. ~((rs:num->real) n * (&1 - t0s n) < &1)`
                            P2CI_SUBSEQ_CHOICE)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `sg:num->num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`eps:real`; `\n. inv(&((sg:num->num) n) + &3)`;
                   `\n. (t0s:num->real) ((sg:num->num) n)`;
                   `\n. (rs:num->real) ((sg:num->num) n)`;
                   `\n. (Ps:num->real->real^3->real^3^3) ((sg:num->num) n)`;
                   `\n. (Hs:num->real->real^3->real^3^3) ((sg:num->num) n)`;
                   `\n. (psis:num->real^3->real^3) ((sg:num->num) n)`;
                   `\n. (psis':num->real^3->real^3) ((sg:num->num) n)`;
                   `\n. (yxs:num->real^3) ((sg:num->num) n)`] P3E_GDATA_SEQ_C1) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\n. inv(&n + &3)`; `sg:num->num`] P3E_BETA_SUBSEQ) THEN
      REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* Lemma B along the shifted sequence *)
  MP_TAC(ISPECL [`eps:real`; `\n. inv(&(n + K) + &3)`;
                 `\n. (t0s:num->real) (n + K)`; `\n. (rs:num->real) (n + K)`;
                 `\n. (Ps:num->real->real^3->real^3^3) (n + K)`;
                 `\n. (Hs:num->real->real^3->real^3^3) (n + K)`;
                 `\n. (psis:num->real^3->real^3) (n + K)`;
                 `\n. (psis':num->real^3->real^3) (n + K)`;
                 `\n. (yxs:num->real^3) (n + K)`] P3E_GDATA_SEQ_C2) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN USE_THEN "KA" MATCH_MP_TAC THEN ARITH_TAC;
      MP_TAC(ISPECL [`\n. inv(&n + &3)`; `\n:num. n + K`] P3E_BETA_SUBSEQ) THEN
      REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `dB:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LB")))) THEN
  USE_THEN "DN" (MP_TAC o SPEC `n + K:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(SPECL [`eps:real`; `inv(&(n + K) + &3)`; `(t0s:num->real) (n + K)`;
                `(rs:num->real) (n + K)`; `(Ps:num->real->real^3->real^3^3) (n + K)`;
                `(Hs:num->real->real^3->real^3^3) (n + K)`;
                `(psis:num->real^3->real^3) (n + K)`; `(psis':num->real^3->real^3) (n + K)`;
                `(yxs:num->real^3) (n + K)`] P3E_GDATA_LATE_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `dL:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LL")))] THEN
  MATCH_MP_TAC(TAUT `a /\ b ==> ~(a /\ b) ==> F`) THEN CONJ_TAC THENL
   [USE_THEN "KA" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `max dB dL` THEN ASM_REWRITE_TAC[REAL_MAX_LT] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s <= --((t0s:num->real) (n + K))` THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN
    USE_THEN "LB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max a b`) THEN
    USE_THEN "LL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

