(* ========================================================================= *)
(* Unit pc_pde_mpar (the linear theory on M, fourth part): the parametrix    *)
(* for d/dt v = tr_k Hess_h v + F on a compact manifold: chart data (cover,  *)
(* cutoffs, partition, torus coefficients and solution operators), the       *)
(* families g, u, w, S F, R F, and the residual identity                     *)
(* (d/dt - tr_k Hess_h) S F = F - R F.                                       *)
(* ========================================================================= *)

needs "src/pc_pde_menergy.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The parametrix data.  A cover with cutoffs psi i supported in the pieces  *)
(* ks i, a partition chi i with psi i = 1 where chi i <> 0, dilations lam i, *)
(* torus coefficients on [0,b'-a) agreeing with the chart coefficients near  *)
(* ks i, and torus solution operators E i.                                   *)
(* ========================================================================= *)

let pde_mx_data = new_definition
 `pde_mx_data (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b'
              (k:real->A->real^N^N) (h:A->real^N^N) n0 (cs:num->(A->bool)#(A->real^N))
              (ks:num->real^N->bool) (psi:num->A->real) (chi:num->A->real) (lam:num->real)
              (aaT:num->real->real^N->real^N^N)
              (bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod)
              (ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod)
              (lamT:num->real)
              (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
  <=>
    a < b' /\
    pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
    (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
    (!i. i < n0 ==> mfd_smooth atlas (\x. lift(chi i x)) /\
                    (!x. ~(chi i x = &0) ==> psi i x = &1)) /\
    (!x. x IN topspace top ==> sum {i | i < n0} (\i. chi i x) = &1) /\
    (!i. i < n0 ==> &1 <= lam i /\ ks i SUBSET ball(vec 0,lam i / &4)) /\
    (!i. i < n0
         ==> pde_tcoeff (b' - a) (lamT i) (aaT i) (bbT i) (ccT i) /\
             ?V. open V /\ ks i SUBSET V /\ V SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
                 !t z. a <= t /\ t < b' /\ z IN V
                       ==> aaT i (t - a) (inv(lam i) % z + inv(&2) % vec 1) =
                             inv(lam i pow 2) %% pde_mlaa atlas (cs i) k t z /\
                           (!j. 1 <= j /\ j <= dimindex(:N)
                                ==> bbT i (t - a) (inv(lam i) % z + inv(&2) % vec 1) j =
                                    inv(lam i) %% pde_mlbt atlas (cs i) k h t z j) /\
                           ccT i (t - a) (inv(lam i) % z + inv(&2) % vec 1) =
                             pde_mlct atlas (cs i) k h t z) /\
    (!i g. i < n0 /\ pde_upto (&0) (b' - a) (:real^N) g /\ (!t. pde_zper (g t))
           ==> pde_tsol (b' - a) (aaT i) (bbT i) (ccT i) g (\x. vec 0) (E i g))`;;

let PDE_MX_DATA_EXISTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b b' (k:real->A->real^N^N) h.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ a < b' /\ b' < b
     ==> ?n0 cs ks psi chi lam aaT bbT ccT lamT E.
           pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                PDE_COVER_CUTOFFS_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `cs:num->(A->bool)#(A->real^N)`
    (X_CHOOSE_THEN `ks:num->real^N->bool` (X_CHOOSE_THEN `psi:num->A->real`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `psi:num->A->real`] PDM_CUTOFF_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `chi:num->A->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. i < n0 ==> (cs:num->(A->bool)#(A->real^N)) i IN atlas /\ compact((ks:num->real^N->bool) i) /\
                   ks i SUBSET IMAGE (SND(cs i)) (FST(cs i))`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                              (cs:num->(A->bool)#(A->real^N)) (ks:num->real^N->bool)`) THEN
    REWRITE_TAC[pde_cover] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?lam:num->real. !i. i < n0 ==> &1 <= lam i /\
                                   (ks:num->real^N->bool) i SUBSET ball(vec 0,lam i / &4)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i:num < n0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `bounded((ks:num->real^N->bool) i)` MP_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `&4 * R + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?aaT bbT ccT lamT.
      !i. i < n0
          ==> pde_tcoeff (b' - a) (lamT i) ((aaT:num->real->real^N->real^N^N) i)
                ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) i)
                ((ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) i) /\
              ?V. open V /\ (ks:num->real^N->bool) i SUBSET V /\
                  V SUBSET IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)) /\
                  !t z. a <= t /\ t < b' /\ z IN V
                        ==> aaT i (t - a) (inv((lam:num->real) i) % z + inv(&2) % vec 1) =
                              inv(lam i pow 2) %% pde_mlaa atlas (cs i) k t z /\
                            (!j. 1 <= j /\ j <= dimindex(:N)
                                 ==> bbT i (t - a) (inv(lam i) % z + inv(&2) % vec 1) j =
                                     inv(lam i) %% pde_mlbt atlas (cs i) k h t z j) /\
                            ccT i (t - a) (inv(lam i) % z + inv(&2) % vec 1) =
                              pde_mlct atlas (cs i) k h t z`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i:num < n0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                   `(cs:num->(A->bool)#(A->real^N)) i`; `(ks:num->real^N->bool) i`;
                   `(lam:num->real) i`] PDE_MT_TORUS_COEFF) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `aa:real->real^N->real^N^N` (X_CHOOSE_THEN
      `bb:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod` (X_CHOOSE_THEN
      `cc:real->real^N->real^(N,N)finite_prod^(N,N)finite_prod` (X_CHOOSE_THEN `lt:real`
      (X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC))))) THEN
    MAP_EVERY EXISTS_TAC [`aa:real->real^N->real^N^N`;
                          `bb:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `cc:real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`; `lt:real`] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `V:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?E. !i (g:real->real^N->real^(N,N)finite_prod).
          i < n0 /\ pde_upto (&0) (b' - a) (:real^N) g /\ (!t. pde_zper (g t))
          ==> pde_tsol (b' - a) ((aaT:num->real->real^N->real^N^N) i)
                ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) i)
                ((ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) i) g
                (\x. vec 0) (E i g)`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i:num < n0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_MT_TSOL_OP THEN EXISTS_TAC `(lamT:num->real) i` THEN
    ASM_SIMP_TAC[REAL_SUB_LT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`n0:num`; `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
    `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
    `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
    `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`; `lamT:num->real`;
    `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`] THEN
  ASM_SIMP_TAC[pde_mx_data] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `L:A->bool` (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* The families of the parametrix and their regularity.  For an M-family Fm: *)
(* the torus forcings g i Fm (transplant of the chart representative of      *)
(* chi_i Fm), the torus solutions u i Fm = E i (g i Fm), their untransplants *)
(* w i Fm to chart i, the commutators comm i Fm, and the M-families S Fm,    *)
(* R Fm (sums of chart fields).                                              *)
(* ========================================================================= *)

let pde_mx_psic = new_definition
 `pde_mx_psic (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real) i (z:real^N) =
    if z IN IMAGE (SND(cs i)) (FST(cs i)) then psi i (chart_inv (cs i) z) else &0`;;

let pde_mx_g = new_definition
 `pde_mx_g (atlas:((A->bool)#(A->real^N))->bool) a (cs:num->(A->bool)#(A->real^N))
           (chi:num->A->real) (lam:num->real) i (Fm:real->A->real^N^N) (tau:real) =
    pdm_transplant (lam i)
      (\z. pde_mx_psic cs chi i z %
           (vectorize:real^N^N->real^(N,N)finite_prod) (metric_local atlas (cs i) (Fm (tau + a)) z))`;;

let pde_mx_u = new_definition
 `pde_mx_u (atlas:((A->bool)#(A->real^N))->bool) a (cs:num->(A->bool)#(A->real^N))
           (chi:num->A->real) (lam:num->real)
           (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
           i (Fm:real->A->real^N^N) =
    E i (pde_mx_g atlas a cs chi lam i Fm)`;;

let pde_mx_w = new_definition
 `pde_mx_w (atlas:((A->bool)#(A->real^N))->bool) a (cs:num->(A->bool)#(A->real^N))
           (chi:num->A->real) (lam:num->real)
           (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
           i (Fm:real->A->real^N^N) (t:real) (z:real^N) =
    pde_mx_u atlas a cs chi lam E i Fm (t - a) (inv(lam i) % z + inv(&2) % vec 1)`;;

let pde_mx_comm = new_definition
 `pde_mx_comm (atlas:((A->bool)#(A->real^N))->bool) a (k:real->A->real^N^N) (h:A->real^N^N)
              (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real) (chi:num->A->real)
              (lam:num->real)
              (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
              i (Fm:real->A->real^N^N) (t:real) (z:real^N) =
    pde_mt_comm (pde_mlaa atlas (cs i) k t) (pde_mlbt atlas (cs i) k h t)
                (\z. lift(pde_mx_psic cs psi i z)) (pde_mx_w atlas a cs chi lam E i Fm t) z`;;

let pde_mx_s = new_definition
 `pde_mx_s (atlas:((A->bool)#(A->real^N))->bool) a (cs:num->(A->bool)#(A->real^N))
           (psi:num->A->real) (chi:num->A->real) (lam:num->real)
           (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
           n0 (Fm:real->A->real^N^N) (t:real) (x:A) =
    (matrify:real^(N,N)finite_prod->real^N^N)
     (vsum {i | i < n0}
       (\i. (vectorize:real^N^N->real^(N,N)finite_prod)
              (pdm_chart_field atlas (cs i)
                 (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                        (pde_mx_psic cs psi i z % pde_mx_w atlas a cs chi lam E i Fm t z)) x)))`;;

let pde_mx_r = new_definition
 `pde_mx_r (atlas:((A->bool)#(A->real^N))->bool) a (k:real->A->real^N^N) (h:A->real^N^N)
           (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real) (chi:num->A->real)
           (lam:num->real)
           (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
           n0 (Fm:real->A->real^N^N) (t:real) (x:A) =
    (matrify:real^(N,N)finite_prod->real^N^N)
     (vsum {i | i < n0}
       (\i. (vectorize:real^N^N->real^(N,N)finite_prod)
              (pdm_chart_field atlas (cs i)
                 (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                        (pde_mx_comm atlas a k h cs psi chi lam E i Fm t z)) x)))`;;

(* Chart representatives of cutoffs. *)

let PDE_MX_PSIC_SMOOTH = prove
 (`!top atlas n0 (cs:num->(A->bool)#(A->real^N)) ks (phi:num->A->real) i.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\ i < n0 /\
     mfd_smooth atlas (\x. lift(phi i x)) /\
     (!x. ~(phi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i))
     ==> smooth_map_on (:real^N) (\z. lift(pde_mx_psic cs phi i z)) /\
         (!z. ~(z IN ks i) ==> pde_mx_psic cs phi i z = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pde_mx_psic] THEN
  MATCH_MP_TAC PDE_ME_CUTOFF_CHART THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                 (cs:num->(A->bool)#(A->real^N)) ks` THEN
  REWRITE_TAC[pde_cover] THEN ASM_SIMP_TAC[]);;

let PDE_MX_DATA_PSIC = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E i.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ i < n0
     ==> smooth_map_on (:real^N) (\z. lift(pde_mx_psic cs psi i z)) /\
         (!z. ~(z IN ks i) ==> pde_mx_psic cs psi i z = &0) /\
         smooth_map_on (:real^N) (\z. lift(pde_mx_psic cs chi i z)) /\
         (!z. ~(z IN ks i) ==> pde_mx_psic cs chi i z = &0) /\
         (!z. ~(pde_mx_psic cs chi i z = &0) ==> pde_mx_psic cs psi i z = &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_mx_data] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_cutoffs (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0 cs psi`
    MP_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[pde_cutoffs]] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. ~((chi:num->A->real) i x = &0)
                    ==> x IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) i)) (ks i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th))) THEN
    ASM_SIMP_TAC[REAL_ARITH `~(&1 = &0)`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `i:num`] PDE_MX_PSIC_SMOOTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `chi:num->A->real`;
                 `i:num`] PDE_MX_PSIC_SMOOTH) THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[pde_mx_psic] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* Closure of pde_upto and of time families under finite sums. *)

let PDE_MX_UPTO_VSUM = prove
 (`!a b (U:real^N->bool) (f:B->real->real^N->real^K) s.
     open U /\ FINITE s /\ (!i. i IN s ==> pde_upto a b U (f i))
     ==> pde_upto a b U (\t x. vsum s (\i. f i t x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  SPEC_TAC(`s:B->bool`,`s:B->bool`) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; PDE_MT_UPTO_CONST_OPEN; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_MT_UPTO_ADD_OPEN THEN
  ASM_SIMP_TAC[ETA_AX]);;

let PDE_MX_TFAM_ADD = prove
 (`!top atlas a b (v:real->A->real^N^N) w.
     smooth_manifold_atlas top atlas /\
     pde_tfam_from atlas a b v /\ pde_tfam_from atlas a b w
     ==> pde_tfam_from atlas a b (\t x. v t x + w t x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`)) THEN
  ASM_REWRITE_TAC[METRIC_LOCAL_ADD; VECTORIZE_ADD; ETA_AX] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC PDE_MT_UPTO_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PDM_CHART_OPEN_C]);;

let PDE_MX_TFAM_VSUM = prove
 (`!top atlas a b (v:B->real->A->real^N^N) s.
     smooth_manifold_atlas top atlas /\ FINITE s /\
     (!i. i IN s ==> pde_tfam_from atlas a b (v i))
     ==> pde_tfam_from atlas a b
           (\t x. (matrify:real^(N,N)finite_prod->real^N^N)
                    (vsum s (\i. (vectorize:real^N^N->real^(N,N)finite_prod) (v i t x))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  SPEC_TAC(`s:B->bool`,`s:B->bool`) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[VSUM_CLAUSES; MATRIFY_0; PDE_ME_TFAM_ZERO; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VSUM_CLAUSES; MATRIFY_ADD; MATRIFY_VECTORIZE] THEN
  MATCH_MP_TAC PDE_MX_TFAM_ADD THEN EXISTS_TAC `top:A topology` THEN
  ASM_SIMP_TAC[ETA_AX]);;

(* Sums of chart fields of chart families supported in the pieces. *)

let PDE_MX_CHART_SUM_TFAM = prove
 (`!top atlas a b n0 (cs:num->(A->bool)#(A->real^N)) ks (Y:num->real->real^N->real^N^N).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     (!i. i < n0 ==> cs i IN atlas /\ compact(ks i) /\ ks i SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
                     pde_upto a b (IMAGE (SND(cs i)) (FST(cs i)))
                       (\t z. (vectorize:real^N^N->real^(N,N)finite_prod) (Y i t z)) /\
                     (!t z. a <= t /\ t < b /\ z IN IMAGE (SND(cs i)) (FST(cs i)) /\
                            ~(z IN ks i) ==> Y i t z = mat 0))
     ==> pde_tfam_from atlas a b
           (\t x. (matrify:real^(N,N)finite_prod->real^N^N)
                    (vsum {i | i < n0}
                       (\i. (vectorize:real^N^N->real^(N,N)finite_prod)
                              (pdm_chart_field atlas (cs i) (Y i t) x))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `\i t. pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) i)
                          ((Y:num->real->real^N->real^N^N) i t)`;
                 `{i:num | i < n0}`] PDE_MX_TFAM_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC PDM_CHART_FIELD_TFAM THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `(ks:num->real^N->bool) i`] THEN
  ASM_SIMP_TAC[]);;

(* The torus forcings, solutions and untransplants. *)

let PDE_MX_CUT_UPTO = prove
 (`!top atlas a b n0 (cs:num->(A->bool)#(A->real^N)) ks (phi:num->A->real) i
    (Fm:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\ i < n0 /\
     smooth_map_on (:real^N) (\z. lift(pde_mx_psic cs phi i z)) /\
     (!z. ~(z IN ks i) ==> pde_mx_psic cs phi i z = &0) /\
     pde_tfam_from atlas a b Fm
     ==> pde_upto a b (:real^N)
           (\t z. pde_mx_psic cs phi i z %
                  (vectorize:real^N^N->real^(N,N)finite_prod)
                    (metric_local atlas (cs i) (Fm t) z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\ compact((ks:num->real^N->bool) i) /\
                ks i SUBSET IMAGE (SND(cs i)) (FST(cs i))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                   (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`;
                 `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                             ((Fm:real->A->real^N^N) t) z)`;
                 `pde_mx_psic (cs:num->(A->bool)#(A->real^N)) (phi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`] PDM_UPTO_CUTOFF_EXT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[PDM_CHART_OPEN_C];
      UNDISCH_TAC `pde_tfam_from atlas a b (Fm:real->A->real^N^N)` THEN
      REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[pde_mx_psic; VECTOR_MUL_LZERO]);;

let PDE_MX_G_UPTO = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E i Fm.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ i < n0 /\
     pde_tfam_from atlas a b' Fm
     ==> pde_upto (&0) (b' - a) (:real^N) (pde_mx_g atlas a cs chi lam i Fm) /\
         (!tau. pde_zper (pde_mx_g atlas a cs chi lam i Fm tau))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`] PDE_MX_DATA_PSIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_mx_data]) THEN
  SUBGOAL_THEN `pde_mx_g atlas a cs chi lam i (Fm:real->A->real^N^N) =
                (\tau. pdm_transplant ((lam:num->real) i)
                         ((\s z. pde_mx_psic (cs:num->(A->bool)#(A->real^N)) chi i z %
                                 (vectorize:real^N^N->real^(N,N)finite_prod)
                                   (metric_local atlas (cs i) (Fm (s + a)) z)) tau))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_mx_g]; ALL_TAC] THEN BETA_TAC THEN
  MATCH_MP_TAC PDM_TRANSPLANT_UPTO THEN EXISTS_TAC `(ks:num->real^N->bool) i` THEN
  SUBGOAL_THEN `&1 <= (lam:num->real) i /\ (ks:num->real^N->bool) i SUBSET ball(vec 0,lam i / &4)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compact((ks:num->real^N->bool) i)` ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                   (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`a:real`; `b':real`; `(:real^N)`;
                   `\t z. pde_mx_psic (cs:num->(A->bool)#(A->real^N)) chi i z %
                          (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas (cs i) ((Fm:real->A->real^N^N) t) z)`;
                   `a:real`] PDE_MT_UPTO_SHIFT) THEN
    REWRITE_TAC[OPEN_UNIV; REAL_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC PDE_MX_CUT_UPTO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `n0:num`; `ks:num->real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]]);;

let PDE_MX_U_TSOL = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E i Fm.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ i < n0 /\
     pde_tfam_from atlas a b' Fm
     ==> pde_tsol (b' - a) (aaT i) (bbT i) (ccT i) (pde_mx_g atlas a cs chi lam i Fm)
                  (\x. vec 0) (pde_mx_u atlas a cs chi lam E i Fm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pde_mx_u] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`; `Fm:real->A->real^N^N`] PDE_MX_G_UPTO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `pde_mx_data (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b'
                 (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E` THEN
  REWRITE_TAC[pde_mx_data] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let PDE_MX_W_UPTO = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E i Fm.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ i < n0 /\
     pde_tfam_from atlas a b' Fm
     ==> pde_upto a b' (:real^N) (pde_mx_w atlas a cs chi lam E i Fm) /\
         (!z. pde_mx_w atlas a cs chi lam E i Fm a z = vec 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PDE_MX_U_TSOL) THEN REWRITE_TAC[pde_tsol] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[pde_mx_w; REAL_SUB_REFL]] THEN
  MP_TAC(ISPECL [`&0`; `b' - a`;
                 `pde_mx_u atlas a cs chi lam
                    (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                       real^(N,N)finite_prod) i (Fm:real->A->real^N^N)`;
                 `inv((lam:num->real) i)`; `inv(&2) % vec 1:real^N`] PDM_UPTO_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`&0`; `b' - a`; `(:real^N)`;
                 `\t x. pde_mx_u atlas a cs chi lam
                          (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                             real^(N,N)finite_prod) i (Fm:real->A->real^N^N) t
                          (inv((lam:num->real) i) % x + inv(&2) % vec 1)`;
                 `--a:real`] PDE_MT_UPTO_SHIFT) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; REAL_ARITH `&0 - --a = a /\ (b' - a) - --a = b'`] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; pde_mx_w; GSYM real_sub]);;

let PDE_MX_S_TFAM = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E Fm.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' Fm
     ==> pde_tfam_from atlas a b' (pde_mx_s atlas a cs psi chi lam E n0 Fm)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pde_mx_s atlas a cs psi chi lam E n0 (Fm:real->A->real^N^N) =
                (\t x. (matrify:real^(N,N)finite_prod->real^N^N)
                    (vsum {i | i < n0}
                       (\i. (vectorize:real^N^N->real^(N,N)finite_prod)
                              (pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                 ((\i t z. (matrify:real^(N,N)finite_prod->real^N^N)
                                     (pde_mx_psic cs psi i z % pde_mx_w atlas a cs chi lam E i Fm t z))
                                  i t) x))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_mx_s]; ALL_TAC] THEN
  MATCH_MP_TAC PDE_MX_CHART_SUM_TFAM THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`] PDE_MX_DATA_PSIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`; `Fm:real->A->real^N^N`] PDE_MX_W_UPTO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\ compact((ks:num->real^N->bool) i) /\
                ks i SUBSET IMAGE (SND(cs i)) (FST(cs i))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_mx_data (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b'
                   (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E` THEN
    REWRITE_TAC[pde_mx_data; pde_cover] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTORIZE_MATRIFY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_MT_UPTO_SCALAR_MUL_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_MT_UPTO_TIME_CONST THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC PDE_MT_UPTO_OPEN_SUBSET THEN
      EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO; MATRIFY_0]]);;

let PDE_MX_R_TFAM = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E Fm.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' <= b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' Fm
     ==> pde_tfam_from atlas a b' (pde_mx_r atlas a k h cs psi chi lam E n0 Fm)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pde_mx_r atlas a k h cs psi chi lam E n0 (Fm:real->A->real^N^N) =
                (\t x. (matrify:real^(N,N)finite_prod->real^N^N)
                    (vsum {i | i < n0}
                       (\i. (vectorize:real^N^N->real^(N,N)finite_prod)
                              (pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                 ((\i t z. (matrify:real^(N,N)finite_prod->real^N^N)
                                     (pde_mx_comm atlas a k h cs psi chi lam E i Fm t z))
                                  i t) x))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_mx_r]; ALL_TAC] THEN
  MATCH_MP_TAC PDE_MX_CHART_SUM_TFAM THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`] PDE_MX_DATA_PSIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`; `Fm:real->A->real^N^N`] PDE_MX_W_UPTO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\ compact((ks:num->real^N->bool) i) /\
                ks i SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\ a < b'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_mx_data (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b'
                   (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E` THEN
    REWRITE_TAC[pde_mx_data; pde_cover] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `(cs:num->(A->bool)#(A->real^N)) i`]
                PDE_MT_CHART_COEFF_UPTO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[VECTORIZE_MATRIFY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`a:real`; `b':real`; `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`;
                   `pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N)`;
                   `pde_mlbt atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N) h`;
                   `\z. lift(pde_mx_psic (cs:num->(A->bool)#(A->real^N)) psi i z)`;
                   `pde_mx_w atlas a cs chi lam
                      (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                         real^(N,N)finite_prod) i (Fm:real->A->real^N^N)`] PDE_MT_COMM_UPTO) THEN
    REWRITE_TAC[pde_mx_comm] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC PDE_MT_UPTO_OPEN_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_comm; GSYM MATRIFY_0] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN EXISTS_TAC `(:real^N) DIFF (ks:num->real^N->bool) i` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV; LIFT_NUM]]);;

(* ========================================================================= *)
(* Linearity of solutions (sums, zero, finite sums, change of the forcing    *)
(* off the times and points that count), and chart fields of chart           *)
(* solutions: a chart family Y solving the chart equation with forcing Q,    *)
(* supported in a compact piece K, gives the M-solution pdm_chart_field c    *)
(* (Y t) with forcing pdm_chart_field c (Q t).                               *)
(* ========================================================================= *)

let PDE_MX_LOP0_ADD_OPEN = prove
 (`!U (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (u:real^N->real^K) v x.
     open U /\ smooth_map_on U u /\ smooth_map_on U v /\ x IN U
     ==> pde_lop0 A B C (\y. u y + v y) x = pde_lop0 A B C u x + pde_lop0 A B C v x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!l. iterated_partial l (\y. (u:real^N->real^K) y + v y) x =
        iterated_partial l u x + iterated_partial l v x`
  MP_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `u:real^N->real^K`;
                                `v:real^N->real^K`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(GEN `i:num` (SPEC `[i:num]` th)) THEN
    MP_TAC(GEN `i:num` (GEN `j:num` (SPEC `[i:num; j:num]` th)))) THEN
  REWRITE_TAC[iterated_partial] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[pde_lop0] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; MATRIX_VECTOR_MUL_ADD_LDISTRIB; VSUM_ADD_NUMSEG] THEN
  VECTOR_ARITH_TAC);;

let PDE_MX_LTRHESS_ADD = prove
 (`!U (K:real^N->real^N^N) H (V1:real^N->real^N^N) V2 y.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V1) /\
     smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V2) /\
     metric_field U H /\ y IN U
     ==> pde_ltrhess K H (\z. V1 z + V2 z) y =
         pde_ltrhess K H V1 y + pde_ltrhess K H V2 y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
  REWRITE_TAC[VECTORIZE_ADD] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o (\z. (V1:real^N->real^N^N) z + V2 z) =
    (\z. (vectorize o V1) z + (vectorize o V2) z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     (\z. (V1:real^N->real^N^N) z + V2 z))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->real^N^N`; `H:real^N->real^N^N`;
                 `\z. (V1:real^N->real^N^N) z + V2 z`; `y:real^N`] PDE_ML_LOP0_FORM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->real^N^N`; `H:real^N->real^N^N`;
                 `V1:real^N->real^N^N`; `y:real^N`] PDE_ML_LOP0_FORM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->real^N^N`; `H:real^N->real^N^N`;
                 `V2:real^N->real^N^N`; `y:real^N`] PDE_ML_LOP0_FORM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC PDE_MX_LOP0_ADD_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let PDE_MX_LTRHESS_ZERO = prove
 (`!U (K:real^N->real^N^N) H y.
     metric_field U H /\ y IN U ==> pde_ltrhess K H (\z. mat 0) y = mat 0`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTORIZE_EQ] THEN REWRITE_TAC[VECTORIZE_0] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->real^N^N`; `H:real^N->real^N^N`;
                 `\z:real^N. mat 0:real^N^N`; `y:real^N`] PDE_ML_LOP0_FORM) THEN
  SUBGOAL_THEN `(vectorize:real^N^N->real^(N,N)finite_prod) o (\z:real^N. mat 0:real^N^N) =
                (\z. vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_0]; ALL_TAC] THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[metric_field]) THEN ASM_REWRITE_TAC[metric_field] THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[pde_lop0; PARTIAL_DERIVATIVE_CONST] THEN
  SUBGOAL_THEN `!j. partial_derivative j (\z:real^N. vec 0:real^(N,N)finite_prod) = (\z. vec 0)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; PARTIAL_DERIVATIVE_CONST]; ALL_TAC] THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_CONST; VECTOR_MUL_RZERO; MATRIX_VECTOR_MUL_RZERO; VSUM_0;
              VECTOR_ADD_LID]);;

let PDE_MX_TRHESS_ADD = prove
 (`!top atlas (K:A->real^N^N) h (v:A->real^N^N) w x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\
     mfd_tensor2_smooth atlas v /\ mfd_tensor2_smooth atlas w /\ x IN topspace top
     ==> pde_trhess atlas K h (\x. v x + w x) x =
         pde_trhess atlas K h v x + pde_trhess atlas K h w x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_trhess; METRIC_LOCAL_ADD; ETA_AX] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  MATCH_MP_TAC PDE_MX_LTRHESS_ADD THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  SUBGOAL_THEN `open(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_tensor2_smooth; riemannian_metric]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

let PDE_MX_TRHESS_ZERO = prove
 (`!top atlas (K:A->real^N^N) h x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\ x IN topspace top
     ==> pde_trhess atlas K h (\x. mat 0) x = mat 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_trhess] THEN
  SUBGOAL_THEN `metric_local atlas (chart_at atlas (x:A)) (\x:A. mat 0:real^N^N) = (\z. mat 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[metric_local; FUN_EQ_THM; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  MATCH_MP_TAC PDE_MX_LTRHESS_ZERO THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[riemannian_metric]) THEN ASM_SIMP_TAC[FUN_IN_IMAGE]);;

(* Sums of solutions. *)

let PDE_MX_MLIN_SOL_ADD = prove
 (`!top atlas a b (k:real->A->real^N^N) h f1 f2 u1 u2 v1 v2.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\
     pde_mlin_sol (top,atlas) a b k h f1 u1 v1 /\ pde_mlin_sol (top,atlas) a b k h f2 u2 v2
     ==> pde_mlin_sol (top,atlas) a b k h (\t x. f1 t x + f2 t x) (\x. u1 x + u2 x)
                      (\t x. v1 t x + v2 t x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < b
        ==> mfd_tensor2_smooth atlas ((v1:real->A->real^N^N) t) /\
            mfd_tensor2_smooth atlas ((v2:real->A->real^N^N) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_MESON_TAC[pde_mlin_sol];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pde_mlin_sol]) THEN REWRITE_TAC[pde_mlin_sol] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_MX_TFAM_ADD THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIX_ADD_COMPONENT] THEN
  SUBGOAL_THEN
   `pde_trhess atlas ((k:real->A->real^N^N) t) h (\x. (v1:real->A->real^N^N) t x + v2 t x) x =
    pde_trhess atlas (k t) h (v1 t) x + pde_trhess atlas (k t) h (v2 t) x`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PDE_MX_TRHESS_ADD THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_ADD_COMPONENT] THEN
  SUBGOAL_THEN
   `(pde_trhess atlas ((k:real->A->real^N^N) t) h ((v1:real->A->real^N^N) t) x$i$j +
     pde_trhess atlas (k t) h ((v2:real->A->real^N^N) t) x$i$j) +
    (f1:real->A->real^N^N) t x$i$j + (f2:real->A->real^N^N) t x$i$j =
    (pde_trhess atlas (k t) h (v1 t) x + f1 t x)$i$j +
    (pde_trhess atlas (k t) h (v2 t) x + f2 t x)$i$j`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_ADD_COMPONENT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN ASM_SIMP_TAC[]);;

let PDE_MX_MLIN_SOL_ZERO = prove
 (`!top atlas a b (k:real->A->real^N^N) h.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h
     ==> pde_mlin_sol (top,atlas) a b k h (\t x. mat 0) (\x. mat 0) (\t x. mat 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mlin_sol; PDE_ME_TFAM_ZERO] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(k:real->A->real^N^N) t`; `h:A->real^N^N`; `x:A`] PDE_MX_TRHESS_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_ADD_LID; MAT_0_COMPONENT; HAS_REAL_DERIVATIVE_CONST]);;

let PDE_MX_MLIN_SOL_VSUM = prove
 (`!top atlas a b (k:real->A->real^N^N) h (f:B->real->A->real^N^N) u v s.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\ FINITE s /\
     (!i. i IN s ==> pde_mlin_sol (top,atlas) a b k h (f i) (u i) (v i))
     ==> pde_mlin_sol (top,atlas) a b k h
           (\t x. (matrify:real^(N,N)finite_prod->real^N^N)
                    (vsum s (\i. (vectorize:real^N^N->real^(N,N)finite_prod) (f i t x))))
           (\x. (matrify:real^(N,N)finite_prod->real^N^N)
                  (vsum s (\i. (vectorize:real^N^N->real^(N,N)finite_prod) (u i x))))
           (\t x. (matrify:real^(N,N)finite_prod->real^N^N)
                    (vsum s (\i. (vectorize:real^N^N->real^(N,N)finite_prod) (v i t x))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
  SPEC_TAC(`s:B->bool`,`s:B->bool`) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; MATRIFY_0; PDE_MX_MLIN_SOL_ZERO; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIFY_ADD; MATRIFY_VECTORIZE] THEN
  MATCH_MP_TAC PDE_MX_MLIN_SOL_ADD THEN ASM_SIMP_TAC[ETA_AX]);;

let PDE_MX_MLIN_SOL_CONG = prove
 (`!top atlas a b (k:real->A->real^N^N) h f1 f2 u1 u2 v.
     pde_mlin_sol (top,atlas) a b k h f1 u1 v /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> f1 t x = f2 t x) /\
     (!x. x IN topspace top ==> u1 x = u2 x)
     ==> pde_mlin_sol (top,atlas) a b k h f2 u2 v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_mlin_sol] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f2:real->A->real^N^N) t x = f1 t x` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Chart fields of chart solutions. *)

let PDE_MX_CHART_FIELD_ZERO_AT = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (W:real^N->real^N^N) x.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     (x IN FST c ==> W(SND c x) = mat 0)
     ==> pdm_chart_field atlas c W x = mat 0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:A) IN FST(c:(A->bool)#(A->real^N))` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `W:real^N->real^N^N`; `x:A`] PDM_CHART_FIELD_AT) THEN
    ASM_SIMP_TAC[MATRIX_MUL_LZERO; MATRIX_MUL_RZERO];
    ASM_REWRITE_TAC[pdm_chart_field]]);;

let PDE_MX_CHART_FIELD_SOL = prove
 (`!top atlas a b (k:real->A->real^N^N) h (c:(A->bool)#(A->real^N)) K
    (Y:real->real^N->real^N^N) Q.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ c IN atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     compact K /\ K SUBSET IMAGE (SND c) (FST c) /\
     pde_upto a b (IMAGE (SND c) (FST c))
       (\t z. (vectorize:real^N^N->real^(N,N)finite_prod) (Y t z)) /\
     (!t z. a <= t /\ t < b /\ z IN IMAGE (SND c) (FST c) /\ ~(z IN K)
            ==> Y t z = mat 0 /\ Q t z = mat 0) /\
     (!z. z IN IMAGE (SND c) (FST c) ==> Y a z = mat 0) /\
     (!t z. a < t /\ t < b /\ z IN IMAGE (SND c) (FST c)
            ==> ((\s. (vectorize:real^N^N->real^(N,N)finite_prod) (Y (drop s) z))
                 has_vector_derivative
                 (pde_lop0 (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t) (pde_mlct atlas c k h t)
                           (\z. vectorize(Y t z)) z + vectorize(Q t z))) (at (lift t)))
     ==> pde_mlin_sol (top,atlas) a b k h (\t. pdm_chart_field atlas c (Q t)) (\x. mat 0)
                      (\t. pdm_chart_field atlas c (Y t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[pde_mlin_sol] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDM_CHART_FIELD_TFAM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `K:real^N->bool`] THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_MX_CHART_FIELD_ZERO_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `p:num`; `q:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_tensor2_smooth atlas (pdm_chart_field atlas (c:(A->bool)#(A->real^N))
                                 ((Y:real->real^N->real^N^N) t))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM PDM_TENSOR_SMOOTH_EQ] THEN MATCH_MP_TAC PDM_CHART_FIELD_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `K:real^N->bool`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                   `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                            ((Y:real->real^N->real^N^N) t z)`; `t:real`] PDE_ML_UPTO_SLICE_OPEN) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; o_DEF];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:A) IN FST(c:(A->bool)#(A->real^N))` THENL
   [ALL_TAC;
    (* off the chart: everything vanishes near x *)
    SUBGOAL_THEN `!W:real^N->real^N^N. pdm_chart_field atlas c W (x:A) = mat 0`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_REWRITE_TAC[pdm_chart_field]; ALL_TAC] THEN
    SUBGOAL_THEN
     `pde_trhess atlas ((k:real->A->real^N^N) t) h
        (pdm_chart_field atlas c ((Y:real->real^N->real^N^N) t)) x = mat 0`
    SUBST1_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[MATRIX_ADD_LID; MAT_0_COMPONENT; HAS_REAL_DERIVATIVE_CONST]] THEN
    ABBREV_TAC `Kc = {y:A | y IN FST(c:(A->bool)#(A->real^N)) /\ SND c y IN K}` THEN
    SUBGOAL_THEN `closed_in top (Kc:A->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kc" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `K:real^N->bool`] MFDC_CHART_COMPACT) THEN
      ASM_REWRITE_TAC[PAIR];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c0:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `U0 = IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0 INTER (topspace top DIFF Kc))` THEN
    SUBGOAL_THEN `open(U0:real^N->bool) /\ SND(c0:(A->bool)#(A->real^N)) x IN U0 /\
                  U0 SUBSET IMAGE (SND c0) (FST c0)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "U0" THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                       `topspace top DIFF (Kc:A->bool)`] MFDR_RESTRICT_IMAGE_OPEN) THEN
        ASM_SIMP_TAC[PAIR; OPEN_IN_DIFF; OPEN_IN_TOPSPACE];
        REWRITE_TAC[IN_IMAGE; IN_INTER; IN_DIFF] THEN EXISTS_TAC `x:A` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kc" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
        SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[pde_trhess] THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC EQ_TRANS
     `pde_ltrhess (metric_local atlas (c0:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t))
                  (metric_local atlas c0 h) (\z. mat 0) (SND c0 (x:A))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_ML_LTRHESS_LOCAL THEN EXISTS_TAC `U0:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?y:A. y IN FST(c0:(A->bool)#(A->real^N)) /\ y IN topspace top /\
                          ~(y IN Kc) /\ SND c0 y = z`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `chart_inv (c0:(A->bool)#(A->real^N)) z = (y:A)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[metric_local] THEN
      SUBGOAL_THEN `pdm_chart_field atlas (c:(A->bool)#(A->real^N))
                      ((Y:real->real^N->real^N^N) t) (y:A) = mat 0`
        (fun th -> REWRITE_TAC[th; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO]) THEN
      MATCH_MP_TAC PDE_MX_CHART_FIELD_ZERO_AT THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `SND(c:(A->bool)#(A->real^N)) y`] o
        check (fun th -> can (find_term ((=) `Q:real->real^N->real^N^N`)) (concl th) &&
                         can (find_term ((=) `K:real^N->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; FUN_IN_IMAGE] THEN ANTS_TAC THENL
       [UNDISCH_TAC `~((y:A) IN Kc)` THEN EXPAND_TAC "Kc" THEN ASM_SIMP_TAC[IN_ELIM_THM];
        SIMP_TAC[]];
      MATCH_MP_TAC PDE_MX_LTRHESS_ZERO THEN
      EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[riemannian_metric]) THEN ASM_SIMP_TAC[FUN_IN_IMAGE]]] THEN
  (* in the chart *)
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^N)) x IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!W:real^N->real^N^N.
      pdm_chart_field atlas c W (x:A) =
      transp(matrix(chart_jac (chart_at atlas x) (c:(A->bool)#(A->real^N)) x)) ** W(SND c x) **
      matrix(chart_jac (chart_at atlas x) c x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PDM_CHART_FIELD_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_trhess atlas ((k:real->A->real^N^N) t) h
      (pdm_chart_field atlas c ((Y:real->real^N->real^N^N) t)) (x:A) =
    pdm_chart_field atlas (c:(A->bool)#(A->real^N))
      (\z. (matrify:real^(N,N)finite_prod->real^N^N)
             (pde_lop0 (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t) (pde_mlct atlas c k h t)
                       (\z. vectorize(Y t z)) z)) x`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`;
                   `pde_trhess atlas ((k:real->A->real^N^N) t) h
                      (pdm_chart_field atlas c ((Y:real->real^N->real^N^N) t))`;
                   `x:A`] PDM_CHART_FIELD_METRIC_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `(k:real->A->real^N^N) t`; `h:A->real^N^N`;
                   `pdm_chart_field atlas (c:(A->bool)#(A->real^N)) ((Y:real->real^N->real^N^N) t)`;
                   `SND(c:(A->bool)#(A->real^N)) x`] PDE_ML_TRHESS_CHART) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
    TRANS_TAC EQ_TRANS
     `pde_ltrhess (metric_local atlas c ((k:real->A->real^N^N) t)) (metric_local atlas c h)
                  ((Y:real->real^N->real^N^N) t) (SND (c:(A->bool)#(A->real^N)) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_ML_LTRHESS_LOCAL THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC PDM_CHART_FIELD_SELF THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM VECTORIZE_EQ] THEN REWRITE_TAC[VECTORIZE_MATRIFY] THEN
    MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                   `metric_local atlas (c:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t)`;
                   `metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N)`;
                   `(Y:real->real^N->real^N^N) t`; `SND(c:(A->bool)#(A->real^N)) x`]
                  PDE_ML_LOP0_FORM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                       `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                ((Y:real->real^N->real^N^N) t z)`; `t:real`]
                      PDE_ML_UPTO_SLICE_OPEN) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; o_DEF];
        ASM_MESON_TAC[riemannian_metric]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PDE_ML_COEFF_FUN; o_DEF; ETA_AX]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM MATRIX_ADD_LDISTRIB; GSYM MATRIX_ADD_RDISTRIB] THEN
  ABBREV_TAC `J = matrix(chart_jac (chart_at atlas (x:A)) (c:(A->bool)#(A->real^N)) x)` THEN
  MP_TAC(ISPECL
   [`\r. (Y:real->real^N->real^N^N) r (SND(c:(A->bool)#(A->real^N)) x)`;
    `(matrify:real^(N,N)finite_prod->real^N^N)
       (pde_lop0 (pde_mlaa atlas c (k:real->A->real^N^N) t) (pde_mlbt atlas c k h t)
                 (pde_mlct atlas c k h t) (\z. vectorize((Y:real->real^N->real^N^N) t z))
                 (SND(c:(A->bool)#(A->real^N)) x) +
        vectorize((Q:real->real^N->real^N^N) t (SND c x)))`;
    `J:real^N^N`; `p:num`; `q:num`; `t:real`] PDE_ML_CONGR_DERIV) THEN
  ASM_SIMP_TAC[VECTORIZE_MATRIFY] THEN
  REWRITE_TAC[MATRIFY_ADD; MATRIFY_VECTORIZE]);;

(* ========================================================================= *)
(* The residual identity of the parametrix,                                  *)
(* pde_mlin_sol (top,atlas) a b' k h (F - R F) 0 (S F) (PDE_MX_PARAMETRIX):  *)
(* each piece psi_i w i F solves the chart equation with forcing             *)
(* psi_i g - comm_i (PDE_MT_UNTRANS_EQ), its chart field solves on M; the    *)
(* sum over the pieces gives the forcing sum_i chi_i F - R F = F - R F.      *)
(* ========================================================================= *)

let PDE_MX_TRANSPLANT_UNDILATE = prove
 (`!lam (w:real^N->real^K) z.
     &0 < lam /\ (!z. lam / &4 < norm z ==> w z = vec 0) /\ norm z < lam / &4
     ==> pdm_transplant lam w (inv lam % z + inv(&2) % vec 1) = w z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lam:real`; `w:real^N->real^K`; `inv lam % z + inv(&2) % vec 1:real^N`]
                PDM_TRANSPLANT_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTERVAL; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                    VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`z:real^N`; `j:num`] COMPONENT_LE_NORM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `abs(inv lam * (z:real^N)$j) < &1 / &4` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[PDE_MT_DILATE_INV]]);;

let PDE_MX_CHART_FIELD_SUB = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (W1:real^N->real^N^N) W2 x.
     smooth_manifold_atlas top atlas /\ c IN atlas
     ==> pdm_chart_field atlas c (\z. W1 z - W2 z) x =
         pdm_chart_field atlas c W1 x - pdm_chart_field atlas c W2 x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:A) IN FST(c:(A->bool)#(A->real^N))` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_FIELD_AT) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB];
    ASM_REWRITE_TAC[pdm_chart_field; MATRIX_SUB_REFL]]);;

(* One piece of the parametrix. *)

let PDE_MX_PIECE_SOL = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E i Fm.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' <= b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ i < n0 /\
     pde_tfam_from atlas a b' Fm
     ==> pde_mlin_sol (top,atlas) a b' k h
           (\t. pdm_chart_field atlas (cs i)
                  (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                         (pde_mx_psic cs psi i z %
                          pde_mx_g atlas a cs chi lam i Fm (t - a)
                            (inv(lam i) % z + inv(&2) % vec 1) -
                          pde_mx_comm atlas a k h cs psi chi lam E i Fm t z)))
           (\x. mat 0)
           (\t. pdm_chart_field atlas (cs i)
                  (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                         (pde_mx_psic cs psi i z % pde_mx_w atlas a cs chi lam E i Fm t z)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`] PDE_MX_DATA_PSIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`; `Fm:real->A->real^N^N`] PDE_MX_W_UPTO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`; `Fm:real->A->real^N^N`] PDE_MX_U_TSOL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_mx_data]) THEN
  SUBGOAL_THEN `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\ compact((ks:num->real^N->bool) i) /\
                ks i SUBSET IMAGE (SND(cs i)) (FST(cs i))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                   (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. ~(z IN (ks:num->real^N->bool) i)
          ==> pde_mx_comm atlas a (k:real->A->real^N^N) h cs psi chi lam E i Fm t z = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_comm] THEN
    MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN EXISTS_TAC `(:real^N) DIFF (ks:num->real^N->bool) i` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV; LIFT_NUM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tcoeff")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. a <= t /\ t < b' ==> riemannian_metric atlas ((k:real->A->real^N^N) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[REAL_LTE_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC PDE_MX_CHART_FIELD_SOL THEN EXISTS_TAC `(ks:num->real^N->bool) i` THEN
  ASM_REWRITE_TAC[VECTORIZE_MATRIFY] THEN REPEAT CONJ_TAC THENL
   [(* regularity *)
    MATCH_MP_TAC PDE_MT_UPTO_SCALAR_MUL_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_MT_UPTO_TIME_CONST THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC PDE_MT_UPTO_OPEN_SUBSET THEN
      EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
    (* supports *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; MATRIFY_0; VECTOR_SUB_RZERO];
    (* initial value *)
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; MATRIFY_0];
    ALL_TAC] THEN
  (* the chart equation *)
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`a:real`; `b':real`; `(lam:num->real) i`; `(aaT:num->real->real^N->real^N^N) i`;
    `(bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) i`;
    `(ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) i`;
    `pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N)`;
    `pde_mlbt atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N) h`;
    `pde_mlct atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N) h`;
    `V:real^N->bool`;
    `pde_mx_u atlas a cs chi lam
       (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod) i
       (Fm:real->A->real^N^N)`;
    `pde_mx_g atlas a cs chi lam i (Fm:real->A->real^N^N)`;
    `pde_mx_psic (cs:num->(A->bool)#(A->real^N)) psi i`; `(ks:num->real^N->bool) i`]
   PDE_MT_UNTRANS_EQ) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `z:real^N`]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM pde_mx_w; ETA_AX] THEN
  SUBGOAL_THEN
   `pde_mt_comm (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) i) (k:real->A->real^N^N) t)
                (pde_mlbt atlas (cs i) k h t) (\z. lift (pde_mx_psic cs psi i z))
                (pde_mx_w atlas a cs chi lam
                       (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                          real^(N,N)finite_prod) i (Fm:real->A->real^N^N) t) z =
    pde_mx_comm atlas a k h cs psi chi lam E i Fm t z`
  SUBST1_TAC THENL [REWRITE_TAC[pde_mx_comm]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

(* The forcing of one piece, on M. *)

let PDE_MX_PIECE_FORCING = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E i Fm t x.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ i < n0 /\
     x IN topspace top
     ==> pdm_chart_field atlas (cs i)
           (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                  (pde_mx_psic cs psi i z %
                   pde_mx_g atlas a cs chi lam i Fm (t - a) (inv(lam i) % z + inv(&2) % vec 1) -
                   pde_mx_comm atlas a k h cs psi chi lam E i Fm t z)) x =
         chi i x %% Fm t x -
         pdm_chart_field atlas (cs i)
           (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                  (pde_mx_comm atlas a k h cs psi chi lam E i Fm t z)) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`] PDE_MX_DATA_PSIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_mx_data]) THEN
  SUBGOAL_THEN `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\ compact((ks:num->real^N->bool) i) /\
                ks i SUBSET IMAGE (SND(cs i)) (FST(cs i))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                   (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (lam:num->real) i /\ (ks:num->real^N->bool) i SUBSET ball(vec 0,lam i / &4)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATRIFY_SUB] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDE_MX_CHART_FIELD_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_CASES_TAC `(x:A) IN FST((cs:num->(A->bool)#(A->real^N)) i)` THENL
   [ALL_TAC;
    SUBGOAL_THEN `(chi:num->A->real) i x = &0` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((psi:num->A->real) i x = &0)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_ARITH `~(&1 = &0)`]; ALL_TAC] THEN
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `i:num < n0`) th) o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th)))) THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]];
      ASM_REWRITE_TAC[pdm_chart_field; MATRIX_CMUL_LZERO]]] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `z0 = SND((cs:num->(A->bool)#(A->real^N)) i) (x:A)` THEN
  SUBGOAL_THEN `(z0:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)) /\
                chart_inv (cs i) z0 = (x:A)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(matrify:real^(N,N)finite_prod->real^N^N)
      (pde_mx_psic cs psi i z0 %
       pde_mx_g atlas a cs chi lam i (Fm:real->A->real^N^N) (t - a)
         (inv((lam:num->real) i) % z0 + inv(&2) % vec 1)) =
    (chi:num->A->real) i x %% metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (Fm t) z0`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `(z0:real^N) IN (ks:num->real^N->bool) i` THENL
     [ALL_TAC;
      SUBGOAL_THEN `(chi:num->A->real) i x = &0 /\
                    pde_mx_psic (cs:num->(A->bool)#(A->real^N)) psi i z0 = &0`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [SUBGOAL_THEN `pde_mx_psic (cs:num->(A->bool)#(A->real^N)) chi i z0 = &0` MP_TAC THENL
           [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[pde_mx_psic]];
          ASM_SIMP_TAC[]];
        ASM_REWRITE_TAC[VECTOR_MUL_LZERO; MATRIFY_0; MATRIX_CMUL_LZERO]]] THEN
    REWRITE_TAC[pde_mx_g; REAL_SUB_ADD] THEN
    MP_TAC(ISPECL [`(lam:num->real) i`;
                   `\z. pde_mx_psic (cs:num->(A->bool)#(A->real^N)) chi i z %
                        (vectorize:real^N^N->real^(N,N)finite_prod)
                          (metric_local atlas (cs i) ((Fm:real->A->real^N^N) t) z)`;
                   `z0:real^N`] PDE_MX_TRANSPLANT_UNDILATE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
        SUBGOAL_THEN `~((y:real^N) IN (ks:num->real^N->bool) i)` (fun th -> ASM_SIMP_TAC[th; VECTOR_MUL_LZERO]) THEN
        DISCH_TAC THEN UNDISCH_TAC `(ks:num->real^N->bool) i SUBSET ball(vec 0,(lam:num->real) i / &4)` THEN
        REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(ks:num->real^N->bool) i SUBSET ball(vec 0,(lam:num->real) i / &4)` THEN
        REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MATRIFY_CMUL; MATRIFY_VECTORIZE; MATRIX_CMUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `pde_mx_psic (cs:num->(A->bool)#(A->real^N)) chi i z0 = (chi:num->A->real) i x`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[pde_mx_psic]; ALL_TAC] THEN
    ASM_CASES_TAC `(chi:num->A->real) i x = &0` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    SUBGOAL_THEN `pde_mx_psic (cs:num->(A->bool)#(A->real^N)) psi i z0 = &1`
      (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&1`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mx_psic")) (concl th))) THEN
    ASM_REWRITE_TAC[pde_mx_psic];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_FIELD_AT) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(Fm:real->A->real^N^N) t`; `x:A`]
                PDM_CHART_FIELD_METRIC_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_FIELD_AT) THEN
  ASM_SIMP_TAC[]);;

(* The residual identity. *)

let PDE_MX_PARAMETRIX = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E Fm.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' <= b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' Fm
     ==> pde_mlin_sol (top,atlas) a b' k h
           (\t x. Fm t x - pde_mx_r atlas a k h cs psi chi lam E n0 Fm t x) (\x. mat 0)
           (pde_mx_s atlas a cs psi chi lam E n0 Fm)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
    `k:real->A->real^N^N`; `h:A->real^N^N`;
    `\i t. pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) i)
             (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                    (pde_mx_psic cs psi i z %
                     pde_mx_g atlas a cs chi lam i (Fm:real->A->real^N^N) (t - a)
                       (inv(lam i) % z + inv(&2) % vec 1) -
                     pde_mx_comm atlas a k h cs psi chi lam E i Fm t z))`;
    `\(i:num) (x:A). mat 0:real^N^N`;
    `\i t. pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) i)
             (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                    (pde_mx_psic cs psi i z %
                     pde_mx_w atlas a cs chi lam E i (Fm:real->A->real^N^N) t z))`;
    `{i:num | i < n0}`] PDE_MX_MLIN_SOL_VSUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC PDE_MX_PIECE_SOL THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `n0:num`; `ks:num->real^N->bool`;
                          `aaT:num->real->real^N->real^N^N`;
                          `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[GSYM pde_mx_s; ETA_AX] o BETA_RULE) THEN
  DISCH_THEN(fun th -> let args = snd(strip_comb(concl th)) in
    MATCH_MP_TAC PDE_MX_MLIN_SOL_CONG THEN EXISTS_TAC (el 5 args) THEN
    EXISTS_TAC (el 6 args) THEN CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  REWRITE_TAC[VECTORIZE_0; VSUM_0; MATRIFY_0] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
  REWRITE_TAC[VECTORIZE_MATRIFY; VECTORIZE_SUB; pde_mx_r] THEN
  TRANS_TAC EQ_TRANS
   `vsum {i:num | i < n0}
      (\i. (chi:num->A->real) i x % (vectorize:real^N^N->real^(N,N)finite_prod)
             ((Fm:real->A->real^N^N) t x) -
           (vectorize:real^N^N->real^(N,N)finite_prod)
             (pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) i)
                (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                       (pde_mx_comm atlas a k h cs psi chi lam E i Fm t z)) x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                      real^(N,N)finite_prod`;
                   `i:num`; `Fm:real->A->real^N^N`; `t:real`; `x:A`] PDE_MX_PIECE_FORCING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTORIZE_SUB; VECTORIZE_CMUL];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_SUB; FINITE_NUMSEG_LT; VSUM_RMUL] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_mx_data]) THEN
  ASM_SIMP_TAC[VECTOR_MUL_LID]);;

