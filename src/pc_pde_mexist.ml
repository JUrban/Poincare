(* ========================================================================= *)
(* Unit pc_pde_mexist: existence for d/dt v = tr_k Hess_h v + f on a compact *)
(* manifold: the Neumann series of the parametrix of pc_pde_mpar, its        *)
(* convergence on the tori with all space-time derivatives, the              *)
(* identification of the limit, initial data and patching in time;           *)
(* PDE_MLIN_FROM_TORUS.                                                      *)
(* ========================================================================= *)

needs "src/pc_pde_mpar.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The Neumann iterates H m (H 0 = G, H (m+1) = R (H m)), the commutator     *)
(* family pde_mx_rq of given torus families, and time-derivative slices      *)
(* pde_mx_tder.                                                              *)
(* ========================================================================= *)

let pde_mx_hh = define
 `(pde_mx_hh (atlas:((A->bool)#(A->real^N))->bool) a (k:real->A->real^N^N) h cs psi chi lam E n0
             (G:real->A->real^N^N) 0 = G) /\
  (pde_mx_hh atlas a k h cs psi chi lam E n0 G (SUC m) =
     pde_mx_r atlas a k h cs psi chi lam E n0 (pde_mx_hh atlas a k h cs psi chi lam E n0 G m))`;;

let pde_mx_rq = new_definition
 `pde_mx_rq (atlas:((A->bool)#(A->real^N))->bool) a (k:real->A->real^N^N) (h:A->real^N^N)
            (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real) (lam:num->real) n0
            (P:num->real->real^N->real^(N,N)finite_prod) (t:real) (x:A) =
    (matrify:real^(N,N)finite_prod->real^N^N)
     (vsum {j | j < n0}
       (\j. (vectorize:real^N^N->real^(N,N)finite_prod)
              (pdm_chart_field atlas (cs j)
                 (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                        (pde_mt_comm (pde_mlaa atlas (cs j) k t) (pde_mlbt atlas (cs j) k h t)
                           (\z. lift(pde_mx_psic cs psi j z))
                           (\z. P j (t - a) (inv(lam j) % z + inv(&2) % vec 1)) z)) x)))`;;

let PDE_MX_W_FUN = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) a cs chi lam E i (Fm:real->A->real^N^N) t.
     pde_mx_w atlas a cs chi lam E i Fm t =
     (\z. pde_mx_u atlas a cs chi lam E i Fm (t - a) (inv(lam i) % z + inv(&2) % vec 1))`,
  REWRITE_TAC[FUN_EQ_THM; pde_mx_w]);;

let PDE_MX_R_RQ = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) a (k:real->A->real^N^N) h cs psi chi lam E n0 Fm.
     pde_mx_r atlas a k h cs psi chi lam E n0 Fm =
     pde_mx_rq atlas a k h cs psi lam n0 (\j. pde_mx_u atlas a cs chi lam E j Fm)`,
  REWRITE_TAC[FUN_EQ_THM; pde_mx_r; pde_mx_rq; pde_mx_comm; PDE_MX_W_FUN]);;

let pde_mx_tder = new_definition
 `pde_mx_tder (m:num) (u:real->real^N->real^K) (tau:real) (x:real^N) =
    iterated_partial (REPLICATE m 1)
      (\w:real^(1,N)finite_sum. u (drop(fstcart w)) (sndcart w)) (pastecart (lift tau) x)`;;

let PDE_MX_HH_TFAM = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' <= b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G
     ==> !m. pde_tfam_from atlas a b' (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[pde_mx_hh] THEN
  MATCH_MP_TAC PDE_MX_R_TFAM THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `b:real`; `ks:num->real^N->bool`;
                        `aaT:num->real->real^N->real^N^N`;
                        `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                        `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                        `lamT:num->real`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Linearity of the families in the forcing and in the torus families        *)
(* (finite sums), for the partial sums of the Neumann series.                *)
(* ========================================================================= *)

let PDE_MX_METRIC_LOCAL_VSUM = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) c (H:B->A->real^N^N) s z.
     FINITE s
     ==> metric_local atlas c
           (\x. (matrify:real^(N,N)finite_prod->real^N^N)
                  (vsum s (\m. (vectorize:real^N^N->real^(N,N)finite_prod) (H m x)))) z =
         (matrify:real^(N,N)finite_prod->real^N^N)
           (vsum s (\m. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (metric_local atlas c (H m) z)))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; MATRIFY_0; MATRIFY_ADD; MATRIFY_VECTORIZE] THEN
  REWRITE_TAC[metric_local; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN REWRITE_TAC[metric_local] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB]);;

let PDE_MX_G_VSUM = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) a cs chi lam i (H:B->real->A->real^N^N) s tau y.
     FINITE s
     ==> pde_mx_g atlas a cs chi lam i
           (\t x. (matrify:real^(N,N)finite_prod->real^N^N)
                    (vsum s (\m. (vectorize:real^N^N->real^(N,N)finite_prod) (H m t x)))) tau y =
         vsum s (\m. pde_mx_g atlas a cs chi lam i (H m) tau y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[pde_mx_g; pdm_transplant; pdm_periodize] THEN
  ASM_SIMP_TAC[PDE_MX_METRIC_LOCAL_VSUM; VECTORIZE_MATRIFY; VSUM_LMUL; ETA_AX]);;

let PDE_MX_CHART_FIELD_VSUM = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (W:B->real^N->real^(N,N)finite_prod) s x.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ FINITE s
     ==> pdm_chart_field atlas c (\z. (matrify:real^(N,N)finite_prod->real^N^N) (vsum s (\m. W m z))) x =
         (matrify:real^(N,N)finite_prod->real^N^N)
           (vsum s (\m. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (pdm_chart_field atlas c (\z. matrify(W m z)) x)))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:A) IN FST(c:(A->bool)#(A->real^N))` THENL
   [ALL_TAC; ASM_REWRITE_TAC[pdm_chart_field; VECTORIZE_0; VSUM_0; MATRIFY_0]] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_FIELD_AT) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  ABBREV_TAC `J = matrix(chart_jac (chart_at atlas (x:A)) (c:(A->bool)#(A->real^N)) x)` THEN
  ABBREV_TAC `z0 = SND(c:(A->bool)#(A->real^N)) (x:A)` THEN
  UNDISCH_TAC `FINITE(s:B->bool)` THEN SPEC_TAC(`s:B->bool`,`s:B->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; MATRIFY_0; MATRIFY_ADD; MATRIFY_VECTORIZE; MATRIX_MUL_LZERO;
           MATRIX_MUL_RZERO] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB]);;

let PDE_MX_COMM_ADD = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) (p:real^N->real^1) (W1:real^N->real^K) W2 z.
     smooth_map_on (:real^N) W1 /\ smooth_map_on (:real^N) W2
     ==> pde_mt_comm A B p (\z. W1 z + W2 z) z =
         pde_mt_comm A B p W1 z + pde_mt_comm A B p W2 z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (\z. (W1:real^N->real^K) z + W2 z) z =
        partial_derivative i W1 z + partial_derivative i W2 z`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`[i:num]`; `(:real^N)`; `W1:real^N->real^K`; `W2:real^N->real^K`]
                  PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; iterated_partial] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pde_mt_comm] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; VECTOR_ADD_LDISTRIB; VSUM_ADD_NUMSEG] THEN
  VECTOR_ARITH_TAC);;

let PDE_MX_COMM_ZERO = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) (p:real^N->real^1) z.
     pde_mt_comm A B p (\z. vec 0) z = vec 0`,
  REWRITE_TAC[pde_mt_comm; PARTIAL_DERIVATIVE_CONST; VECTOR_MUL_RZERO; VECTOR_ADD_RID;
              MATRIX_VECTOR_MUL_RZERO; VSUM_0]);;

let PDE_MX_COMM_VSUM = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) (p:real^N->real^1) (W:C->real^N->real^K) s z.
     FINITE s /\ (!m. m IN s ==> smooth_map_on (:real^N) (W m))
     ==> pde_mt_comm A B p (\z. vsum s (\m. W m z)) z = vsum s (\m. pde_mt_comm A B p (W m) z)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; PDE_MX_COMM_ZERO; FORALL_IN_INSERT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^N->real^N^N`; `B:real^N->num->real^K^K`; `p:real^N->real^1`;
                 `(W:C->real^N->real^K) x`; `\z. vsum s (\m. (W:C->real^N->real^K) m z)`;
                 `z:real^N`] PDE_MX_COMM_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV];
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]);;

let PDE_MX_RQ_VSUM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a (k:real->A->real^N^N) h cs psi lam n0
    (P:B->num->real->real^N->real^(N,N)finite_prod) s t x.
     smooth_manifold_atlas top atlas /\ (!j. j < n0 ==> cs j IN atlas) /\ FINITE s /\
     (!m j. m IN s /\ j < n0 ==> smooth_map_on (:real^N) (P m j (t - a)))
     ==> (matrify:real^(N,N)finite_prod->real^N^N)
           (vsum s (\m. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (pde_mx_rq atlas a k h cs psi lam n0 (P m) t x))) =
         pde_mx_rq atlas a k h cs psi lam n0 (\j tau y. vsum s (\m. P m j tau y)) t x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_rq; VECTORIZE_MATRIFY] THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z. pde_mt_comm (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) j) (k:real->A->real^N^N) t)
          (pde_mlbt atlas (cs j) k h t) (\z. lift(pde_mx_psic cs psi j z))
          (\z. vsum s (\m. (P:B->num->real->real^N->real^(N,N)finite_prod) m j (t - a)
                             (inv((lam:num->real) j) % z + inv(&2) % vec 1))) z =
        vsum s (\m. pde_mt_comm (pde_mlaa atlas (cs j) k t) (pde_mlbt atlas (cs j) k h t)
                      (\z. lift(pde_mx_psic cs psi j z))
                      (\z. P m j (t - a) (inv(lam j) % z + inv(&2) % vec 1)) z)`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) j) (k:real->A->real^N^N) t`;
                   `pde_mlbt atlas ((cs:num->(A->bool)#(A->real^N)) j) (k:real->A->real^N^N) h t`;
                   `\z. lift(pde_mx_psic (cs:num->(A->bool)#(A->real^N)) psi j z)`;
                   `\m z. (P:B->num->real->real^N->real^(N,N)finite_prod) m j (t - a)
                            (inv((lam:num->real) j) % z + inv(&2) % vec 1)`;
                   `s:B->bool`; `z:real^N`] PDE_MX_COMM_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDM_SMOOTH_AFFINE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`;
                 `\m z. pde_mt_comm (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) j)
                                       (k:real->A->real^N^N) t)
                          (pde_mlbt atlas (cs j) k h t)
                          (\z. lift(pde_mx_psic cs psi j z))
                          (\z. (P:B->num->real->real^N->real^(N,N)finite_prod) m j (t - a)
                                 (inv((lam:num->real) j) % z + inv(&2) % vec 1)) z`;
                 `s:B->bool`; `x:A`] PDE_MX_CHART_FIELD_VSUM) THEN
  ASM_SIMP_TAC[VECTORIZE_MATRIFY]);;

(* ========================================================================= *)
(* Partial sums of the Neumann series.  The torus partial sums solve the     *)
(* torus equations with the partial sums of the forcings; the M-level        *)
(* partial sums satisfy F (n+1) = G + R' P n; commutators and the family     *)
(* pde_mx_rq pass to pointwise limits.                                       *)
(* ========================================================================= *)

let PDE_MX_PSUM_TSOL = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E
    (HH:num->real->A->real^N^N) i.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ i < n0 /\
     (!m. pde_tfam_from atlas a b' (HH m))
     ==> !n. pde_tsol (b' - a) (aaT i) (bbT i) (ccT i)
               (\tau y. vsum(0..n) (\m. pde_mx_g atlas a cs chi lam i (HH m) tau y))
               (\x. vec 0)
               (\tau y. vsum(0..n) (\m. pde_mx_u atlas a cs chi lam E i (HH m) tau y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_SING_NUMSEG; ETA_AX] THEN MATCH_MP_TAC PDE_MX_U_TSOL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                          `n0:num`; `ks:num->real^N->bool`; `psi:num->A->real`;
                          `lamT:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0] THEN
  MP_TAC(ISPECL
   [`b' - a`; `(aaT:num->real->real^N->real^N^N) i`;
    `(bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) i`;
    `(ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) i`;
    `\tau y. vsum(0..n) (\m. pde_mx_g atlas a cs chi lam i ((HH:num->real->A->real^N^N) m) tau y)`;
    `pde_mx_g atlas a cs chi lam i ((HH:num->real->A->real^N^N) (SUC n))`;
    `\x:real^N. vec 0:real^(N,N)finite_prod`; `\x:real^N. vec 0:real^(N,N)finite_prod`;
    `\tau y. vsum(0..n) (\m. pde_mx_u atlas a cs chi lam
        (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
        i ((HH:num->real->A->real^N^N) m) tau y)`;
    `pde_mx_u atlas a cs chi lam
        (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
        i ((HH:num->real->A->real^N^N) (SUC n))`;
    `&1`; `&1`] PDE_TSOL_LIN2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC PDE_MX_U_TSOL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                          `n0:num`; `ks:num->real^N->bool`; `psi:num->A->real`;
                          `lamT:num->real`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ADD_LID; VECTOR_MUL_RZERO; ETA_AX]]);;

let PDE_MX_VSUM_SHIFT = prove
 (`!(f:num->real^K) n. vsum(0..SUC n) f = f 0 + vsum(0..n) (\m. f(SUC m))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->real^K`; `0`; `SUC n`] VSUM_CLAUSES_LEFT) THEN
  REWRITE_TAC[LE_0] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`1`; `f:num->real^K`; `0`; `n:num`] VSUM_OFFSET) THEN
  REWRITE_TAC[ADD1; ADD_CLAUSES]);;

let PDE_MX_FSUM_REC = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G n t x.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     (!m. pde_tfam_from atlas a b' (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)) /\
     a <= t /\ t < b'
     ==> (matrify:real^(N,N)finite_prod->real^N^N)
           (vsum(0..SUC n) (\m. (vectorize:real^N^N->real^(N,N)finite_prod)
                                  (pde_mx_hh atlas a k h cs psi chi lam E n0 G m t x))) =
         G t x +
         pde_mx_rq atlas a k h cs psi lam n0
           (\j tau y. vsum(0..n) (\m. pde_mx_u atlas a cs chi lam E j
                                        (pde_mx_hh atlas a k h cs psi chi lam E n0 G m) tau y))
           t x`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [PDE_MX_VSUM_SHIFT] THEN
  REWRITE_TAC[pde_mx_hh; PDE_MX_R_RQ] THEN
  REWRITE_TAC[MATRIFY_ADD; MATRIFY_VECTORIZE] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `cs:num->(A->bool)#(A->real^N)`;
                 `psi:num->A->real`; `lam:num->real`; `n0:num`;
                 `\m j. pde_mx_u atlas a cs chi lam
                          (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                             real^(N,N)finite_prod) j
                          (pde_mx_hh atlas a (k:real->A->real^N^N) h cs psi chi lam E n0
                             (G:real->A->real^N^N) m)`;
                 `0..n`; `t:real`; `x:A`] PDE_MX_RQ_VSUM) THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_mx_data]) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN CONJ_TAC THENL
   [UNDISCH_TAC `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                   (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `j:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`;
                 `pde_mx_hh atlas a (k:real->A->real^N^N) h cs psi chi lam
                    (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                       real^(N,N)finite_prod) n0 (G:real->A->real^N^N) m`] PDE_MX_U_TSOL) THEN
  ASM_REWRITE_TAC[pde_tsol] THEN STRIP_TAC THEN
  MATCH_MP_TAC PDE_ML_UPTO_SLICE_OPEN THEN
  MAP_EVERY EXISTS_TAC [`&0`; `b' - a`] THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN ASM_REAL_ARITH_TAC);;

(* Pointwise limits of commutators and of pde_mx_rq. *)

let PDE_MX_COMM_LIM = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) (p:real^N->real^1) (Wn:num->real^N->real^K) W z.
     ((\n. Wn n z) --> W z) sequentially /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> ((\n. partial_derivative i (Wn n) z) --> partial_derivative i W z) sequentially)
     ==> ((\n. pde_mt_comm A B p (Wn n) z) --> pde_mt_comm A B p W z) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mt_comm] THEN MATCH_MP_TAC LIM_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THENL
   [MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LIM_CMUL THEN REPEAT(MATCH_MP_TAC LIM_ADD THEN CONJ_TAC) THEN
    MATCH_MP_TAC LIM_CMUL THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC LIM_CMUL THEN
    MP_TAC(ISPECL [`sequentially`; `(**) ((B:real^N->num->real^K^K) z i)`;
                   `\n. (Wn:num->real^N->real^K) n z`; `(W:real^N->real^K) z`] LIM_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[REWRITE_RULE[ETA_AX] MATRIX_VECTOR_MUL_LINEAR]]);;

let PDE_MX_TRIPLE_LINEAR = prove
 (`!J:real^N^N. linear(\v. (vectorize:real^N^N->real^(N,N)finite_prod)
                             (transp J ** (matrify:real^(N,N)finite_prod->real^N^N) v ** J))`,
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB;
              MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; VECTORIZE_ADD; VECTORIZE_CMUL]);;

let PDE_MX_RQ_LIM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a (k:real->A->real^N^N) h cs psi lam n0
    (P:num->num->real->real^N->real^(N,N)finite_prod) Q t x.
     smooth_manifold_atlas top atlas /\ (!j. j < n0 ==> cs j IN atlas) /\
     (!j. j < n0 ==> (!n. smooth_map_on (:real^N) (P n j (t - a))) /\
                     smooth_map_on (:real^N) (Q j (t - a))) /\
     (!j y. j < n0
            ==> ((\n. P n j (t - a) y) --> Q j (t - a) y) sequentially /\
                (!i. 1 <= i /\ i <= dimindex(:N)
                     ==> ((\n. partial_derivative i (P n j (t - a)) y) -->
                          partial_derivative i (Q j (t - a)) y) sequentially))
     ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                 (pde_mx_rq atlas a k h cs psi lam n0 (P n) t x)) -->
          vectorize(pde_mx_rq atlas a k h cs psi lam n0 Q t x)) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_rq; VECTORIZE_MATRIFY] THEN
  MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:A) IN FST((cs:num->(A->bool)#(A->real^N)) j)` THENL
   [ALL_TAC; ASM_REWRITE_TAC[pdm_chart_field; LIM_CONST]] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_FIELD_AT) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  ABBREV_TAC `J = matrix(chart_jac (chart_at atlas (x:A)) ((cs:num->(A->bool)#(A->real^N)) j) x)` THEN
  ABBREV_TAC `z0 = SND((cs:num->(A->bool)#(A->real^N)) j) (x:A)` THEN
  MP_TAC(ISPECL
   [`sequentially`;
    `\v. (vectorize:real^N^N->real^(N,N)finite_prod)
           (transp (J:real^N^N) ** (matrify:real^(N,N)finite_prod->real^N^N) v ** J)`;
    `\n. pde_mt_comm (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) j) (k:real->A->real^N^N) t)
           (pde_mlbt atlas (cs j) k h t) (\z. lift(pde_mx_psic cs psi j z))
           (\z. (P:num->num->real->real^N->real^(N,N)finite_prod) n j (t - a)
                  (inv((lam:num->real) j) % z + inv(&2) % vec 1)) z0`;
    `pde_mt_comm (pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) j) (k:real->A->real^N^N) t)
       (pde_mlbt atlas (cs j) k h t) (\z. lift(pde_mx_psic cs psi j z))
       (\z. (Q:num->real->real^N->real^(N,N)finite_prod) j (t - a)
              (inv((lam:num->real) j) % z + inv(&2) % vec 1)) z0`] LIM_LINEAR) THEN
  REWRITE_TAC[PDE_MX_TRIPLE_LINEAR] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC PDE_MX_COMM_LIM THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!f:real^N->real^(N,N)finite_prod.
      smooth_map_on (:real^N) f
      ==> partial_derivative i (\z. f(inv((lam:num->real) j) % z + inv(&2) % vec 1)) z0 =
          inv(lam j) % partial_derivative i f (inv(lam j) % z0 + inv(&2) % vec 1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`[i:num]`; `f:real^N->real^(N,N)finite_prod`; `inv((lam:num->real) j)`;
                   `inv(&2) % vec 1:real^N`] PDM_ITERATED_PARTIAL_AFFINE) THEN
    ASM_REWRITE_TAC[iterated_partial; LENGTH; REAL_POW_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\n. partial_derivative i
           (\z. (P:num->num->real->real^N->real^(N,N)finite_prod) n j (t - a)
                  (inv((lam:num->real) j) % z + inv(&2) % vec 1)) z0) =
    (\n. inv(lam j) % partial_derivative i (P n j (t - a)) (inv(lam j) % z0 + inv(&2) % vec 1)) /\
    partial_derivative i
      (\z. (Q:num->real->real^N->real^(N,N)finite_prod) j (t - a)
             (inv((lam:num->real) j) % z + inv(&2) % vec 1)) z0 =
    inv(lam j) % partial_derivative i (Q j (t - a)) (inv(lam j) % z0 + inv(&2) % vec 1)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN CONJ_TAC THENL [GEN_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC(SPEC_ALL th) ORELSE
      MATCH_MP_TAC (SPEC `(Q:num->real->real^N->real^(N,N)finite_prod) j (t - a)` th) ORELSE
      MATCH_MP_TAC (SPEC `(P:num->num->real->real^N->real^(N,N)finite_prod) n j (t - a)` th)) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC LIM_CMUL THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Analytic core, part 1: time-derivative slices pde_mx_tder of torus        *)
(* families smooth up to 0: they are smooth periodic maps, space-time jets   *)
(* are space jets of time-derivative slices, and the torus Sobolev           *)
(* inequality bounds all space-time jets.                                    *)
(* ========================================================================= *)

let PDE_MX_CANON_SMOOTH = prove
 (`!Tm (u:real->real^N->real^K).
     pde_upto (&0) Tm (:real^N) u
     ==> smooth_map_on (interval(lift(&0),lift Tm) PCROSS (:real^N))
                       (\w. u (drop(fstcart w)) (sndcart w))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fe:real^(1,N)finite_sum->real^K`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `Fe:real^(1,N)finite_sum->real^K` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`drop s`; `y:real^N`]) THEN REWRITE_TAC[LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIFT_DROP]) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(&0 - e),lift Tm) PCROSS (:real^N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC]);;

let PDE_MX_REPLICATE_SUC_APPEND = prove
 (`!n (x:A). REPLICATE (SUC n) x = APPEND (REPLICATE n x) [x]`,
  INDUCT_TAC THENL
   [REWRITE_TAC[REPLICATE; APPEND];
    GEN_TAC THEN ONCE_REWRITE_TAC[REPLICATE] THEN ASM_REWRITE_TAC[APPEND]]);;

let PDE_MX_IP_REP_SUC = prove
 (`!n (f:real^M->real^K).
     iterated_partial (REPLICATE (SUC n) 1) f =
     iterated_partial (REPLICATE n 1) (partial_derivative 1 f)`,
  REWRITE_TAC[PDE_MX_REPLICATE_SUC_APPEND; ITERATED_PARTIAL_APPEND; iterated_partial]);;

let PDE_MX_TDER_UPTO = prove
 (`!Tm (u:real->real^N->real^K) j d.
     pde_upto (&0) Tm (:real^N) u /\ &0 < d
     ==> pde_upto d Tm (:real^N) (pde_mx_tder j u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
  EXISTS_TAC `d / &2` THEN
  EXISTS_TAC `iterated_partial (REPLICATE j 1)
                (\w:real^(1,N)finite_sum. (u:real->real^N->real^K) (drop(fstcart w)) (sndcart w))` THEN
  REWRITE_TAC[pde_mx_tder] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `interval(lift(&0),lift Tm) PCROSS (:real^N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    MATCH_MP_TAC PDE_MX_CANON_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let PDE_MX_TDER_SMOOTH = prove
 (`!Tm (u:real->real^N->real^K) j tau.
     pde_upto (&0) Tm (:real^N) u /\ &0 < tau /\ tau < Tm
     ==> smooth_map_on (:real^N) (pde_mx_tder j u tau)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ML_UPTO_SLICE_OPEN THEN
  MAP_EVERY EXISTS_TAC [`tau:real`; `Tm:real`] THEN
  ASM_SIMP_TAC[OPEN_UNIV; REAL_LE_REFL; PDE_MX_TDER_UPTO]);;

let PDE_MX_TDER_ZPER = prove
 (`!Tm (u:real->real^N->real^K) j tau.
     pde_upto (&0) Tm (:real^N) u /\ (!t. &0 <= t /\ t < Tm ==> pde_zper (u t)) /\
     &0 < tau /\ tau < Tm
     ==> pde_zper (pde_mx_tder j u tau)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_zper; pde_mx_tder] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `kk:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift(&0),lift Tm) PCROSS (:real^N))
                  (\w:real^(1,N)finite_sum. (u:real->real^N->real^K) (drop(fstcart w)) (sndcart w))`
  ASSUME_TAC THENL [MATCH_MP_TAC PDE_MX_CANON_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift tau) (x + basis kk:real^N) =
                pastecart (lift tau) x + pastecart (vec 0) (basis kk)` SUBST1_TAC THENL
   [REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_RID]; ALL_TAC] THEN
  MP_TAC(ISPECL [`REPLICATE j 1`;
                 `\w:real^(1,N)finite_sum. (u:real->real^N->real^K) (drop(fstcart w)) (sndcart w)`;
                 `&0`; `Tm:real`; `basis kk:real^N`; `pastecart (lift tau) (x:real^N)`]
                PDE_HEAT_ITERATED_TRANSLATE_SLAB) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
  EXISTS_TAC `interval(lift(&0),lift Tm) PCROSS (:real^N)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_INTERVAL_1;
               LIFT_DROP; IN_UNIV; FORALL_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `z:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_ADD; FSTCART_ADD; SNDCART_ADD;
              VECTOR_ADD_RID] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop s` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_zper")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[pde_zper]] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Space-time jets as space jets of time-derivative slices. *)

let PDE_MX_FILTER_SHIFT = prove
 (`!l. ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l
       ==> FILTER (\j. ~(j = 1)) l = MAP (\k. 1 + k) (MAP (\j. j - 1) (FILTER (\j. ~(j = 1)) l)) /\
           ALL (\k. 1 <= k /\ k <= dimindex(:N)) (MAP (\j. j - 1) (FILTER (\j. ~(j = 1)) l)) /\
           LENGTH (MAP (\j. j - 1) (FILTER (\j. ~(j = 1)) l)) = LENGTH l - pde_ntime l`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l` THEN
    SPEC_TAC(`l:num list`,`l:num list`) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[FILTER; MAP; ALL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[MAP; CONS_11] THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM ACCEPT_TAC]; FIRST_X_ASSUM ACCEPT_TAC];
    UNDISCH_TAC `ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l` THEN
    SPEC_TAC(`l:num list`,`l:num list`) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[FILTER; MAP; ALL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[MAP; ALL] THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `h <= dimindex(:(1,N)finite_sum)` THEN REWRITE_TAC[PDE_HEAT_DIMINDEX_ST] THEN
        ASM_ARITH_TAC;
        FIRST_X_ASSUM ACCEPT_TAC];
      FIRST_X_ASSUM ACCEPT_TAC];
    REWRITE_TAC[LENGTH_MAP; pde_ntime] THEN
    MP_TAC(ISPECL [`\j:num. j = 1`; `l:num list`] PDE_FILTER_LENGTH_SPLIT) THEN
    REWRITE_TAC[] THEN ARITH_TAC]);;

let PDE_MX_TDER_JET = prove
 (`!Tm (u:real->real^N->real^K) l tau y.
     pde_upto (&0) Tm (:real^N) u /\ &0 < tau /\ tau < Tm /\
     ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l
     ==> iterated_partial l (\w. u (drop(fstcart w)) (sndcart w)) (pastecart (lift tau) y) =
         iterated_partial (MAP (\j. j - 1) (FILTER (\j. ~(j = 1)) l))
                          (pde_mx_tder (pde_ntime l) u tau) y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `CU = \w:real^(1,N)finite_sum. (u:real->real^N->real^K) (drop(fstcart w)) (sndcart w)` THEN
  SUBGOAL_THEN `smooth_map_on (interval(lift(&0),lift Tm) PCROSS (:real^N))
                  (CU:real^(1,N)finite_sum->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "CU" THEN MATCH_MP_TAC PDE_MX_CANON_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift(&0),lift Tm) PCROSS (:real^N)`;
                 `CU:real^(1,N)finite_sum->real^K`; `1`] TEXT_ITERATED_PARTIAL_CANON) THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PDE_HEAT_DIMINDEX_ST] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l` THEN
    REWRITE_TAC[PDE_HEAT_DIMINDEX_ST];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift tau) (y:real^N)`) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `FILTER (\j. j = 1) l = REPLICATE (pde_ntime l) 1` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`1`; `FILTER (\j. j = 1) l`] PDE_ALL_EQ_REPLICATE) THEN
    REWRITE_TAC[ALL_FILTER; ALL_T; pde_ntime];
    ALL_TAC] THEN
  REWRITE_TAC[ITERATED_PARTIAL_APPEND] THEN
  MP_TAC(SPEC `l:num list` PDE_MX_FILTER_SHIFT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [th])
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`iterated_partial (REPLICATE (pde_ntime l) 1) (CU:real^(1,N)finite_sum->real^K)`;
                 `&0`; `Tm:real`; `MAP (\j. j - 1) (FILTER (\j. ~(j = 1)) l)`; `tau:real`;
                 `y:real^N`] PDE_SLAB_SLICE_ITERATED) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  EXPAND_TAC "CU" THEN REWRITE_TAC[FUN_EQ_THM; pde_mx_tder]);;

let PDE_MX_JET_SOBOLEV = prove
 (`?C. &0 < C /\
       !Tm (u:real->real^N->real^K) l tau y.
         pde_upto (&0) Tm (:real^N) u /\ (!t. &0 <= t /\ t < Tm ==> pde_zper (u t)) /\
         &0 < tau /\ tau < Tm /\ ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l
         ==> norm(iterated_partial l (\w. u (drop(fstcart w)) (sndcart w))
                                   (pastecart (lift tau) y)) pow 2 <=
             C * pde_hs2 (dimindex(:N) + (LENGTH l - pde_ntime l))
                         (pde_mx_tder (pde_ntime l) u tau)`,
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC PDE_TORUS_SOBOLEV_PARTIAL THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Tm:real`; `u:real->real^N->real^K`; `l:num list`; `tau:real`; `y:real^N`]
                PDE_MX_TDER_JET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPEC `l:num list` PDE_MX_FILTER_SHIFT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "LENGTH")) (concl th) &&
    is_eq (concl th))) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_MX_TDER_ZPER THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Analytic core, part 2: trading a time derivative of a torus solution with *)
(* zero data for two space derivatives (R2), pointwise (PDE_MX_TT_POINT) and *)
(* in H^s (PDE_MX_TIME_TRADE):                                               *)
(*   |d_t^(j+1) u|_s <= C (sum_(m<=j) |d_t^m u|_(s+2) + |d_t^j g|_s).        *)
(* ========================================================================= *)

let PDE_MX_NTIME_SPACE = prove
 (`!l. ALL (\i. 1 <= i /\ i <= dimindex(:N)) l ==> pde_ntime (MAP (\k. 1 + k) l) = 0`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL; PDE_NTIME_CLAUSES] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(1 + h = 1)` (fun th -> ASM_SIMP_TAC[th; PDE_NTIME_CLAUSES]) THEN
  ASM_ARITH_TAC);;

(* Space derivatives of a time-derivative slice through an extension. *)

let PDE_MX_SLICE_TDER = prove
 (`!Tm (u:real->real^N->real^K) FU j l tau x.
     pde_upto (&0) Tm (:real^N) u /\
     (!t y. &0 <= t /\ t < Tm ==> FU(pastecart (lift t) y) = u t y) /\
     &0 < tau /\ tau < Tm /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> iterated_partial l (pde_mx_tder j u tau) x =
         iterated_partial (APPEND (MAP (\k. 1 + k) l) (REPLICATE j 1)) FU
                          (pastecart (lift tau) x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `CU = \w:real^(1,N)finite_sum. (u:real->real^N->real^K) (drop(fstcart w)) (sndcart w)` THEN
  SUBGOAL_THEN `smooth_map_on (interval(lift(&0),lift Tm) PCROSS (:real^N))
                  (CU:real^(1,N)finite_sum->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "CU" THEN MATCH_MP_TAC PDE_MX_CANON_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pde_mx_tder j (u:real->real^N->real^K) tau =
                (\y. iterated_partial (REPLICATE j 1) (CU:real^(1,N)finite_sum->real^K)
                       (pastecart (lift tau) y))` SUBST1_TAC THENL
   [EXPAND_TAC "CU" THEN REWRITE_TAC[FUN_EQ_THM; pde_mx_tder]; ALL_TAC] THEN
  MP_TAC(ISPECL [`iterated_partial (REPLICATE j 1) (CU:real^(1,N)finite_sum->real^K)`;
                 `&0`; `Tm:real`; `l:num list`; `tau:real`; `x:real^N`] PDE_SLAB_SLICE_ITERATED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM ITERATED_PARTIAL_APPEND] THEN
  MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
  EXISTS_TAC `interval(lift(&0),lift Tm) PCROSS (:real^N)` THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV; FORALL_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`s1:real^1`; `z:real^N`] THEN STRIP_TAC THEN
  EXPAND_TAC "CU" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`drop s1`; `z:real^N`] o check (fun th ->
    can (find_term ((=) `FU:real^(1,N)finite_sum->real^K`)) (concl th) && is_forall (concl th))) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(MATCH_MP_TAC o GSYM) THEN ASM_REAL_ARITH_TAC);;

(* Space-time jets of an extension as space jets of time-derivative slices. *)

let PDE_MX_EXT_JET = prove
 (`!Tm (u:real->real^N->real^K) FU L tau x.
     pde_upto (&0) Tm (:real^N) u /\
     (!t y. &0 <= t /\ t < Tm ==> FU(pastecart (lift t) y) = u t y) /\
     &0 < tau /\ tau < Tm /\ ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) L
     ==> iterated_partial L FU (pastecart (lift tau) x) =
         iterated_partial (MAP (\j. j - 1) (FILTER (\j. ~(j = 1)) L))
                          (pde_mx_tder (pde_ntime L) u tau) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Tm:real`; `u:real->real^N->real^K`; `L:num list`; `tau:real`; `x:real^N`]
                PDE_MX_TDER_JET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
  EXISTS_TAC `interval(lift(&0),lift Tm) PCROSS (:real^N)` THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV; FORALL_PASTECART;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`s1:real^1`; `z:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`drop s1`; `z:real^N`] o check (fun th ->
    can (find_term ((=) `FU:real^(1,N)finite_sum->real^K`)) (concl th) && is_forall (concl th))) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Pointwise time trading. *)

let PDE_MX_TT_POINT = prove
 (`!Tm lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc T2 j s.
     pde_tcoeff Tm lam aa bb cc /\ &0 < T2 /\ T2 < Tm
     ==> ?Kt. &0 <= Kt /\
              !g u tau x l.
                pde_upto (&0) Tm (:real^N) g /\
                pde_tsol Tm aa bb cc g (\x. vec 0) u /\ &0 < tau /\ tau <= T2 /\
                l IN pde_index_lists s (:N)
                ==> norm(iterated_partial l (pde_mx_tder (SUC j) u tau) x) <=
                    Kt * sum(0..j) (\m. pde_jetn (s + 2) (pde_mx_tder m u tau) x) +
                    norm(iterated_partial l (pde_mx_tder j g tau) x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `T3 = (T2 + Tm) / &2` THEN
  SUBGOAL_THEN `T2 < T3 /\ T3 < Tm` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T3" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pde_tbnd Tm (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K)
                         (cc:real->real^N->real^K^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_TCOEFF_TBND THEN EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Tm:real`; `aa:real->real^N->real^N^N`; `bb:real->real^N->num->real^K^K`;
                 `cc:real->real^N->real^K^K`; `T3:real`; `s + j:num`] PDE_TBND_STBND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `A:real`)] THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pde_stbnd]); ALL_TAC] THEN
  ABBREV_TAC `Ls = {l | ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                        pde_ntime l <= j /\ LENGTH l <= (s + 2) + j /\
                        LENGTH l - pde_ntime l <= s + 2}` THEN
  EXISTS_TAC `&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * A * &2 pow (s + j) *
              &(CARD(Ls:num list->bool))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_POW_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g:real->real^N->real^K`; `u:real->real^N->real^K`; `tau:real`;
                       `x:real^N`; `l:num list`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ LENGTH l <= s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `l IN pde_index_lists s (:N)` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_tsol]) THEN
  MP_TAC(ASSUME `pde_upto (&0) Tm (:real^N) (u:real->real^N->real^K)`) THEN
  REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FU:real^(1,N)finite_sum->real^K`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ASSUME `pde_upto (&0) Tm (:real^N) (g:real->real^N->real^K)`) THEN
  REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `eg:real` (X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^K`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `S3 = interval(lift(&0),lift T3) PCROSS (:real^N)` THEN
  ABBREV_TAC `w = pastecart (lift tau) (x:real^N)` THEN
  SUBGOAL_THEN `open (S3:real^(1,N)finite_sum->bool) /\ w IN S3 /\
                smooth_map_on S3 (FU:real^(1,N)finite_sum->real^K) /\
                smooth_map_on S3 (FG:real^(1,N)finite_sum->real^K)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S3"; "w"] THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_INTERVAL_1;
             LIFT_DROP; IN_UNIV] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - e),lift Tm) PCROSS (:real^N)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - eg),lift Tm) PCROSS (:real^N)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `L = APPEND (MAP (\k. 1 + k) (l:num list)) (REPLICATE j 1)` THEN
  SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) L /\
                LENGTH L = LENGTH (l:num list) + j /\ pde_ntime L = j`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    REWRITE_TAC[ALL_APPEND; LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE; PDE_NTIME_APPEND;
                PDE_NTIME_REPLICATE] THEN
    ASM_SIMP_TAC[PDE_MX_NTIME_SPACE; PDE_MAP_SUC_RANGE; ADD_CLAUSES] THEN
    MATCH_MP_TAC PDE_FT_ALL_REPLICATE THEN REWRITE_TAC[PDE_HEAT_DIMINDEX_ST] THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the u side: d_t^(j+1) u = D^L (stop FU + FG) on the slab *)
  SUBGOAL_THEN
   `iterated_partial l (pde_mx_tder (SUC j) (u:real->real^N->real^K) tau) x =
    iterated_partial L
      (pde_stop (\z:real^(1,N)finite_sum. (aa:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
                (\z i. (bb:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
                (\z. (cc:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))
                (FU:real^(1,N)finite_sum->real^K)) w +
    iterated_partial L (FG:real^(1,N)finite_sum->real^K) w`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`Tm:real`; `u:real->real^N->real^K`; `FU:real^(1,N)finite_sum->real^K`;
                   `SUC j`; `l:num list`; `tau:real`; `x:real^N`] PDE_MX_SLICE_TDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `APPEND (MAP (\k. 1 + k) (l:num list)) (REPLICATE (SUC j) 1) = APPEND L [1]` SUBST1_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[PDE_MX_REPLICATE_SUC_APPEND; APPEND_ASSOC]; ALL_TAC] THEN
    ASM_REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
    TRANS_TAC EQ_TRANS
     `iterated_partial L
        (\z. pde_stop (\z:real^(1,N)finite_sum. (aa:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
                      (\z i. (bb:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
                      (\z. (cc:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))
                      (FU:real^(1,N)finite_sum->real^K) z +
             (FG:real^(1,N)finite_sum->real^K) z) w` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
      EXISTS_TAC `S3:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "S3" THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; IN_UNIV; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`s1:real^1`; `z:real^N`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`Tm:real`; `aa:real->real^N->real^N^N`; `bb:real->real^N->num->real^K^K`;
                     `cc:real->real^N->real^K^K`; `g:real->real^N->real^K`;
                     `\x:real^N. vec 0:real^K`; `u:real->real^N->real^K`;
                     `FU:real^(1,N)finite_sum->real^K`; `e:real`;
                     `drop s1`; `z:real^N`] PDE_TSOL_ST_EQ) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`drop s1`; `z:real^N`] o check (fun th ->
        can (find_term ((=) `FG:real^(1,N)finite_sum->real^K`)) (concl th) &&
        is_forall (concl th))) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(MATCH_MP_TAC o GSYM) THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`L:num list`; `S3:real^(1,N)finite_sum->bool`;
                     `pde_stop (\z:real^(1,N)finite_sum. (aa:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
                               (\z i. (bb:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
                               (\z. (cc:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))
                               (FU:real^(1,N)finite_sum->real^K)`;
                     `FG:real^(1,N)finite_sum->real^K`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_STOP_SMOOTH THEN
        MAP_EVERY EXISTS_TAC [`s + j:num`; `A:real`] THEN ASM_REWRITE_TAC[];
        DISCH_THEN(MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]]];
    ALL_TAC] THEN
  (* the g side *)
  SUBGOAL_THEN
   `iterated_partial l (pde_mx_tder j (g:real->real^N->real^K) tau) x =
    iterated_partial L (FG:real^(1,N)finite_sum->real^K) w`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`Tm:real`; `g:real->real^N->real^K`; `FG:real^(1,N)finite_sum->real^K`;
                   `j:num`; `l:num list`; `tau:real`; `x:real^N`] PDE_MX_SLICE_TDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH `norm(a:real^K) <= k ==> norm(a + b) <= k + norm b`) THEN
  MP_TAC(ISPECL [`S3:real^(1,N)finite_sum->bool`; `s + j:num`; `A:real`;
                 `\z:real^(1,N)finite_sum. (aa:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)`;
                 `\z:real^(1,N)finite_sum i. (bb:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i`;
                 `\z:real^(1,N)finite_sum. (cc:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z)`;
                 `FU:real^(1,N)finite_sum->real^K`; `L:num list`; `w:real^(1,N)finite_sum`]
                PDE_STOP_ITERATED_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_POW_LE; REAL_POS; PDE_PJET_POS] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* the space-time jet of the extension, bounded by the jets of the slices *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_pjet (s + 2) j (FU:real^(1,N)finite_sum->real^K) w` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_PJET_MONO THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[pde_pjet] THEN EXPAND_TAC "Ls" THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[PDE_PJET_FINITE] THEN
  X_GEN_TAC `L3:num list` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Tm:real`; `u:real->real^N->real^K`; `FU:real^(1,N)finite_sum->real^K`;
                 `L3:num list`; `tau:real`; `x:real^N`] PDE_MX_EXT_JET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_jetn (s + 2) (pde_mx_tder (pde_ntime L3) (u:real->real^N->real^K) tau) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_ME_TERM_LE_JETN THEN
    MP_TAC(SPEC `L3:num list` PDE_MX_FILTER_SHIFT) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\m. pde_jetn (s + 2) (pde_mx_tder m (u:real->real^N->real^K) tau) x`;
                 `sum(0..j) (\m. pde_jetn (s + 2) (pde_mx_tder m (u:real->real^N->real^K) tau) x)`;
                 `0..j`] SUM_POS_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL; PDE_JETN_POS; IN_NUMSEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* Smoothness of real-valued combinations (lifted). *)

let PDE_MX_LIFT_ADD_SMOOTH = prove
 (`!f g:real^N->real.
     smooth_map_on (:real^N) (\x. lift(f x)) /\ smooth_map_on (:real^N) (\x. lift(g x))
     ==> smooth_map_on (:real^N) (\x. lift(f x + g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. lift(f x)`; `\x:real^N. lift(g x)`]
                SMOOTH_MAP_ON_LIFT_ADD) THEN
  REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let PDE_MX_LIFT_CMUL_SMOOTH = prove
 (`!c (f:real^N->real).
     smooth_map_on (:real^N) (\x. lift(f x))
     ==> smooth_map_on (:real^N) (\x. lift(c * f x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `c:real`; `\x:real^N. lift(f x)`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let PDE_MX_LIFT_SUM_SMOOTH = prove
 (`!(f:num->real^N->real) n.
     (!m. m IN 0..n ==> smooth_map_on (:real^N) (\x. lift(f m x)))
     ==> smooth_map_on (:real^N) (\x. lift(sum(0..n) (\m. f m x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\m (x:real^N). lift((f:num->real^N->real) m x)`; `0..n`]
                SMOOTH_MAP_ON_LIFT_SUM) THEN
  REWRITE_TAC[OPEN_UNIV; LIFT_DROP; FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Cube integral of K * sum_m S m + c * N. *)

let PDE_MX_CINT_COMB = prove
 (`!K2 c (S:num->real^N->real) (Nf:real^N->real) j.
     (!m. smooth_map_on (:real^N) (\x. lift(S m x))) /\
     smooth_map_on (:real^N) (\x. lift(Nf x))
     ==> pde_cint (\x. K2 * sum(0..j) (\m. S m x) + c * Nf x) =
         K2 * sum(0..j) (\m. pde_cint (S m)) + c * pde_cint Nf`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (\x. lift(sum(0..j) (\m. (S:num->real^N->real) m x)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_MX_LIFT_SUM_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. K2 * sum(0..j) (\m. (S:num->real^N->real) m x)`;
                 `\x:real^N. c * (Nf:real^N->real) x`] PDE_CINT_ADD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_MX_LIFT_CMUL_SMOOTH THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`K2:real`; `\x:real^N. sum(0..j) (\m. (S:num->real^N->real) m x)`]
                PDE_CINT_CMUL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`c:real`; `Nf:real^N->real`] PDE_CINT_CMUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`S:num->real^N->real`; `0..j`] PDE_CINT_SUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let PDE_MX_SQ_ARITH = prove
 (`!a b k J Q. &0 <= k /\ &0 <= J /\ &0 <= a /\ &0 <= b /\ a <= k * J + b /\ J pow 2 <= Q
               ==> a pow 2 <= &2 * k pow 2 * Q + &2 * b pow 2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(k * J + b) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `k * J - b` REAL_LE_POW_2) THEN
  SUBGOAL_THEN `k pow 2 * J pow 2 <= k pow 2 * Q` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Time trading in H^s. *)

let PDE_MX_TIME_TRADE = prove
 (`!Tm lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc T2 j s.
     pde_tcoeff Tm lam aa bb cc /\ &0 < T2 /\ T2 < Tm
     ==> ?C. &0 <= C /\
             !g u tau.
               pde_upto (&0) Tm (:real^N) g /\
               pde_tsol Tm aa bb cc g (\x. vec 0) u /\ &0 < tau /\ tau <= T2
               ==> pde_hs2 s (pde_mx_tder (SUC j) u tau) <=
                   C * (sum(0..j) (\m. pde_hs2 (s + 2) (pde_mx_tder m u tau)) +
                        pde_hs2 s (pde_mx_tder j g tau))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Tm:real`; `lam:real`; `aa:real->real^N->real^N^N`;
                 `bb:real->real^N->num->real^K^K`; `cc:real->real^N->real^K^K`;
                 `T2:real`; `j:num`; `s:num`] PDE_MX_TT_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Kt:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K2 = &2 * Kt pow 2 * &(j + 1) * &(CARD(pde_index_lists (s + 2) (:N)))` THEN
  SUBGOAL_THEN `&0 <= K2` ASSUME_TAC THENL
   [EXPAND_TAC "K2" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  EXISTS_TAC `&(CARD(pde_index_lists s (:N))) * K2 + &2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g:real->real^N->real^K`; `u:real->real^N->real^K`; `tau:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `tau < Tm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pde_upto (&0) Tm (:real^N) (u:real->real^N->real^K)` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pde_tsol]); ALL_TAC] THEN
  SUBGOAL_THEN `!m. smooth_map_on (:real^N) (pde_mx_tder m (u:real->real^N->real^K) tau) /\
                    smooth_map_on (:real^N) (pde_mx_tder m (g:real->real^N->real^K) tau)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN
    EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `SU = sum(0..j) (\m. pde_hs2 (s + 2) (pde_mx_tder m (u:real->real^N->real^K) tau))` THEN
  ABBREV_TAC `SG = pde_hs2 s (pde_mx_tder j (g:real->real^N->real^K) tau)` THEN
  SUBGOAL_THEN `&0 <= SU /\ &0 <= SG` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["SU"; "SG"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC PDE_HS2_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_HS2_POS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l IN pde_index_lists s (:N)
        ==> pde_cint (\x. norm(iterated_partial l
                                 (pde_mx_tder (SUC j) (u:real->real^N->real^K) tau) x) pow 2)
            <= K2 * SU +
               &2 * pde_cint (\x. norm(iterated_partial l
                                         (pde_mx_tder j (g:real->real^N->real^K) tau) x) pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!x. norm(iterated_partial l (pde_mx_tder (SUC j) (u:real->real^N->real^K) tau) x) pow 2 <=
          K2 * sum(0..j) (\m. sum (pde_index_lists (s + 2) (:N))
                                  (\l'. norm(iterated_partial l' (pde_mx_tder m u tau) x) pow 2)) +
          &2 * norm(iterated_partial l (pde_mx_tder j (g:real->real^N->real^K) tau) x) pow 2`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "K2" THEN
      MATCH_MP_TAC(REAL_ARITH
       `a <= &2 * k pow 2 * (n * (c * S)) + b ==> a <= (&2 * k pow 2 * n * c) * S + b`) THEN
      MATCH_MP_TAC PDE_MX_SQ_ARITH THEN
      EXISTS_TAC `sum(0..j) (\m. pde_jetn (s + 2) (pde_mx_tder m (u:real->real^N->real^K) tau) x)` THEN
      REWRITE_TAC[NORM_POS_LE] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[PDE_JETN_POS];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(CARD(0..j)) *
                  sum(0..j) (\m. pde_jetn (s + 2) (pde_mx_tder m (u:real->real^N->real^K) tau) x pow 2)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC PDM_SUM_SQUARE_LE THEN REWRITE_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
      REWRITE_TAC[CARD_NUMSEG; SUB_0] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      ONCE_REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      REWRITE_TAC[PDE_ME_JETN_SQ];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `pde_cint (\x. K2 * sum(0..j) (\m. sum (pde_index_lists (s + 2) (:N))
                       (\l'. norm(iterated_partial l' (pde_mx_tder m (u:real->real^N->real^K) tau) x) pow 2)) +
                    &2 * norm(iterated_partial l (pde_mx_tder j (g:real->real^N->real^K) tau) x) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_CINT_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
        ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX];
        MATCH_MP_TAC PDE_MX_LIFT_ADD_SMOOTH THEN CONJ_TAC THEN
        MATCH_MP_TAC PDE_MX_LIFT_CMUL_SMOOTH THENL
         [MATCH_MP_TAC PDE_MX_LIFT_SUM_SMOOTH THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC PDE_ME_SQSUM_SMOOTH THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
          ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX]]];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`K2:real`; `&2`;
      `\m (x:real^N). sum (pde_index_lists (s + 2) (:N))
                         (\l'. norm(iterated_partial l' (pde_mx_tder m (u:real->real^N->real^K) tau) x) pow 2)`;
      `\x:real^N. norm(iterated_partial l (pde_mx_tder j (g:real->real^N->real^K) tau) x) pow 2`;
      `j:num`] PDE_MX_CINT_COMB) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `m:num` THEN MATCH_MP_TAC PDE_ME_SQSUM_SMOOTH THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
        ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX]];
      DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "SU" THEN ASM_SIMP_TAC[GSYM PDE_ME_HS2_SQSUM; REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists s (:N))
                  (\l. K2 * SU + &2 * pde_cint (\x. norm(iterated_partial l
                                     (pde_mx_tder j (g:real->real^N->real^K) tau) x) pow 2))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PDE_HS2_CINT] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_SIMP_TAC[PDE_INDEX_LISTS_FINITE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; SUM_CONST; PDE_INDEX_LISTS_FINITE] THEN
  SUBGOAL_THEN
   `sum (pde_index_lists s (:N))
        (\l. pde_cint (\x. norm(iterated_partial l
                                (pde_mx_tder j (g:real->real^N->real^K) tau) x) pow 2)) = SG`
  SUBST1_TAC THENL [EXPAND_TAC "SG" THEN REWRITE_TAC[PDE_HS2_CINT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &(CARD(pde_index_lists s (:N))) * K2 * SG` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL]; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= SU` THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Analytic core, part 3: the transfer identity (R1).  The torus commutator  *)
(* families pde_mx_tc j and their chart representatives pde_mx_wr r j (time  *)
(* derivatives of order r, cut off outside the ball of radius lam j / 4);    *)
(* the residual family R Fm is the chart-field sum pde_mx_fw of pde_mx_wr 0, *)
(* and the time derivatives of the forcings g i (R Fm) are g i of the        *)
(* chart-field sums of pde_mx_wr r (PDE_MX_TDER_G_R).                        *)
(* ========================================================================= *)

let pde_mx_pt = new_definition
 `pde_mx_pt (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real) (lam:num->real) j =
    pdm_transplant (lam j) (\z. lift(pde_mx_psic cs psi j z))`;;

let pde_mx_tc = new_definition
 `pde_mx_tc (aaT:num->real->real^N->real^N^N)
            (bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod)
            (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real) (lam:num->real)
            (P:num->real->real^N->real^(N,N)finite_prod) j (tau:real) =
    pde_mt_comm (aaT j tau) (bbT j tau) (pde_mx_pt cs psi lam j) (P j tau)`;;

let pde_mx_wr = new_definition
 `pde_mx_wr (aaT:num->real->real^N->real^N^N)
            (bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod)
            (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real) (lam:num->real)
            (P:num->real->real^N->real^(N,N)finite_prod) a r j (t:real) (z:real^N) =
    if norm z < lam j / &4
    then pde_mx_tder r (pde_mx_tc aaT bbT cs psi lam P j) (t - a)
                     (inv(lam j) % z + inv(&2) % vec 1)
    else vec 0`;;

let pde_mx_fw = new_definition
 `pde_mx_fw (atlas:((A->bool)#(A->real^N))->bool) (cs:num->(A->bool)#(A->real^N)) n0
            (W:num->real->real^N->real^(N,N)finite_prod) (t:real) (x:A) =
    (matrify:real^(N,N)finite_prod->real^N^N)
     (vsum {j | j < n0}
       (\j. (vectorize:real^N^N->real^(N,N)finite_prod)
              (pdm_chart_field atlas (cs j)
                 (\z. (matrify:real^(N,N)finite_prod->real^N^N) (W j t z)) x)))`;;

(* Time-derivative slices and one-dimensional derivatives. *)

let PDE_MX_TDER_0 = prove
 (`!(u:real->real^N->real^K) tau. pde_mx_tder 0 u tau = u tau`,
  REWRITE_TAC[FUN_EQ_THM; pde_mx_tder; REPLICATE; iterated_partial;
              FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]);;

let PDE_MX_TDER_DERIV = prove
 (`!Tm (u:real->real^N->real^K) m tau x.
     pde_upto (&0) Tm (:real^N) u /\ &0 < tau /\ tau < Tm
     ==> ((\s. pde_mx_tder m u (drop s) x) has_vector_derivative
          pde_mx_tder (SUC m) u tau x) (at (lift tau))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_tder; LIFT_DROP; REPLICATE; iterated_partial] THEN
  MATCH_MP_TAC PDE_ST_TIME_DERIV THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `interval(lift(&0),lift Tm) PCROSS (:real^N)` THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_INTERVAL_1;
           LIFT_DROP; IN_UNIV] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
  MATCH_MP_TAC PDE_MX_CANON_SMOOTH THEN ASM_REWRITE_TAC[]);;

let PDE_MX_HVD_LINEAR = prove
 (`!(L:real^M->real^P) (f:real^1->real^M) f' x.
     linear L /\ (f has_vector_derivative f') (at x)
     ==> ((\s. L(f s)) has_vector_derivative L f') (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN `(\h. drop h % (L:real^M->real^P) f') = L o (\h. drop h % f')` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[LINEAR_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `(\s. (L:real^M->real^P) (f s)) = L o (f:real^1->real^M)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; GSYM has_vector_derivative]);;

let PDE_MX_HVD_VSUM = prove
 (`!(f:B->real^1->real^M) f' s x.
     FINITE s /\ (!b. b IN s ==> (f b has_vector_derivative f' b) (at x))
     ==> ((\t. vsum s (\b. f b t)) has_vector_derivative vsum s f') (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN `(\h. drop h % vsum s (f':B->real^M)) = (\h. vsum s (\b. drop h % f' b))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VSUM_LMUL]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN ASM_REWRITE_TAC[GSYM has_vector_derivative]);;

let PDE_MX_HVD_TRIPLE = prove
 (`!(J:real^N^N) (FF:real^1->real^N^N) FF' x.
     ((\s. (vectorize:real^N^N->real^(N,N)finite_prod) (FF s)) has_vector_derivative
      vectorize FF') (at x)
     ==> ((\s. (vectorize:real^N^N->real^(N,N)finite_prod) (transp J ** FF s ** J))
          has_vector_derivative vectorize(transp J ** FF' ** J)) (at x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\v. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (transp (J:real^N^N) ** matrify v ** J)`;
                 `\s. (vectorize:real^N^N->real^(N,N)finite_prod) ((FF:real^1->real^N^N) s)`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) FF'`; `x:real^1`]
                PDE_MX_HVD_LINEAR) THEN
  ASM_REWRITE_TAC[PDE_MX_TRIPLE_LINEAR; MATRIFY_VECTORIZE]);;

(* The chart representatives: derivatives in time. *)

let PDE_MX_WR_DERIV = prove
 (`!aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam (P:num->real->real^N->real^(N,N)finite_prod)
    a Tm r j tau (z:real^N).
     pde_upto (&0) Tm (:real^N) (pde_mx_tc aaT bbT cs psi lam P j) /\ &0 < tau /\ tau < Tm
     ==> ((\s. pde_mx_wr aaT bbT cs psi lam P a r j (drop s + a) z) has_vector_derivative
          pde_mx_wr aaT bbT cs psi lam P a (SUC r) j (tau + a) z) (at (lift tau))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_wr; REAL_ARITH `(x + a) - a:real = x`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
  MP_TAC(ISPECL [`Tm:real`; `pde_mx_tc aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                    (P:num->real->real^N->real^(N,N)finite_prod) j`; `r:num`; `tau:real`;
                 `inv((lam:num->real) j) % z + inv(&2) % vec 1:real^N`] PDE_MX_TDER_DERIV) THEN
  ASM_REWRITE_TAC[]);;

let PDE_MX_FW_DERIV = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) cs n0 W W' a tau (x:A).
     (!j z. j < n0
            ==> ((\s. W j (drop s + a) z) has_vector_derivative W' j (tau + a) z)
                (at (lift tau)))
     ==> ((\s. (vectorize:real^N^N->real^(N,N)finite_prod)
                 (pde_mx_fw atlas cs n0 W (drop s + a) x)) has_vector_derivative
          vectorize(pde_mx_fw atlas cs n0 W' (tau + a) x)) (at (lift tau))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_fw; VECTORIZE_MATRIFY] THEN
  MATCH_MP_TAC PDE_MX_HVD_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[pdm_chart_field] THEN COND_CASES_TAC THEN
  REWRITE_TAC[VECTORIZE_0; HAS_VECTOR_DERIVATIVE_CONST] THEN
  REWRITE_TAC[mpullback] THEN MATCH_MP_TAC PDE_MX_HVD_TRIPLE THEN
  REWRITE_TAC[VECTORIZE_MATRIFY; ETA_AX] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let PDE_MX_G_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a cs chi lam i (Fm:real->A->real^N^N) Fm' tau y.
     smooth_manifold_atlas top atlas /\ cs i IN atlas /\
     (!x. x IN topspace top
          ==> ((\s. (vectorize:real^N^N->real^(N,N)finite_prod) (Fm (drop s + a) x))
               has_vector_derivative vectorize(Fm' (tau + a) x)) (at (lift tau)))
     ==> ((\s. pde_mx_g atlas a cs chi lam i Fm (drop s) y) has_vector_derivative
          pde_mx_g atlas a cs chi lam i Fm' tau y) (at (lift tau))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_g; pdm_transplant; pdm_periodize] THEN
  ABBREV_TAC `z0 = (lam:num->real) i % (pdm_frac (y:real^N) - inv(&2) % vec 1)` THEN
  ASM_CASES_TAC `(z0:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[pde_mx_psic; VECTOR_MUL_LZERO; HAS_VECTOR_DERIVATIVE_CONST]] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN REWRITE_TAC[metric_local] THEN
  MATCH_MP_TAC PDE_MX_HVD_TRIPLE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Accessor for the data. *)

let PDE_MX_DATA_PIECE = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E i.
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ i < n0
     ==> a < b' /\ cs i IN atlas /\ compact(ks i) /\
         ks i SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
         &1 <= lam i /\ ks i SUBSET ball(vec 0,lam i / &4) /\
         pde_tcoeff (b' - a) (lamT i) (aaT i) (bbT i) (ccT i) /\
         ?V. open V /\ ks i SUBSET V /\ V SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
             !t z. a <= t /\ t < b' /\ z IN V
                   ==> aaT i (t - a) (inv(lam i) % z + inv(&2) % vec 1) =
                         inv(lam i pow 2) %% pde_mlaa atlas (cs i) k t z /\
                       (!j. 1 <= j /\ j <= dimindex(:N)
                            ==> bbT i (t - a) (inv(lam i) % z + inv(&2) % vec 1) j =
                                inv(lam i) %% pde_mlbt atlas (cs i) k h t z j) /\
                       ccT i (t - a) (inv(lam i) % z + inv(&2) % vec 1) =
                         pde_mlct atlas (cs i) k h t z`,
  REWRITE_TAC[pde_mx_data; pde_cover] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[]);;

(* The commutator in chart coordinates is the torus commutator, dilated. *)

let PDE_MX_COMM_WR0 = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E Fm j t z.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ j < n0 /\
     pde_tfam_from atlas a b' Fm /\ a <= t /\ t < b'
     ==> pde_mx_comm atlas a k h cs psi chi lam E j Fm t z =
         pde_mx_wr aaT bbT cs psi lam (\j. pde_mx_u atlas a cs chi lam E j Fm) a 0 j t z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_DATA_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_DATA_PSIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (lam:num->real) j` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `uj = pde_mx_u atlas a cs chi lam
                     (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                     j (Fm:real->A->real^N^N)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) ((uj:real->real^N->real^(N,N)finite_prod) (t - a))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `j:num`; `Fm:real->A->real^N^N`] PDE_MX_U_TSOL) THEN
    ASM_REWRITE_TAC[pde_tsol] THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_ML_UPTO_SLICE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b' - a:real`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. lam j / &4 < norm z ==>
                  lift(pde_mx_psic (cs:num->(A->bool)#(A->real^N)) psi j z) = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ks (j:num) SUBSET ball(vec 0:real^N,lam j / &4)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_MESON_TAC[REAL_LT_ANTISYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(ks (j:num):real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[pde_mx_comm; pde_mx_wr; PDE_MX_TDER_0; PDE_MX_W_FUN; pde_mx_tc] THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `~((z:real^N) IN ks (j:num))` ASSUME_TAC THENL
     [UNDISCH_TAC `ks (j:num) SUBSET ball(vec 0:real^N,lam j / &4)` THEN
      REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN EXISTS_TAC `(:real^N) DIFF ks (j:num)` THEN
    REWRITE_TAC[GSYM closed; IN_DIFF; IN_UNIV] THEN ASM_SIMP_TAC[LIFT_NUM]] THEN
  (* the torus commutator at the dilated point *)
  MP_TAC(ISPECL [`(lam:num->real) j`;
                 `(aaT:num->real->real^N->real^N^N) j (t - a)`;
                 `(bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) j (t - a)`;
                 `pde_mx_pt (cs:num->(A->bool)#(A->real^N)) psi lam j`;
                 `(uj:real->real^N->real^(N,N)finite_prod) (t - a)`;
                 `\z:real^N. lam j pow 2 %% (aaT:num->real->real^N->real^N^N) j (t - a)
                                 (inv(lam j) % z + inv(&2) % vec 1)`;
                 `\(z:real^N) i. lam j %%
                    (bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) j (t - a)
                      (inv(lam j) % z + inv(&2) % vec 1) i`;
                 `z:real^N`] PDE_ME_COMM_DILATE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_POW_NZ; REAL_LT_IMP_NZ; MATRIX_CMUL_LID] THEN
    REWRITE_TAC[pde_mx_pt] THEN MATCH_MP_TAC PDM_TRANSPLANT_SMOOTH THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `pde_mt_comm (\z:real^N. lam j pow 2 %% (aaT:num->real->real^N->real^N^N) j (t - a)
                              (inv(lam j) % z + inv(&2) % vec 1))
                (\(z:real^N) i. lam j %%
                   (bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) j (t - a)
                     (inv(lam j) % z + inv(&2) % vec 1) i)
                (\z. lift(pde_mx_psic (cs:num->(A->bool)#(A->real^N)) psi j z))
                (\z. (uj:real->real^N->real^(N,N)finite_prod) (t - a)
                       (inv(lam j) % z + inv(&2) % vec 1)) z` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC PDE_ME_COMM_LOCAL THEN EXISTS_TAC `ball(vec 0:real^N,lam (j:num) / &4)` THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[pde_mx_pt] THEN
    MP_TAC(ISPECL [`(lam:num->real) j`;
                   `\z:real^N. lift(pde_mx_psic (cs:num->(A->bool)#(A->real^N)) psi j z)`;
                   `y:real^N`] PDE_MX_TRANSPLANT_UNDILATE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)] THEN
  ASM_CASES_TAC `(z:real^N) IN ks (j:num)` THENL
   [MATCH_MP_TAC PDE_ME_COMM_COEFF_AT THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `z:real^N`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mlaa")) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_POW_NZ; REAL_LT_IMP_NZ; MATRIX_CMUL_LID];
    TRANS_TAC EQ_TRANS `vec 0:real^(N,N)finite_prod` THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
    MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN EXISTS_TAC `(:real^N) DIFF ks (j:num)` THEN
    REWRITE_TAC[GSYM closed; IN_DIFF; IN_UNIV] THEN ASM_SIMP_TAC[LIFT_NUM]]);;

(* The torus cutoffs and the torus commutator families are smooth. *)

let PDE_MX_PT_SMOOTH = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E j.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ j < n0
     ==> smooth_map_on (:real^N) (pde_mx_pt cs psi lam j) /\ pde_zper (pde_mx_pt cs psi lam j) /\
         (!z. norm z < lam j / &4
              ==> pde_mx_pt cs psi lam j (inv(lam j) % z + inv(&2) % vec 1) =
                  lift(pde_mx_psic cs psi j z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_DATA_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_DATA_PSIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (lam:num->real) j` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. lam j / &4 < norm z ==>
                  lift(pde_mx_psic (cs:num->(A->bool)#(A->real^N)) psi j z) = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ks (j:num) SUBSET ball(vec 0:real^N,lam j / &4)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_MESON_TAC[REAL_LT_ANTISYM];
    ALL_TAC] THEN
  REWRITE_TAC[pde_mx_pt; PDM_TRANSPLANT_ZPER] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDM_TRANSPLANT_SMOOTH THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(lam:num->real) j`;
                   `\z:real^N. lift(pde_mx_psic (cs:num->(A->bool)#(A->real^N)) psi j z)`;
                   `z:real^N`] PDE_MX_TRANSPLANT_UNDILATE) THEN
    ASM_REWRITE_TAC[]]);;

let PDE_MX_TC_UPTO = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E Fm j.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ j < n0 /\
     pde_tfam_from atlas a b' Fm
     ==> pde_upto (&0) (b' - a) (:real^N)
           (pde_mx_tc aaT bbT cs psi lam (\j. pde_mx_u atlas a cs chi lam E j Fm) j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_DATA_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_PT_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`; `Fm:real->A->real^N^N`] PDE_MX_U_TSOL) THEN
  ASM_REWRITE_TAC[pde_tsol] THEN STRIP_TAC THEN
  UNDISCH_TAC `pde_tcoeff (b' - a) ((lamT:num->real) j) ((aaT:num->real->real^N->real^N^N) j)
                 ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) j)
                 ((ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) j)` THEN
  REWRITE_TAC[pde_tcoeff] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pde_mx_tc aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
              (\j. pde_mx_u atlas a cs chi lam
                     (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                     j (Fm:real->A->real^N^N)) j =
    (\t z. pde_mt_comm ((aaT:num->real->real^N->real^N^N) j t)
             ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) j t)
             (pde_mx_pt cs psi lam j) (pde_mx_u atlas a cs chi lam E j Fm t) z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_mx_tc]; ALL_TAC] THEN
  MATCH_MP_TAC PDE_MT_COMM_UPTO THEN ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX]);;

(* The residual is the chart-field sum of the torus commutators. *)

let PDE_MX_R_FW0 = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E Fm t x.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' Fm /\ a <= t /\ t < b'
     ==> pde_mx_r atlas a k h cs psi chi lam E n0 Fm t x =
         pde_mx_fw atlas cs n0
           (pde_mx_wr aaT bbT cs psi lam (\j. pde_mx_u atlas a cs chi lam E j Fm) a 0) t x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_r; pde_mx_fw] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `z:real^N` THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `Fm:real->A->real^N^N`; `j:num`; `t:real`; `z:real^N`] PDE_MX_COMM_WR0) THEN
  ASM_REWRITE_TAC[]);;

(* Time derivatives of the transferred forcings. *)

let PDE_MX_TDER_G_R = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E Fm i.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' <= b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' Fm /\ i < n0
     ==> !r tau. &0 < tau /\ tau < b' - a
                 ==> pde_mx_tder r
                       (pde_mx_g atlas a cs chi lam i (pde_mx_r atlas a k h cs psi chi lam E n0 Fm))
                       tau =
                     pde_mx_g atlas a cs chi lam i
                       (pde_mx_fw atlas cs n0
                          (pde_mx_wr aaT bbT cs psi lam
                             (\j. pde_mx_u atlas a cs chi lam E j Fm) a r)) tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`] PDE_MX_DATA_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b' (pde_mx_r atlas a k h cs psi chi lam
                  (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                  n0 (Fm:real->A->real^N^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_MX_R_TFAM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `b:real`; `ks:num->real^N->bool`;
                          `aaT:num->real->real^N->real^N^N`;
                          `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_upto (&0) (b' - a) (:real^N)
                  (pde_mx_g atlas a cs chi lam i (pde_mx_r atlas a k h cs psi chi lam
                    (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                    n0 (Fm:real->A->real^N^N)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `i:num`;
                   `pde_mx_r atlas a k h cs psi chi lam
                      (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                      n0 (Fm:real->A->real^N^N)`] PDE_MX_G_UPTO) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < n0
        ==> pde_upto (&0) (b' - a) (:real^N)
              (pde_mx_tc aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                 (\j. pde_mx_u atlas a cs chi lam
                   (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                   j (Fm:real->A->real^N^N)) j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_MX_TC_UPTO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                          `n0:num`; `ks:num->real^N->bool`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_MX_TDER_0] THEN
    SUBGOAL_THEN
     `pde_mx_r atlas a k h cs psi chi lam
        (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
        n0 (Fm:real->A->real^N^N) (tau + a) =
      pde_mx_fw atlas cs n0
        (pde_mx_wr aaT bbT cs psi lam (\j. pde_mx_u atlas a cs chi lam E j Fm) a 0) (tau + a)`
    (fun th -> REWRITE_TAC[pde_mx_g; th]) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
    MATCH_MP_TAC PDE_MX_R_FW0 THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `b':real`; `ks:num->real^N->bool`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\s. pde_mx_tder r
                    (pde_mx_g atlas a cs chi lam i (pde_mx_r atlas a k h cs psi chi lam
                      (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                      n0 (Fm:real->A->real^N^N))) (drop s) (y:real^N)` THEN
  EXISTS_TAC `lift tau` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_MX_TDER_DERIV THEN EXISTS_TAC `b' - a:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. pde_mx_g atlas a cs chi lam i
                    (pde_mx_fw atlas cs n0
                       (pde_mx_wr aaT bbT cs psi lam
                          (\j. pde_mx_u atlas a cs chi lam
                            (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                            j (Fm:real->A->real^N^N)) a r)) (drop s) (y:real^N)` THEN
  EXISTS_TAC `min tau (b' - a - tau)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_1; LIFT_DROP] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop s` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mx_tder")) (concl th) &&
      is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC PDE_MX_G_DERIV THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC PDE_MX_FW_DERIV THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_MX_WR_DERIV THEN EXISTS_TAC `b' - a:real` THEN
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Analytic core, part 4: H^s bounds for the transfer (R1).  The forcing     *)
(* g i of a chart-field sum pde_mx_fw W is bounded in H^s by the chart H^s   *)
(* norms pde_mx_cn of the W j (PDE_MX_G_FW_BOUND), via the transplant, the   *)
(* localization of the M-norm and the chart-field norm.                      *)
(* ========================================================================= *)

let pde_mx_cn = new_definition
 `pde_mx_cn (c:(A->bool)#(A->real^N)) s (V:real^N->real^(N,N)finite_prod) =
    sum (pde_index_lists s (:N))
      (\l. drop(integral (IMAGE (SND c) (FST c))
                  (\y. lift(norm(iterated_partial l V y) pow 2))))`;;

let PDE_MX_CN_POS = prove
 (`!(c:(A->bool)#(A->real^N)) s V.
     open(IMAGE (SND c) (FST c)) /\ smooth_map_on (IMAGE (SND c) (FST c)) V /\
     (?k. compact k /\ k SUBSET IMAGE (SND c) (FST c) /\
          !y. y IN IMAGE (SND c) (FST c) /\ ~(y IN k) ==> V y = vec 0)
     ==> &0 <= pde_mx_cn c s V`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_cn] THEN MATCH_MP_TAC SUM_POS_LE THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `k:real^N->bool`;
                 `V:real^N->real^(N,N)finite_prod`; `l:num list`] PDM_SQNORM_INTEGRAL_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  MP_TAC(ISPECL [`\y:real^N. lift(norm(iterated_partial l (V:real^N->real^(N,N)finite_prod) y) pow 2)`;
                 `k:real^N->bool`] PDM_INTEGRABLE_CONTINUOUS_COMPACT) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX]);;

(* Real sums of smooth functions, and H^s of finite sums. *)

let PDE_MX_LIFT_SUMJ_SMOOTH = prove
 (`!(f:B->real^N->real) J.
     FINITE J /\ (!j. j IN J ==> smooth_map_on (:real^N) (\x. lift(f j x)))
     ==> smooth_map_on (:real^N) (\x. lift(sum J (\j. f j x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\j (x:real^N). lift((f:B->real^N->real) j x)`; `J:B->bool`]
                SMOOTH_MAP_ON_LIFT_SUM) THEN
  REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let PDE_MX_HS2_VSUM = prove
 (`!s (f:B->real^N->real^K) J.
     FINITE J /\ (!j. j IN J ==> smooth_map_on (:real^N) (f j))
     ==> pde_hs2 s (\z. vsum J (\j. f j z)) <= &(CARD J) * sum J (\j. pde_hs2 s (f j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_HS2_CINT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o rand o rand o snd) THEN
  ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!j. j IN J ==> smooth_map_on (:real^N)
                  (\x. lift(norm(iterated_partial l ((f:B->real^N->real^K) j) x) pow 2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(j:B) (x:real^N). norm(iterated_partial l ((f:B->real^N->real^K) j) x) pow 2`;
                 `J:B->bool`] PDE_CINT_SUM) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`&(CARD(J:B->bool))`;
                 `\x:real^N. sum J (\j. norm(iterated_partial l ((f:B->real^N->real^K) j) x) pow 2)`]
                PDE_CINT_CMUL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC PDE_MX_LIFT_SUMJ_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC PDE_CINT_LE THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN REWRITE_TAC[OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    MATCH_MP_TAC PDE_MX_LIFT_CMUL_SMOOTH THEN MATCH_MP_TAC PDE_MX_LIFT_SUMJ_SMOOTH THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN
    MP_TAC(ISPECL [`l:num list`; `(:real^N)`; `f:B->real^N->real^K`; `J:B->bool`]
                  PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC PDM_NORM_VSUM_SQ_LE THEN ASM_REWRITE_TAC[]]);;

(* The cut-off chart representative of a smooth tensor field is smooth. *)

let PDE_MX_CUT_SMOOTH = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) k (F0:A->real^N^N).
     smooth_manifold_atlas top atlas /\ c IN atlas /\ mfd_smooth atlas (\x. lift(phi x)) /\
     compact k /\ k SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) k) /\ pde_tensor_smooth atlas F0
     ==> smooth_map_on (:real^N)
           (\z. (if z IN IMAGE (SND c) (FST c) then phi(chart_inv c z) else &0) %
                (vectorize:real^N^N->real^(N,N)finite_prod) (metric_local atlas c F0 z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `k:real^N->bool`]
                PDE_ME_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `z0:real^N` THEN
  ASM_CASES_TAC `(z0:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THENL
   [EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^N. drop((\z. lift(if z IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)
                                           then (phi:A->real)(chart_inv c z) else &0)) z) %
                           (vectorize:real^N^N->real^(N,N)finite_prod)
                             (metric_local atlas c (F0:A->real^N^N) z)` THEN
    CONJ_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      UNDISCH_TAC `pde_tensor_smooth atlas (F0:A->real^N^N)` THEN
      REWRITE_TAC[pde_tensor_smooth] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
      ASM_REWRITE_TAC[o_DEF]];
    EXISTS_TAC `(:real^N) DIFF k` THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^N. vec 0:real^(N,N)finite_prod` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_DIFF; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]]);;

(* The H^s norm of the forcing of a smooth M-family is bounded by its M-norm. *)

let PDE_MX_G_HS2_MNORM = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E i s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ i < n0
     ==> ?C. &0 <= C /\
             !Fm tau. pde_tensor_smooth atlas (Fm (tau + a))
                      ==> pde_hs2 s (pde_mx_g atlas a cs chi lam i Fm tau) <=
                          C * pde_mnorm2 atlas n0 cs psi s (Fm (tau + a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`] PDE_MX_DATA_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`] PDE_MX_DATA_PSIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_mx_data]) THEN
  SUBGOAL_THEN
   `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((chi:num->A->real) i x)) /\
    (!x. ~(chi i x = &0) ==> x IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) i)) (ks i))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(psi:num->A->real) i x = &1` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
      can (find_term ((=) `psi:num->A->real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(chi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`; `s:num`] PDM_MNORM_LOCALIZE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C0:real`) THEN
  SUBGOAL_THEN `&0 < (lam:num->real) i` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  EXISTS_TAC `(lam:num->real) i pow (2 * s) * max C0 (&0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`Fm:real->A->real^N^N`; `tau:real`] THEN DISCH_TAC THEN
  ABBREV_TAC `G0 = \z. pde_mx_psic (cs:num->(A->bool)#(A->real^N)) chi i z %
                       (vectorize:real^N^N->real^(N,N)finite_prod)
                         (metric_local atlas (cs i) ((Fm:real->A->real^N^N) (tau + a)) z)` THEN
  SUBGOAL_THEN `pde_mx_g atlas a cs chi lam i (Fm:real->A->real^N^N) tau =
                pdm_transplant ((lam:num->real) i) (G0:real^N->real^(N,N)finite_prod)`
  SUBST1_TAC THENL [EXPAND_TAC "G0" THEN REWRITE_TAC[pde_mx_g]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (G0:real^N->real^(N,N)finite_prod)` ASSUME_TAC THENL
   [EXPAND_TAC "G0" THEN REWRITE_TAC[pde_mx_psic] THEN MATCH_MP_TAC PDE_MX_CUT_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `(ks:num->real^N->bool) i`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. ~(z IN (ks:num->real^N->bool) i) ==> (G0:real^N->real^(N,N)finite_prod) z = vec 0`
  ASSUME_TAC THENL
   [EXPAND_TAC "G0" THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(lam:num->real) i pow (2 * s) *
              sum (pde_index_lists s (:N))
                (\l. drop(integral (:real^N)
                       (\z. lift(norm(iterated_partial l (G0:real^N->real^(N,N)finite_prod) z)
                                 pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_ME_TRANSPLANT_HS2_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(ks:num->real^N->bool) i SUBSET ball(vec 0,lam i / &4)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_MESON_TAC[REAL_LT_ANTISYM];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C0 * pde_mnorm2 (atlas:((A->bool)#(A->real^N))->bool) n0 cs psi s
                               ((Fm:real->A->real^N^N) (tau + a))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
    MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(Fm:real->A->real^N^N) (tau + a)` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mnorm2")) (concl th) &&
    is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `x = y ==> y <= z ==> x <= z`) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN
  TRANS_TAC EQ_TRANS
   `integral ((ks:num->real^N->bool) i)
      (\z. lift(norm(iterated_partial l (G0:real^N->real^(N,N)finite_prod) z) pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDM_SQNORM_INTEGRAL_RESTRICT THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  TRANS_TAC EQ_TRANS
   `integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
      (\z. lift(norm(iterated_partial l (G0:real^N->real^(N,N)finite_prod) z) pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "G0" THEN
    ASM_REWRITE_TAC[pde_mx_psic; VECTORIZE_CMUL];
    MATCH_MP_TAC PDM_SQNORM_INTEGRAL_RESTRICT THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

let PDE_MX_G_SMOOTH_STATIC = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E i Fm tau.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ i < n0 /\
     pde_tensor_smooth atlas (Fm (tau + a))
     ==> smooth_map_on (:real^N) (pde_mx_g atlas a cs chi lam i Fm tau)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`] PDE_MX_DATA_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`] PDE_MX_DATA_PSIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_mx_data]) THEN
  REWRITE_TAC[pde_mx_g] THEN MATCH_MP_TAC PDM_TRANSPLANT_SMOOTH THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pde_mx_psic] THEN MATCH_MP_TAC PDE_MX_CUT_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `(ks:num->real^N->bool) i`] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(psi:num->A->real) i x = &1` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
      can (find_term ((=) `psi:num->A->real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~((z:real^N) IN (ks:num->real^N->bool) i)` ASSUME_TAC THENL
     [UNDISCH_TAC `(ks:num->real^N->bool) i SUBSET ball(vec 0,lam i / &4)` THEN
      REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
      ASM_MESON_TAC[REAL_LT_ANTISYM];
      ASM_SIMP_TAC[VECTOR_MUL_LZERO]]]);;

let PDE_MX_G_FW_BOUND = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E i s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ i < n0
     ==> ?C. &0 <= C /\
             !W tau. (!j. j < n0 ==> smooth_map_on (:real^N) (W j (tau + a)) /\
                                     (!z. ~(z IN ks j) ==> W j (tau + a) z = vec 0))
                     ==> pde_hs2 s (pde_mx_g atlas a cs chi lam i (pde_mx_fw atlas cs n0 W) tau) <=
                         C * sum {j | j < n0} (\j. pde_mx_cn (cs j) s (W j (tau + a)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_mx_data]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`; `s:num`] PDE_MX_G_HS2_MNORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Ci:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!j. ?Cj. j < n0
             ==> !W:real^N->real^N^N.
                   smooth_map_on (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))
                     ((vectorize:real^N^N->real^(N,N)finite_prod) o W) /\
                   (!z. z IN IMAGE (SND(cs j)) (FST(cs j)) /\ ~(z IN (ks:num->real^N->bool) j)
                        ==> W z = mat 0)
                   ==> pde_tensor_smooth atlas (pdm_chart_field atlas (cs j) W) /\
                       pde_mnorm2 atlas n0 cs psi s (pdm_chart_field atlas (cs j) W) <=
                       Cj * sum (pde_index_lists s (:N))
                              (\l. drop(integral (IMAGE (SND(cs j)) (FST(cs j)))
                                     (\y. lift(norm(iterated_partial l
                                            ((vectorize:real^N^N->real^(N,N)finite_prod) o W) y)
                                            pow 2))))`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN ASM_CASES_TAC `(j:num) < n0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `j:num`] PDE_MX_DATA_PIECE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC PDM_CHART_FIELD_NORM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Cf:num->real`)] THEN
  EXISTS_TAC `&n0 * Ci * sum {j | j < n0} (\j. abs((Cf:num->real) j))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`W:num->real->real^N->real^(N,N)finite_prod`; `tau:real`] THEN
  DISCH_TAC THEN
  (* each chart field: tensor smooth, M-norm bound *)
  SUBGOAL_THEN
   `!j. j < n0
        ==> pde_tensor_smooth atlas
              (pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) j)
                 (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                        ((W:num->real->real^N->real^(N,N)finite_prod) j (tau + a) z))) /\
            pde_mnorm2 atlas n0 cs psi s
              (pdm_chart_field atlas (cs j) (\z. matrify(W j (tau + a) z))) <=
            Cf j * pde_mx_cn (cs j) s (W j (tau + a))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `Cf:num->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `\z. (matrify:real^(N,N)finite_prod->real^N^N)
                                    ((W:num->real->real^N->real^(N,N)finite_prod) j (tau + a) z)`) THEN
    REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY; ETA_AX; pde_mx_cn] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIFY_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_mx_g atlas a cs chi lam i (pde_mx_fw atlas cs n0 (W:num->real->real^N->real^(N,N)finite_prod))
             tau =
    (\y. vsum {j | j < n0}
           (\j. pde_mx_g atlas a cs chi lam i
                  (\t x. pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) j)
                           (\z. (matrify:real^(N,N)finite_prod->real^N^N) (W j t z)) x) tau y))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `pde_mx_fw atlas (cs:num->(A->bool)#(A->real^N)) n0
                (W:num->real->real^N->real^(N,N)finite_prod) =
      (\t x. (matrify:real^(N,N)finite_prod->real^N^N)
               (vsum {j | j < n0}
                 (\j. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (pdm_chart_field atlas (cs j) (\z. matrify(W j t z)) x))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_mx_fw]; ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `cs:num->(A->bool)#(A->real^N)`; `chi:num->A->real`; `lam:num->real`; `i:num`;
                   `\m t x. pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) m)
                             (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                                    ((W:num->real->real^N->real^(N,N)finite_prod) m t z)) (x:A)`;
                   `{j:num | j < n0}`; `tau:real`; `y:real^N`] PDE_MX_G_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {j | j < n0}) *
              sum {j | j < n0}
                (\j. pde_hs2 s (pde_mx_g atlas a cs chi lam i
                       (\t x. pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) j)
                                (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                                       ((W:num->real->real^N->real^(N,N)finite_prod) j t z)) x)
                       tau))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:num`;
                   `\j. pde_mx_g (atlas:((A->bool)#(A->real^N))->bool) a cs chi lam i
                          (\t x. pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) j)
                                   (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                                          ((W:num->real->real^N->real^(N,N)finite_prod) j t z)) x)
                          tau`; `{j:num | j < n0}`] PDE_MX_HS2_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC PDE_MX_G_SMOOTH_STATIC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                          `n0:num`; `ks:num->real^N->bool`; `psi:num->A->real`;
                          `aaT:num->real->real^N->real^N^N`;
                          `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`;
                          `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`] THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[CARD_NUMSEG_LT; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Ci * pde_mnorm2 atlas n0 cs psi s
                (pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) j)
                   (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                          ((W:num->real->real^N->real^(N,N)finite_prod) j (tau + a) z)))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
     [`\t x. pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) j)
               (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                      ((W:num->real->real^N->real^(N,N)finite_prod) j t z)) x`; `tau:real`] o
     check (fun th -> can (find_term ((=) `Ci:real`)) (concl th) && is_forall (concl th))) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Cf:num->real) j * pde_mx_cn ((cs:num->(A->bool)#(A->real^N)) j) s
                ((W:num->real->real^N->real^(N,N)finite_prod) j (tau + a))` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((Cf:num->real) j)` THEN
    REWRITE_TAC[REAL_ABS_LE] THEN
    MP_TAC(ISPECL [`\j. abs((Cf:num->real) j)`; `sum {j | j < n0} (\j. abs((Cf:num->real) j))`;
                   `{j:num | j < n0}`] SUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; REAL_ABS_POS; REAL_LE_REFL; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_MX_CN_POS THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_DATA_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV];
    EXISTS_TAC `(ks:num->real^N->bool) j` THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Analytic core, part 5: the chart representatives pde_mx_wr are smooth,    *)
(* supported in ks j, and their chart H^s norms are bounded by the H^s norms *)
(* of the time-derivative slices of the torus commutators (PDE_MX_WR_PROPS). *)
(* ========================================================================= *)

let PDE_MX_INTEGRABLE_CC = prove
 (`!(f:real^N->real^1) k. f continuous_on k /\ compact k ==> f integrable_on k`,
  MESON_TAC[PDM_INTEGRABLE_CONTINUOUS_COMPACT]);;

let PDE_MX_TC_ZERO_NEAR = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E
    (P:num->real->real^N->real^(N,N)finite_prod) j r tau z.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ j < n0 /\
     norm z < lam j / &4 /\ ~(z IN ks j)
     ==> pde_mx_tder r (pde_mx_tc aaT bbT cs psi lam P j) tau
                       (inv(lam j) % z + inv(&2) % vec 1) = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_DATA_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_DATA_PSIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_PT_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (lam:num->real) j` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `S0 = {y:real^N | (lam:num->real) j % (y - inv(&2) % vec 1) IN
                               ball(vec 0,lam j / &4) DIFF (ks:num->real^N->bool) j}` THEN
  SUBGOAL_THEN `open (S0:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S0" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_BALL; COMPACT_IMP_CLOSED] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
    REWRITE_TAC[CONTINUOUS_AT_ID; CONTINUOUS_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN S0 ==> pde_mx_pt (cs:num->(A->bool)#(A->real^N)) psi lam j y = vec 0`
  ASSUME_TAC THENL
   [EXPAND_TAC "S0" THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_BALL_0] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(lam:num->real) j`; `y:real^N`] PDE_MT_DILATE_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM(CONJUNCT1 th)]) THEN
    ASM_SIMP_TAC[LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau' y:real^N. y IN S0
                    ==> pde_mx_tc aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                          (P:num->real->real^N->real^(N,N)finite_prod) j tau' y = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_tc] THEN MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN
    EXISTS_TAC `S0:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pde_mx_tder] THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
  EXISTS_TAC `(:real^1) PCROSS (S0:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV; FORALL_PASTECART;
               FSTCART_PASTECART; SNDCART_PASTECART] THEN
  EXPAND_TAC "S0" THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_BALL_0] THEN
  MP_TAC(ISPECL [`(lam:num->real) j`; `z:real^N`] PDE_MT_DILATE_INV) THEN
  ASM_SIMP_TAC[]);;

let PDE_MX_WR_PROPS = prove
 (`!top atlas a b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E
    (P:num->real->real^N->real^(N,N)finite_prod) j r t s.
     smooth_manifold_atlas top atlas /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\ j < n0 /\
     pde_upto (&0) (b' - a) (:real^N) (pde_mx_tc aaT bbT cs psi lam P j) /\
     a < t /\ t < b'
     ==> smooth_map_on (:real^N) (pde_mx_wr aaT bbT cs psi lam P a r j t) /\
         (!z. ~(z IN ks j) ==> pde_mx_wr aaT bbT cs psi lam P a r j t z = vec 0) /\
         pde_mx_cn (cs j) s (pde_mx_wr aaT bbT cs psi lam P a r j t) <=
         lam j pow dimindex(:N) *
         pde_hs2 s (pde_mx_tder r (pde_mx_tc aaT bbT cs psi lam P j) (t - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_DATA_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (lam:num->real) j` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `VV = pde_mx_tder r (pde_mx_tc aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                    (P:num->real->real^N->real^(N,N)finite_prod) j) (t - a)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (VV:real^N->real^(N,N)finite_prod)` ASSUME_TAC THENL
   [EXPAND_TAC "VV" THEN MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN EXISTS_TAC `b' - a:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. pde_mx_wr aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
          (P:num->real->real^N->real^(N,N)finite_prod) a r j t z =
        if norm z < lam j / &4 then (VV:real^N->real^(N,N)finite_prod)
                                      (inv(lam j) % z + inv(&2) % vec 1)
        else vec 0`
  (LABEL_TAC "wreq") THENL [EXPAND_TAC "VV" THEN REWRITE_TAC[pde_mx_wr]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. ~(z IN (ks:num->real^N->bool) j)
        ==> pde_mx_wr aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
              (P:num->real->real^N->real^(N,N)finite_prod) a r j t z = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN USE_THEN "wreq" (fun th -> REWRITE_TAC[th]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "VV" THEN
    MATCH_MP_TAC PDE_MX_TC_ZERO_NEAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                          `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                          `ks:num->real^N->bool`; `chi:num->A->real`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`;
                          `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^N)
                  (\z. (VV:real^N->real^(N,N)finite_prod) (inv(lam (j:num)) % z + inv(&2) % vec 1))`
  ASSUME_TAC THENL [MATCH_MP_TAC PDM_SMOOTH_AFFINE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball(vec 0,lam j / &4)
        ==> pde_mx_wr aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
              (P:num->real->real^N->real^(N,N)finite_prod) a r j t y =
            (VV:real^N->real^(N,N)finite_prod) (inv(lam j) % y + inv(&2) % vec 1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN
    USE_THEN "wreq" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^N)
                  (pde_mx_wr aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                     (P:num->real->real^N->real^(N,N)finite_prod) a r j t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `z0:real^N` THEN ASM_CASES_TAC `norm(z0:real^N) < lam (j:num) / &4` THENL
     [EXISTS_TAC `ball(vec 0:real^N,lam (j:num) / &4)` THEN
      ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
      EXISTS_TAC `\z. (VV:real^N->real^(N,N)finite_prod) (inv(lam (j:num)) % z + inv(&2) % vec 1)` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      EXISTS_TAC `(:real^N) DIFF (ks:num->real^N->bool) j` THEN
      ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(ks:num->real^N->bool) j SUBSET ball(vec 0,lam j / &4)` THEN
        REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\z:real^N. vec 0:real^(N,N)finite_prod` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_DIFF; IN_UNIV] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
        is_neg(lhand(snd(dest_forall(concl th)))))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "wreq" (K ALL_TAC) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* the chart norm *)
  SUBGOAL_THEN `open(IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  REWRITE_TAC[pde_mx_cn] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (pde_index_lists s (:N))
      (\l. drop(integral (interval[--(lam (j:num) / &2) % vec 1,(lam j / &2) % vec 1])
                  (\z. lift(norm(iterated_partial l
                         (\z. (VV:real^N->real^(N,N)finite_prod) (inv(lam j) % z + inv(&2) % vec 1))
                         z) pow 2))))` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC PDM_UNTRANSPLANT_NORM THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))`;
                 `(ks:num->real^N->bool) j`;
                 `pde_mx_wr aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                    (P:num->real->real^N->real^(N,N)finite_prod) a r j t`;
                 `l:num list`] PDM_SQNORM_INTEGRAL_RESTRICT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `integral ((ks:num->real^N->bool) j)
      (\y. lift(norm(iterated_partial l
             (pde_mx_wr aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                (P:num->real->real^N->real^(N,N)finite_prod) a r j t) y) pow 2)) =
    integral (ks j)
      (\y. lift(norm(iterated_partial l
             (\z. (VV:real^N->real^(N,N)finite_prod) (inv(lam j) % z + inv(&2) % vec 1)) y) pow 2))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `ball(vec 0:real^N,lam (j:num) / &4)` THEN
    REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^N,lam (j:num) / &4)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL_0; IN_INTERVAL; VECTOR_NEG_COMPONENT;
                                       VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`y:real^N`; `i:num`] COMPONENT_LE_NORM) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC PDE_MX_INTEGRABLE_CC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX];
    MATCH_MP_TAC PDE_MX_INTEGRABLE_CC THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX];
    REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2]]);;

(* ========================================================================= *)
(* Analytic core, part 6: time derivatives of the torus commutators (lossy   *)
(* bound, R1 in time).  A general passage from pointwise jet bounds to H^s   *)
(* bounds (PDE_MX_HS2_FROM_POINT), pointwise bounds for the operator applied *)
(* to a family (PDE_MX_STOP_JET_BOUND, PDE_MX_LOP_TDER_POINT), and the       *)
(* commutator bound PDE_MX_TCOMM_TDER_BOUND.                                 *)
(* ========================================================================= *)

let PDE_MX_HS2_FROM_POINT = prove
 (`!s d j Kt. &0 <= Kt
     ==> ?C. &0 <= C /\
             !(F0:real^N->real^K) (G:num->real^N->real^K) (H:real^N->real^K).
               smooth_map_on (:real^N) F0 /\ (!m. smooth_map_on (:real^N) (G m)) /\
               smooth_map_on (:real^N) H /\
               (!l x. l IN pde_index_lists s (:N)
                      ==> norm(iterated_partial l F0 x) <=
                          Kt * sum(0..j) (\m. pde_jetn (s + d) (G m) x) +
                          norm(iterated_partial l H x))
               ==> pde_hs2 s F0 <=
                   C * (sum(0..j) (\m. pde_hs2 (s + d) (G m)) + pde_hs2 s H)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K2 = &2 * Kt pow 2 * &(j + 1) * &(CARD(pde_index_lists (s + d) (:N)))` THEN
  SUBGOAL_THEN `&0 <= K2` ASSUME_TAC THENL
   [EXPAND_TAC "K2" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  EXISTS_TAC `&(CARD(pde_index_lists s (:N))) * K2 + &2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`F0:real^N->real^K`; `G:num->real^N->real^K`; `H:real^N->real^K`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `SU = sum(0..j) (\m. pde_hs2 (s + d) ((G:num->real^N->real^K) m))` THEN
  ABBREV_TAC `SG = pde_hs2 s (H:real^N->real^K)` THEN
  SUBGOAL_THEN `&0 <= SU /\ &0 <= SG` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["SU"; "SG"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC PDE_HS2_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_HS2_POS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l IN pde_index_lists s (:N)
        ==> pde_cint (\x. norm(iterated_partial l (F0:real^N->real^K) x) pow 2)
            <= K2 * SU + &2 * pde_cint (\x. norm(iterated_partial l (H:real^N->real^K) x) pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!x. norm(iterated_partial l (F0:real^N->real^K) x) pow 2 <=
          K2 * sum(0..j) (\m. sum (pde_index_lists (s + d) (:N))
                                  (\l'. norm(iterated_partial l' ((G:num->real^N->real^K) m) x)
                                        pow 2)) +
          &2 * norm(iterated_partial l (H:real^N->real^K) x) pow 2`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "K2" THEN
      MATCH_MP_TAC(REAL_ARITH
       `a <= &2 * k pow 2 * (n * (c * S)) + b ==> a <= (&2 * k pow 2 * n * c) * S + b`) THEN
      MATCH_MP_TAC PDE_MX_SQ_ARITH THEN
      EXISTS_TAC `sum(0..j) (\m. pde_jetn (s + d) ((G:num->real^N->real^K) m) x)` THEN
      REWRITE_TAC[NORM_POS_LE] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[PDE_JETN_POS];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(CARD(0..j)) *
                  sum(0..j) (\m. pde_jetn (s + d) ((G:num->real^N->real^K) m) x pow 2)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC PDM_SUM_SQUARE_LE THEN REWRITE_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
      REWRITE_TAC[CARD_NUMSEG; SUB_0] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      ONCE_REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      REWRITE_TAC[PDE_ME_JETN_SQ];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `pde_cint (\x. K2 * sum(0..j) (\m. sum (pde_index_lists (s + d) (:N))
                       (\l'. norm(iterated_partial l' ((G:num->real^N->real^K) m) x) pow 2)) +
                    &2 * norm(iterated_partial l (H:real^N->real^K) x) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_CINT_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
        ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX];
        MATCH_MP_TAC PDE_MX_LIFT_ADD_SMOOTH THEN CONJ_TAC THEN
        MATCH_MP_TAC PDE_MX_LIFT_CMUL_SMOOTH THENL
         [MATCH_MP_TAC PDE_MX_LIFT_SUM_SMOOTH THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC PDE_ME_SQSUM_SMOOTH THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
          ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX]]];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`K2:real`; `&2`;
      `\m (x:real^N). sum (pde_index_lists (s + d) (:N))
                         (\l'. norm(iterated_partial l' ((G:num->real^N->real^K) m) x) pow 2)`;
      `\x:real^N. norm(iterated_partial l (H:real^N->real^K) x) pow 2`;
      `j:num`] PDE_MX_CINT_COMB) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `m:num` THEN MATCH_MP_TAC PDE_ME_SQSUM_SMOOTH THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
        ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX]];
      DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "SU" THEN ASM_SIMP_TAC[GSYM PDE_ME_HS2_SQSUM; REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists s (:N))
                  (\l. K2 * SU + &2 * pde_cint (\x. norm(iterated_partial l
                                     (H:real^N->real^K) x) pow 2))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PDE_HS2_CINT] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_SIMP_TAC[PDE_INDEX_LISTS_FINITE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; SUM_CONST; PDE_INDEX_LISTS_FINITE] THEN
  SUBGOAL_THEN
   `sum (pde_index_lists s (:N))
        (\l. pde_cint (\x. norm(iterated_partial l (H:real^N->real^K) x) pow 2)) = SG`
  SUBST1_TAC THENL [EXPAND_TAC "SG" THEN REWRITE_TAC[PDE_HS2_CINT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &(CARD(pde_index_lists s (:N))) * K2 * SG` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL]; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= SU` THEN REAL_ARITH_TAC);;

(* Pointwise jet bounds for the space-time operator applied to an extension. *)

let PDE_MX_STOP_JET_BOUND = prove
 (`!Tm (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc T2 j s.
     pde_tbnd Tm aa bb cc /\ &0 < T2 /\ T2 < Tm
     ==> ?Kt. &0 <= Kt /\
              !v FV e tau x l.
                pde_upto (&0) Tm (:real^N) v /\ &0 < e /\
                smooth_map_on (interval(lift(&0 - e),lift Tm) PCROSS (:real^N)) FV /\
                (!t y. &0 <= t /\ t < Tm ==> FV(pastecart (lift t) y) = v t y) /\
                &0 < tau /\ tau <= T2 /\ l IN pde_index_lists s (:N)
                ==> norm(iterated_partial (APPEND (MAP (\k. 1 + k) l) (REPLICATE j 1))
                           (pde_stop (\z. aa (drop(fstcart z)) (sndcart z))
                                     (\z i. bb (drop(fstcart z)) (sndcart z) i)
                                     (\z. cc (drop(fstcart z)) (sndcart z)) FV)
                           (pastecart (lift tau) x)) <=
                    Kt * sum(0..j) (\m. pde_jetn (s + 2) (pde_mx_tder m v tau) x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `T3 = (T2 + Tm) / &2` THEN
  SUBGOAL_THEN `T2 < T3 /\ T3 < Tm` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T3" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`Tm:real`; `aa:real->real^N->real^N^N`; `bb:real->real^N->num->real^K^K`;
                 `cc:real->real^N->real^K^K`; `T3:real`; `s + j:num`] PDE_TBND_STBND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `A:real`)] THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pde_stbnd]); ALL_TAC] THEN
  ABBREV_TAC `Ls = {l | ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                        pde_ntime l <= j /\ LENGTH l <= (s + 2) + j /\
                        LENGTH l - pde_ntime l <= s + 2}` THEN
  EXISTS_TAC `&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * A * &2 pow (s + j) *
              &(CARD(Ls:num list->bool))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_POW_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:real->real^N->real^K`; `FV:real^(1,N)finite_sum->real^K`; `e:real`;
                       `tau:real`; `x:real^N`; `l:num list`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ LENGTH l <= s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `l IN pde_index_lists s (:N)` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S3 = interval(lift(&0),lift T3) PCROSS (:real^N)` THEN
  ABBREV_TAC `w = pastecart (lift tau) (x:real^N)` THEN
  SUBGOAL_THEN `open (S3:real^(1,N)finite_sum->bool) /\ w IN S3 /\
                smooth_map_on S3 (FV:real^(1,N)finite_sum->real^K)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S3"; "w"] THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_INTERVAL_1;
             LIFT_DROP; IN_UNIV] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - e),lift Tm) PCROSS (:real^N)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `L = APPEND (MAP (\k. 1 + k) (l:num list)) (REPLICATE j 1)` THEN
  SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) L /\
                LENGTH L = LENGTH (l:num list) + j /\ pde_ntime L = j`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    REWRITE_TAC[ALL_APPEND; LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE; PDE_NTIME_APPEND;
                PDE_NTIME_REPLICATE] THEN
    ASM_SIMP_TAC[PDE_MX_NTIME_SPACE; PDE_MAP_SUC_RANGE; ADD_CLAUSES] THEN
    MATCH_MP_TAC PDE_FT_ALL_REPLICATE THEN REWRITE_TAC[PDE_HEAT_DIMINDEX_ST] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S3:real^(1,N)finite_sum->bool`; `s + j:num`; `A:real`;
                 `\z:real^(1,N)finite_sum. (aa:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)`;
                 `\z:real^(1,N)finite_sum i. (bb:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i`;
                 `\z:real^(1,N)finite_sum. (cc:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z)`;
                 `FV:real^(1,N)finite_sum->real^K`; `L:num list`; `w:real^(1,N)finite_sum`]
                PDE_STOP_ITERATED_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_POW_LE; REAL_POS; PDE_PJET_POS] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* the space-time jet of the extension, bounded by the jets of the slices *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_pjet (s + 2) j (FV:real^(1,N)finite_sum->real^K) w` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_PJET_MONO THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[pde_pjet] THEN EXPAND_TAC "Ls" THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[PDE_PJET_FINITE] THEN
  X_GEN_TAC `L3:num list` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Tm:real`; `v:real->real^N->real^K`; `FV:real^(1,N)finite_sum->real^K`;
                 `L3:num list`; `tau:real`; `x:real^N`] PDE_MX_EXT_JET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_jetn (s + 2) (pde_mx_tder (pde_ntime L3) (v:real->real^N->real^K) tau) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_ME_TERM_LE_JETN THEN
    MP_TAC(SPEC `L3:num list` PDE_MX_FILTER_SHIFT) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\m. pde_jetn (s + 2) (pde_mx_tder m (v:real->real^N->real^K) tau) x`;
                 `sum(0..j) (\m. pde_jetn (s + 2) (pde_mx_tder m (v:real->real^N->real^K) tau) x)`;
                 `0..j`] SUM_POS_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL; PDE_JETN_POS; IN_NUMSEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* Pointwise bounds for time derivatives of the operator applied to a family. *)

let PDE_MX_LOP_TDER_POINT = prove
 (`!Tm (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc T2 j s.
     pde_tbnd Tm aa bb cc /\ &0 < T2 /\ T2 < Tm
     ==> ?Kt. &0 <= Kt /\
              !v tau x l.
                pde_upto (&0) Tm (:real^N) v /\ &0 < tau /\ tau <= T2 /\
                l IN pde_index_lists s (:N)
                ==> norm(iterated_partial l
                           (pde_mx_tder j (\t y. pde_lop aa bb cc v t y) tau) x) <=
                    Kt * sum(0..j) (\m. pde_jetn (s + 2) (pde_mx_tder m v tau) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Tm:real`; `aa:real->real^N->real^N^N`; `bb:real->real^N->num->real^K^K`;
                 `cc:real->real^N->real^K^K`; `T2:real`; `j:num`; `s:num`]
                PDE_MX_STOP_JET_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Kt:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `Kt:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`v:real->real^N->real^K`; `tau:real`; `x:real^N`; `l:num list`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:N)) l` ASSUME_TAC THENL
   [UNDISCH_TAC `l IN pde_index_lists s (:N)` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ASSUME `pde_upto (&0) Tm (:real^N) (v:real->real^N->real^K)`) THEN
  REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FV:real^(1,N)finite_sum->real^K`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pde_upto (&0) Tm (:real^N) (\t y. pde_lop aa bb cc (v:real->real^N->real^K) t y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_UPTO_LOP THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ASSUME `pde_upto (&0) Tm (:real^N) (\t y. pde_lop aa bb cc (v:real->real^N->real^K) t y)`) THEN
  REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `eL:real` (X_CHOOSE_THEN `FL:real^(1,N)finite_sum->real^K`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`Tm:real`; `\t y. pde_lop aa bb cc (v:real->real^N->real^K) t y`;
                 `FL:real^(1,N)finite_sum->real^K`; `j:num`; `l:num list`; `tau:real`;
                 `x:real^N`] PDE_MX_SLICE_TDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `iterated_partial (APPEND (MAP (\k. 1 + k) l) (REPLICATE j 1))
      (FL:real^(1,N)finite_sum->real^K) (pastecart (lift tau) x) =
    iterated_partial (APPEND (MAP (\k. 1 + k) l) (REPLICATE j 1))
      (pde_stop (\z:real^(1,N)finite_sum. (aa:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
                (\z i. (bb:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
                (\z. (cc:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))
                (FV:real^(1,N)finite_sum->real^K)) (pastecart (lift tau) x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `interval(lift(&0),lift Tm) PCROSS (:real^N)` THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV; FORALL_PASTECART] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s1:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`drop s1`; `y:real^N`] o check (fun th ->
      can (find_term ((=) `FL:real^(1,N)finite_sum->real^K`)) (concl th) &&
      is_forall (concl th))) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`aa:real->real^N->real^N^N`; `bb:real->real^N->num->real^K^K`;
                   `cc:real->real^N->real^K^K`; `v:real->real^N->real^K`;
                   `FV:real^(1,N)finite_sum->real^K`; `&0`; `Tm:real`; `drop s1`; `y:real^N`]
                  PDE_LOP_STOP_CANON) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - e),lift Tm) PCROSS (:real^N)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `Kt:real`)) (concl th) && is_forall (concl th))) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[]);;

(* Time derivatives of combinations with time-independent coefficients. *)

let PDE_MX_TDER_SUBP = prove
 (`!Tm (p:real^N->real^1) (Q:real->real^N->real^K) F1 F2.
     pde_upto (&0) Tm (:real^N) Q /\ pde_upto (&0) Tm (:real^N) F1 /\
     pde_upto (&0) Tm (:real^N) F2 /\
     (!t z. &0 <= t /\ t < Tm ==> Q t z = F1 t z - drop(p z) % F2 t z)
     ==> !r tau. &0 < tau /\ tau < Tm
                 ==> pde_mx_tder r Q tau =
                     (\z. pde_mx_tder r F1 tau z - drop(p z) % pde_mx_tder r F2 tau z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_MX_TDER_0; FUN_EQ_THM] THEN
    GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\s. pde_mx_tder r (Q:real->real^N->real^K) (drop s) y` THEN
  EXISTS_TAC `lift tau` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_MX_TDER_DERIV THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. pde_mx_tder r (F1:real->real^N->real^K) (drop s) y -
                  drop((p:real^N->real^1) y) % pde_mx_tder r (F2:real->real^N->real^K) (drop s) y` THEN
  EXISTS_TAC `min tau (Tm - tau)` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_1; LIFT_DROP] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop s` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mx_tder")) (concl th) &&
      is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_MX_TDER_DERIV THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
      MATCH_MP_TAC PDE_MX_TDER_DERIV THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[]]]);;

let PDE_MX_TDER_PMUL = prove
 (`!Tm (p:real^N->real^1) (u:real->real^N->real^K).
     smooth_map_on (:real^N) p /\ pde_upto (&0) Tm (:real^N) u
     ==> pde_upto (&0) Tm (:real^N) (\t z. drop(p z) % u t z) /\
         !r tau. &0 < tau /\ tau < Tm
                 ==> pde_mx_tder r (\t z. drop(p z) % u t z) tau =
                     (\z. drop(p z) % pde_mx_tder r u tau z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_upto (&0) Tm (:real^N) (\t z. drop((p:real^N->real^1) z) %
                                                  (u:real->real^N->real^K) t z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_MT_UPTO_SCALAR_MUL_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN
    MATCH_MP_TAC PDE_MT_UPTO_TIME_CONST THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN INDUCT_TAC THENL
   [REWRITE_TAC[PDE_MX_TDER_0]; ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\s. pde_mx_tder r (\t z. drop((p:real^N->real^1) z) %
                                       (u:real->real^N->real^K) t z) (drop s) y` THEN
  EXISTS_TAC `lift tau` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_MX_TDER_DERIV THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. drop((p:real^N->real^1) y) % pde_mx_tder r (u:real->real^N->real^K) (drop s) y` THEN
  EXISTS_TAC `min tau (Tm - tau)` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_1; LIFT_DROP] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop s` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mx_tder")) (concl th) &&
      is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
    MATCH_MP_TAC PDE_MX_TDER_DERIV THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[]]);;

(* Multiplication by a smooth periodic function in H^s. *)

let PDE_MX_HS2_PMUL = prove
 (`!(p:real^N->real^1) s.
     smooth_map_on (:real^N) p /\ pde_zper p
     ==> ?C. &0 <= C /\
             !w:real^N->real^K. smooth_map_on (:real^N) w
                                ==> pde_hs2 s (\z. drop(p z) % w z) <= C * pde_hs2 s w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^N->real^1`; `s:num`] PDE_ZPER_JET_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Ap:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:num`; `0`; `0`;
                 `(&(CARD(pde_index_lists s (:N))) * &2 pow s) * Ap`] PDE_MX_HS2_FROM_POINT) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_POS; REAL_POW_LE];
    DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N->real^K` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL [`\z:real^N. drop((p:real^N->real^1) z) % (w:real^N->real^K) z`;
                                 `\m:num. (w:real^N->real^K)`; `\z:real^N. vec 0:real^K`] o
                check (fun th -> can (find_term ((=) `C:real`)) (concl th) && is_forall (concl th))) THEN
  REWRITE_TAC[ADD_CLAUSES; SUM_SING_NUMSEG; ETA_AX; TEXT_ITERATED_PARTIAL_ZERO; NORM_0;
              REAL_ADD_RID; SMOOTH_MAP_ON_CONST] THEN
  SUBGOAL_THEN `pde_hs2 s (\z:real^N. vec 0:real^K) = &0` SUBST1_TAC THENL
   [REWRITE_TAC[PDE_HS2_CINT; TEXT_ITERATED_PARTIAL_ZERO; NORM_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[pde_cint; LIFT_NUM; INTEGRAL_0; DROP_VEC; SUM_0];
    REWRITE_TAC[REAL_ADD_RID]] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn s (\z:real^N. drop((p:real^N->real^1) z) % (w:real^N->real^K) z) x` THEN
    CONJ_TAC THENL [MATCH_MP_TAC PDE_ME_TERM_LE_JETN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:real^N->real^1`; `w:real^N->real^K`; `Ap:real`; `s:num`; `x:real^N`]
                  PDE_ME_JETN_DROPMUL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ACCEPT_TAC o MATCH_MP (REAL_ARITH `x <= a * b * c ==> x <= (a * b) * c`))]);;

(* Time derivatives of the operator applied to a family, in H^s. *)

let PDE_MX_LOP_TRADE = prove
 (`!Tm (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc T2 j s.
     pde_tbnd Tm aa bb cc /\ &0 < T2 /\ T2 < Tm
     ==> ?C. &0 <= C /\
             !v tau. pde_upto (&0) Tm (:real^N) v /\ &0 < tau /\ tau <= T2
                     ==> pde_hs2 s (pde_mx_tder j (\t y. pde_lop aa bb cc v t y) tau) <=
                         C * sum(0..j) (\m. pde_hs2 (s + 2) (pde_mx_tder m v tau))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Tm:real`; `aa:real->real^N->real^N^N`; `bb:real->real^N->num->real^K^K`;
                 `cc:real->real^N->real^K^K`; `T2:real`; `j:num`; `s:num`]
                PDE_MX_LOP_TDER_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Kt:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:num`; `2`; `j:num`; `Kt:real`] PDE_MX_HS2_FROM_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`v:real->real^N->real^K`; `tau:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_upto (&0) Tm (:real^N) (\t y. pde_lop aa bb cc (v:real->real^N->real^K) t y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_UPTO_LOP THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL
   [`pde_mx_tder j (\t y. pde_lop aa bb cc (v:real->real^N->real^K) t y) tau`;
    `\m. pde_mx_tder m (v:real->real^N->real^K) tau`; `\z:real^N. vec 0:real^K`] o
   check (fun th -> can (find_term ((=) `C:real`)) (concl th) && is_forall (concl th))) THEN
  REWRITE_TAC[TEXT_ITERATED_PARTIAL_ZERO; NORM_0; REAL_ADD_RID; SMOOTH_MAP_ON_CONST] THEN
  SUBGOAL_THEN `pde_hs2 s (\z:real^N. vec 0:real^K) = &0` SUBST1_TAC THENL
   [REWRITE_TAC[PDE_HS2_CINT; TEXT_ITERATED_PARTIAL_ZERO; NORM_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[pde_cint; LIFT_NUM; INTEGRAL_0; DROP_VEC; SUM_0];
    REWRITE_TAC[REAL_ADD_RID]] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    GEN_TAC THEN MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN EXISTS_TAC `Tm:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Time derivatives of torus commutators. *)

let PDE_MX_TCOMM_TDER_BOUND = prove
 (`!Tm lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc
    (p:real^N->real^1) T2 r s.
     pde_tcoeff Tm lam aa bb cc /\ smooth_map_on (:real^N) p /\ pde_zper p /\
     &0 < T2 /\ T2 < Tm
     ==> ?C. &0 <= C /\
             !u tau. pde_upto (&0) Tm (:real^N) u /\ &0 < tau /\ tau <= T2
                     ==> pde_hs2 s (pde_mx_tder r (\t. pde_mt_comm (aa t) (bb t) p (u t)) tau) <=
                         C * sum(0..r) (\m. pde_hs2 (s + 2) (pde_mx_tder m u tau))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pde_tbnd Tm (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K)
                         (cc:real->real^N->real^K^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_TCOEFF_TBND THEN EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Tm:real`; `aa:real->real^N->real^N^N`; `bb:real->real^N->num->real^K^K`;
                 `cc:real->real^N->real^K^K`; `T2:real`; `r:num`; `s:num`] PDE_MX_LOP_TRADE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p:real^N->real^1`; `s:num`] PDE_MX_HS2_PMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Cp:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p:real^N->real^1`; `s + 2`] PDE_MX_HS2_PMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Cq:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 * C1 * Cq + &2 * Cp * C1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real->real^N->real^K`; `tau:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `tau < Tm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`Tm:real`; `p:real^N->real^1`; `u:real->real^N->real^K`] PDE_MX_TDER_PMUL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `pu = \t z. drop((p:real^N->real^1) z) % (u:real->real^N->real^K) t z` THEN
  SUBGOAL_THEN
   `pde_upto (&0) Tm (:real^N) (\t y. pde_lop aa bb cc (pu:real->real^N->real^K) t y) /\
    pde_upto (&0) Tm (:real^N) (\t y. pde_lop aa bb cc (u:real->real^N->real^K) t y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_UPTO_LOP THEN EXISTS_TAC `Tm:real` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_upto (&0) Tm (:real^N)
      (\t. pde_mt_comm ((aa:real->real^N->real^N^N) t) ((bb:real->real^N->num->real^K^K) t) p
                       ((u:real->real^N->real^K) t))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pde_tcoeff Tm lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K)
                   (cc:real->real^N->real^K^K)` THEN
    REWRITE_TAC[pde_tcoeff] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\t. pde_mt_comm ((aa:real->real^N->real^N^N) t) ((bb:real->real^N->num->real^K^K) t) p
                       ((u:real->real^N->real^K) t)) =
      (\t z. pde_mt_comm (aa t) (bb t) p (u t) z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC PDE_MT_COMM_UPTO THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Tm:real`; `p:real^N->real^1`;
                 `\t. pde_mt_comm ((aa:real->real^N->real^N^N) t)
                                  ((bb:real->real^N->num->real^K^K) t) p
                                  ((u:real->real^N->real^K) t)`;
                 `\t y. pde_lop aa bb cc (pu:real->real^N->real^K) t y`;
                 `\t y. pde_lop aa bb cc (u:real->real^N->real^K) t y`] PDE_MX_TDER_SUBP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `smooth_map_on (:real^N) ((u:real->real^N->real^K) t)` ASSUME_TAC THENL
     [MATCH_MP_TAC PDE_ML_UPTO_SLICE_OPEN THEN MAP_EVERY EXISTS_TAC [`&0`; `Tm:real`] THEN
      ASM_REWRITE_TAC[OPEN_UNIV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(:real^N)`; `(aa:real->real^N->real^N^N) t`;
                   `(bb:real->real^N->num->real^K^K) t`; `(cc:real->real^N->real^K^K) t`;
                   `p:real^N->real^1`; `(u:real->real^N->real^K) t`; `z:real^N`]
                  PDE_MT_LOP0_CUTOFF) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    EXPAND_TAC "pu" THEN REWRITE_TAC[pde_lop; GSYM pde_lop0] THEN
    REWRITE_TAC[pde_lop0] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`r:num`; `tau:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `A1 = pde_mx_tder r (\t y. pde_lop aa bb cc (pu:real->real^N->real^K) t y) tau` THEN
  ABBREV_TAC `B1 = pde_mx_tder r (\t y. pde_lop aa bb cc (u:real->real^N->real^K) t y) tau` THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (A1:real^N->real^K) /\ smooth_map_on (:real^N) (B1:real^N->real^K)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A1"; "B1"] THEN CONJ_TAC THEN MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN
    EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * pde_hs2 s (A1:real^N->real^K) +
              &2 * pde_hs2 s (\z. drop((p:real^N->real^1) z) % (B1:real^N->real^K) z)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:num`; `A1:real^N->real^K`;
                   `\z. drop((p:real^N->real^1) z) % (B1:real^N->real^K) z`] PDE_ME_HS2_SUB) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_hs2 s (A1:real^N->real^K) <=
                C1 * Cq * sum(0..r) (\m. pde_hs2 (s + 2) (pde_mx_tder m (u:real->real^N->real^K) tau))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C1 * sum(0..r) (\m. pde_hs2 (s + 2) (pde_mx_tder m (pu:real->real^N->real^K) tau))` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "A1" THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `C1:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    EXPAND_TAC "pu" THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `tau:real`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mx_tder")) (concl th) &&
      is_forall (concl th) && not (can (find_term ((=) `C1:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `Cq:real`)) (concl th) && is_forall (concl th))) THEN
    MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_hs2 s (\z. drop((p:real^N->real^1) z) % (B1:real^N->real^K) z) <=
                Cp * C1 * sum(0..r) (\m. pde_hs2 (s + 2) (pde_mx_tder m (u:real->real^N->real^K) tau))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Cp * pde_hs2 s (B1:real^N->real^K)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `Cp:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "B1" THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `C1:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Analytic core, part 7: the transfer estimates (R1) for the Neumann        *)
(* iterates, tight in space (PDE_MX_R1_TIGHT) and lossy with time            *)
(* derivatives (PDE_MX_R1_TIME), and the base bounds (R0, PDE_MX_BASE_HS2).  *)
(* ========================================================================= *)

let PDE_MX_R1_CHAIN = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G t1 s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\ &0 < t1 /\ t1 < b' - a
     ==> ?C. &0 <= C /\
             !m r tau.
               &0 < tau /\ tau <= t1
               ==> sum {i | i < n0}
                     (\i. pde_hs2 s (pde_mx_tder r
                            (pde_mx_g atlas a cs chi lam i
                               (pde_mx_hh atlas a k h cs psi chi lam E n0 G (SUC m))) tau)) <=
                   C * sum {j | j < n0}
                         (\j. pde_hs2 s (pde_mx_tder r
                                (pde_mx_tc aaT bbT cs psi lam
                                   (\j. pde_mx_u atlas a cs chi lam E j
                                          (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)) j)
                                tau))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. ?Ci. i < n0
             ==> &0 <= Ci /\
                 !W tau. (!j. j < n0 ==> smooth_map_on (:real^N) (W j (tau + a)) /\
                                         (!z. ~(z IN (ks:num->real^N->bool) j)
                                              ==> W j (tau + a) z = vec 0))
                         ==> pde_hs2 s (pde_mx_g atlas a cs chi lam i
                                          (pde_mx_fw atlas (cs:num->(A->bool)#(A->real^N)) n0 W)
                                          tau) <=
                             Ci * sum {j | j < n0} (\j. pde_mx_cn (cs j) s (W j (tau + a)))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) < n0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_MX_G_FW_BOUND THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                          `psi:num->A->real`;
                          `aaT:num->real->real^N->real^N^N`;
                          `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`;
                          `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Cg:num->real`)] THEN
  SUBGOAL_THEN `!i. i < n0 ==> &0 <= (Cg:num->real) i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term ((=) `Cg:num->real`)) (concl th))) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `sum {i | i < n0} (\i. (Cg:num->real) i) *
              sum {j | j < n0} (\j. (lam:num->real) j pow dimindex(:N))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                     `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                     `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                     `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                     `aaT:num->real->real^N->real^N^N`;
                     `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                     `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                     `lamT:num->real`;
                     `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                     `x:num`] PDE_MX_DATA_PIECE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `r:num`; `tau:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `Hm = pde_mx_hh atlas a k h cs psi chi lam
                     (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                     n0 G m:real->A->real^N^N` THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b' (Hm:real->A->real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "Hm" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `G:real->A->real^N^N`] PDE_MX_HH_TFAM) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[pde_mx_hh] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `P = \j. pde_mx_u atlas a cs chi lam
                        (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                        j (Hm:real->A->real^N^N)` THEN
  SUBGOAL_THEN
   `!j. j < n0 ==> pde_upto (&0) (b' - a) (:real^N)
                     (pde_mx_tc aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                        (P:num->real->real^N->real^(N,N)finite_prod) j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "P" THEN MATCH_MP_TAC PDE_MX_TC_UPTO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                          `n0:num`; `ks:num->real^N->bool`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `LS = sum {j | j < n0} (\j. (lam:num->real) j pow dimindex(:N))` THEN
  ABBREV_TAC `SS = sum {j | j < n0}
                     (\j. pde_hs2 s (pde_mx_tder r
                            (pde_mx_tc aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                               (P:num->real->real^N->real^(N,N)finite_prod) j) tau))` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {i | i < n0} (\i. (Cg:num->real) i * (LS * SS))` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_RMUL; REAL_MUL_ASSOC; REAL_LE_REFL; ETA_AX]] THEN
  MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `Hm:real->A->real^N^N`; `i:num`] PDE_MX_TDER_G_R) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(MP_TAC o SPECL [`r:num`; `tau:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!j. j < n0
        ==> smooth_map_on (:real^N)
              (pde_mx_wr aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                 (P:num->real->real^N->real^(N,N)finite_prod) a r j (tau + a)) /\
            (!z. ~(z IN (ks:num->real^N->bool) j)
                 ==> pde_mx_wr aaT bbT cs psi lam P a r j (tau + a) z = vec 0) /\
            pde_mx_cn (cs j) s (pde_mx_wr aaT bbT cs psi lam P a r j (tau + a)) <=
            (lam:num->real) j pow dimindex(:N) *
            pde_hs2 s (pde_mx_tder r (pde_mx_tc aaT bbT cs psi lam P j) tau)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `P:num->real->real^N->real^(N,N)finite_prod`; `j:num`; `r:num`;
                   `tau + a:real`; `s:num`] PDE_MX_WR_PROPS) THEN
    ASM_SIMP_TAC[REAL_ARITH `(tau + a) - a:real = tau`] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Cg:num->real) i *
              sum {j | j < n0}
                (\j. pde_mx_cn ((cs:num->(A->bool)#(A->real^N)) j) s
                       (pde_mx_wr aaT bbT cs psi lam (P:num->real->real^N->real^(N,N)finite_prod)
                          a r j (tau + a)))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term ((=) `Cg:num->real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mx_fw")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {j | j < n0}
                (\j. (lam:num->real) j pow dimindex(:N) *
                     pde_hs2 s (pde_mx_tder r
                       (pde_mx_tc aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                          (P:num->real->real^N->real^(N,N)finite_prod) j) tau))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < n0 ==> &0 <= pde_hs2 s (pde_mx_tder r
                     (pde_mx_tc aaT bbT (cs:num->(A->bool)#(A->real^N)) psi lam
                        (P:num->real->real^N->real^(N,N)finite_prod) j) tau) /\
                   &0 <= (lam:num->real) j pow dimindex(:N)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_HS2_POS THEN MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN
      EXISTS_TAC `b' - a:real` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                     `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                     `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                     `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                     `aaT:num->real->real^N->real^N^N`;
                     `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                     `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                     `lamT:num->real`;
                     `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                     `j:num`] PDE_MX_DATA_PIECE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXPAND_TAC "SS" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[] THEN EXPAND_TAC "LS" THEN
  MP_TAC(ISPECL [`\j. (lam:num->real) j pow dimindex(:N)`;
                 `sum {j | j < n0} (\j. (lam:num->real) j pow dimindex(:N))`;
                 `{j:num | j < n0}`] SUM_POS_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_REFL; IN_ELIM_THM] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let PDE_MX_R1_TIME = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G t1 r s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\ &0 < t1 /\ t1 < b' - a
     ==> ?C. &0 <= C /\
             !m tau.
               &0 < tau /\ tau <= t1
               ==> sum {i | i < n0}
                     (\i. pde_hs2 s (pde_mx_tder r
                            (pde_mx_g atlas a cs chi lam i
                               (pde_mx_hh atlas a k h cs psi chi lam E n0 G (SUC m))) tau)) <=
                   C * sum {j | j < n0}
                         (\j. sum(0..r) (\r'. pde_hs2 (s + 2) (pde_mx_tder r'
                                (pde_mx_u atlas a cs chi lam E j
                                   (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)) tau)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`; `t1:real`; `s:num`] PDE_MX_R1_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!j. ?Cj. j < n0
             ==> &0 <= Cj /\
                 !u tau. pde_upto (&0) (b' - a) (:real^N) u /\ &0 < tau /\ tau <= t1
                         ==> pde_hs2 s (pde_mx_tder r
                               (\t. pde_mt_comm ((aaT:num->real->real^N->real^N^N) j t)
                                      ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) j t)
                                      (pde_mx_pt (cs:num->(A->bool)#(A->real^N)) psi lam j) (u t)) tau) <=
                             Cj * sum(0..r) (\m. pde_hs2 (s + 2) (pde_mx_tder m u tau))`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN ASM_CASES_TAC `(j:num) < n0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `j:num`] PDE_MX_DATA_PIECE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `j:num`] PDE_MX_PT_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_MX_TCOMM_TDER_BOUND THEN
    MAP_EVERY EXISTS_TAC [`(lamT:num->real) j`;
                          `(ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) j`] THEN
    ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Ct:num->real`)] THEN
  SUBGOAL_THEN `!j. j < n0 ==> &0 <= (Ct:num->real) j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `Ct:num->real`)) (concl th))) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `C0 * sum {j | j < n0} (\j. (Ct:num->real) j)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `tau:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `r:num`; `tau:real`] o check (fun th ->
    can (find_term ((=) `C0:real`)) (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Hm = pde_mx_hh atlas a k h cs psi chi lam
                     (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                     n0 G m:real->A->real^N^N` THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b' (Hm:real->A->real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "Hm" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `G:real->A->real^N^N`] PDE_MX_HH_TFAM) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `SS = sum {j | j < n0}
                     (\j. sum(0..r) (\r'. pde_hs2 (s + 2) (pde_mx_tder r'
                            (pde_mx_u atlas a cs chi lam
                               (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                               j (Hm:real->A->real^N^N)) tau)))` THEN
  REWRITE_TAC[SUM_RMUL] THEN EXPAND_TAC "SS" THEN
  ONCE_REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `pde_upto (&0) (b' - a) (:real^N)
                  (pde_mx_u atlas a cs chi lam
                     (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                     j (Hm:real->A->real^N^N))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `j:num`; `Hm:real->A->real^N^N`] PDE_MX_U_TSOL) THEN
    ASM_SIMP_TAC[pde_tsol];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Ct:num->real) j *
              sum(0..r) (\r'. pde_hs2 (s + 2) (pde_mx_tder r'
                (pde_mx_u atlas a cs chi lam
                   (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                   j (Hm:real->A->real^N^N)) tau))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `Ct:num->real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mt_comm")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`pde_mx_u atlas a cs chi lam
         (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
         j (Hm:real->A->real^N^N)`; `tau:real`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= z ==> y <= z`) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; pde_mx_tc];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\j. (Ct:num->real) j`; `sum {j | j < n0} (\j. (Ct:num->real) j)`;
                   `{j:num | j < n0}`] SUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_REFL; IN_ELIM_THM] THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_HS2_POS THEN MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN
    EXISTS_TAC `b' - a:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let PDE_MX_R1_TIGHT = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G t1 s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\ &0 < t1 /\ t1 < b' - a
     ==> ?C. &0 <= C /\
             !m tau.
               &0 < tau /\ tau <= t1
               ==> sum {i | i < n0}
                     (\i. pde_hs2 s
                            (pde_mx_g atlas a cs chi lam i
                               (pde_mx_hh atlas a k h cs psi chi lam E n0 G (SUC m)) tau)) <=
                   C * sum {j | j < n0}
                         (\j. pde_hs2 (s + 1)
                                (pde_mx_u atlas a cs chi lam E j
                                   (pde_mx_hh atlas a k h cs psi chi lam E n0 G m) tau))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`; `t1:real`; `s:num`] PDE_MX_R1_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!j. ?Cj. j < n0
             ==> &0 <= Cj /\
                 !t u. &0 <= t /\ t <= t1 /\ smooth_map_on (:real^N) u
                       ==> pde_hs2 s (pde_mt_comm ((aaT:num->real->real^N->real^N^N) j t)
                                      ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) j t)
                                      (pde_mx_pt (cs:num->(A->bool)#(A->real^N)) psi lam j) u) <=
                           Cj * pde_hs2 (s + 1) u`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN ASM_CASES_TAC `(j:num) < n0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `j:num`] PDE_MX_DATA_PIECE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `j:num`] PDE_MX_PT_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_ME_COMM_TORUS_BOUND THEN
    MAP_EVERY EXISTS_TAC [`b' - a:real`; `(lamT:num->real) j`;
                          `(ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) j`] THEN
    ASM_REWRITE_TAC[ETA_AX] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Ct:num->real`)] THEN
  SUBGOAL_THEN `!j. j < n0 ==> &0 <= (Ct:num->real) j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `Ct:num->real`)) (concl th))) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `C0 * sum {j | j < n0} (\j. (Ct:num->real) j)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `tau:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `0`; `tau:real`] o check (fun th ->
    can (find_term ((=) `C0:real`)) (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[PDE_MX_TDER_0] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Hm = pde_mx_hh atlas a k h cs psi chi lam
                     (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                     n0 G m:real->A->real^N^N` THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b' (Hm:real->A->real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "Hm" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `G:real->A->real^N^N`] PDE_MX_HH_TFAM) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `SS = sum {j | j < n0}
                     (\j. pde_hs2 (s + 1)
                            (pde_mx_u atlas a cs chi lam
                               (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                               j (Hm:real->A->real^N^N) tau))` THEN
  REWRITE_TAC[SUM_RMUL] THEN EXPAND_TAC "SS" THEN
  ONCE_REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `pde_upto (&0) (b' - a) (:real^N)
                  (pde_mx_u atlas a cs chi lam
                     (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                     j (Hm:real->A->real^N^N))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `j:num`; `Hm:real->A->real^N^N`] PDE_MX_U_TSOL) THEN
    ASM_SIMP_TAC[pde_tsol];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Ct:num->real) j *
              pde_hs2 (s + 1)
                (pde_mx_u atlas a cs chi lam
                   (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                   j (Hm:real->A->real^N^N) tau)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `Ct:num->real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mt_comm")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`tau:real`;
      `pde_mx_u atlas a cs chi lam
         (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
         j (Hm:real->A->real^N^N) tau`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC PDE_ML_UPTO_SLICE_OPEN THEN MAP_EVERY EXISTS_TAC [`&0`; `b' - a:real`] THEN
      ASM_REWRITE_TAC[OPEN_UNIV] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= z ==> y <= z`) THEN
    AP_TERM_TAC THEN REWRITE_TAC[pde_mx_tc];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\j. (Ct:num->real) j`; `sum {j | j < n0} (\j. (Ct:num->real) j)`;
                   `{j:num | j < n0}`] SUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_REFL; IN_ELIM_THM] THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_HS2_POS THEN
    MATCH_MP_TAC PDE_ML_UPTO_SLICE_OPEN THEN MAP_EVERY EXISTS_TAC [`&0`; `b' - a:real`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Analytic core, part 8: base bounds (R0) for time-derivative slices of a   *)
(* periodic family smooth up to 0, and elementary integral facts for the     *)
(* Volterra-Bielecki iteration.                                              *)
(* ========================================================================= *)

let PDE_MX_CINT_CONST = prove
 (`!c. pde_cint (\x:real^N. c) = c`,
  REWRITE_TAC[pde_cint; INTEGRAL_CONST; CONTENT_UNIT; VECTOR_MUL_LID; LIFT_DROP]);;

let PDE_MX_BASE_HS2 = prove
 (`!Tm (g:real->real^N->real^K) T2 r s.
     pde_upto (&0) Tm (:real^N) g /\ (!t. pde_zper (g t)) /\ &0 < T2 /\ T2 < Tm
     ==> ?B. &0 <= B /\
             !tau. &0 < tau /\ tau < T2 ==> pde_hs2 s (pde_mx_tder r g tau) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Tm:real`; `g:real->real^N->real^K`; `T2:real`; `s + r:num`]
                PDE_UPTO_SLAB_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^K` (X_CHOOSE_THEN `A:real`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `&(CARD(pde_index_lists s (:N))) * A pow 2` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2]; ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (pde_mx_tder r (g:real->real^N->real^K) tau)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN EXISTS_TAC `Tm:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[PDE_HS2_CINT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists s (:N)) (\l:num list. A pow 2)` THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[SUM_CONST; PDE_INDEX_LISTS_FINITE; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ LENGTH l <= s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `l IN pde_index_lists s (:N)` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV) [GSYM PDE_MX_CINT_CONST] THEN
  MATCH_MP_TAC PDE_CINT_LE THEN REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  REWRITE_TAC[NORM_POS_LE] THEN
  MP_TAC(ISPECL [`Tm:real`; `g:real->real^N->real^K`; `FG:real^(1,N)finite_sum->real^K`;
                 `r:num`; `l:num list`; `tau:real`; `x:real^N`] PDE_MX_SLICE_TDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE; ALL_APPEND] THEN
  ASM_SIMP_TAC[PDE_MAP_SUC_RANGE; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
  CONJ_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC PDE_FT_ALL_REPLICATE THEN REWRITE_TAC[PDE_HEAT_DIMINDEX_ST] THEN ARITH_TAC]);;

(* ========================================================================= *)
(* Analytic core, part 9: the summed H^s norms pde_mx_ym (torus solutions)   *)
(* and pde_mx_gm (forcings) of the Neumann iterates, and the estimates R0-R3 *)
(* in these terms.                                                           *)
(* ========================================================================= *)

let pde_mx_ym = new_definition
 `pde_mx_ym (atlas:((A->bool)#(A->real^N))->bool) a (k:real->A->real^N^N) (h:A->real^N^N)
            (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real) (chi:num->A->real)
            (lam:num->real)
            (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
            n0 (G:real->A->real^N^N) m r s tau =
    sum {i | i < n0}
      (\i. pde_hs2 s (pde_mx_tder r
             (pde_mx_u atlas a cs chi lam E i (pde_mx_hh atlas a k h cs psi chi lam E n0 G m))
             tau))`;;

let pde_mx_gm = new_definition
 `pde_mx_gm (atlas:((A->bool)#(A->real^N))->bool) a (k:real->A->real^N^N) (h:A->real^N^N)
            (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real) (chi:num->A->real)
            (lam:num->real)
            (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
            n0 (G:real->A->real^N^N) m r s tau =
    sum {i | i < n0}
      (\i. pde_hs2 s (pde_mx_tder r
             (pde_mx_g atlas a cs chi lam i (pde_mx_hh atlas a k h cs psi chi lam E n0 G m))
             tau))`;;

let PDE_MX_ITER_FACTS = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G
     ==> !m i. i < n0
               ==> pde_tsol (b' - a) (aaT i) (bbT i) (ccT i)
                     (pde_mx_g atlas a cs chi lam i (pde_mx_hh atlas a k h cs psi chi lam E n0 G m))
                     (\x. vec 0)
                     (pde_mx_u atlas a cs chi lam E i (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)) /\
                   pde_upto (&0) (b' - a) (:real^N)
                     (pde_mx_g atlas a cs chi lam i (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)) /\
                   (!tau. pde_zper (pde_mx_g atlas a cs chi lam i
                                     (pde_mx_hh atlas a k h cs psi chi lam E n0 G m) tau)) /\
                   pde_upto (&0) (b' - a) (:real^N)
                     (pde_mx_u atlas a cs chi lam E i (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)) /\
                   (!t. &0 <= t /\ t < b' - a
                        ==> pde_zper (pde_mx_u atlas a cs chi lam E i
                                       (pde_mx_hh atlas a k h cs psi chi lam E n0 G m) t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b'
                  (pde_mx_hh atlas a k h cs psi chi lam
                    (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                    n0 G m:real->A->real^N^N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `G:real->A->real^N^N`] PDE_MX_HH_TFAM) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`;
                 `pde_mx_hh atlas a k h cs psi chi lam
                    (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                    n0 G m:real->A->real^N^N`] PDE_MX_U_TSOL) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `i:num`;
                 `pde_mx_hh atlas a k h cs psi chi lam
                    (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                    n0 G m:real->A->real^N^N`] PDE_MX_G_UPTO) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[pde_tsol]);;

let PDE_MX_YM_POS = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G
     ==> !m r s tau. &0 < tau /\ tau < b' - a
                     ==> &0 <= pde_mx_ym atlas a k h cs psi chi lam E n0 G m r s tau /\
                         &0 <= pde_mx_gm atlas a k h cs psi chi lam E n0 G m r s tau`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PDE_MX_ITER_FACTS) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_ym; pde_mx_gm] THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC PDE_HS2_POS THEN MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN
  EXISTS_TAC `b' - a:real` THEN ASM_SIMP_TAC[]);;

let PDE_MX_YM_CONT = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G
     ==> !m s t. t < b' - a
                 ==> (\r. pde_mx_ym atlas a k h cs psi chi lam E n0 G m 0 s r)
                       real_continuous_on real_interval[&0,t] /\
                     (\r. pde_mx_gm atlas a k h cs psi chi lam E n0 G m 0 s r)
                       real_continuous_on real_interval[&0,t]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PDE_MX_ITER_FACTS) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_ym; pde_mx_gm; PDE_MX_TDER_0] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC PDE_UPTO_HS2_CONT THEN EXISTS_TAC `b' - a:real` THEN ASM_SIMP_TAC[ETA_AX]);;

let PDE_MX_R2_YM = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G t1 r s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\ &0 < t1 /\ t1 < b' - a
     ==> ?C. &0 <= C /\
             !m tau. &0 < tau /\ tau <= t1
                     ==> pde_mx_ym atlas a k h cs psi chi lam E n0 G m (SUC r) s tau <=
                         C * (sum(0..r) (\r'. pde_mx_ym atlas a k h cs psi chi lam E n0 G m r'
                                                 (s + 2) tau) +
                              pde_mx_gm atlas a k h cs psi chi lam E n0 G m r s tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`] PDE_MX_ITER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. ?Ci. i < n0
             ==> &0 <= Ci /\
                 !g u tau.
                   pde_upto (&0) (b' - a) (:real^N) g /\
                   pde_tsol (b' - a) ((aaT:num->real->real^N->real^N^N) i)
                     ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) i)
                     ((ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) i)
                     g (\x. vec 0) u /\ &0 < tau /\ tau <= t1
                   ==> pde_hs2 s (pde_mx_tder (SUC r) u tau) <=
                       Ci * (sum(0..r) (\m. pde_hs2 (s + 2) (pde_mx_tder m u tau)) +
                             pde_hs2 s (pde_mx_tder r g tau))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) < n0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `i:num`] PDE_MX_DATA_PIECE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_MX_TIME_TRADE THEN EXISTS_TAC `(lamT:num->real) i` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Cq:num->real`)] THEN
  SUBGOAL_THEN `!i. i < n0 ==> &0 <= (Cq:num->real) i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term ((=) `Cq:num->real`)) (concl th))) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `sum {i | i < n0} (\i. (Cq:num->real) i)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `tau:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `Hm = pde_mx_hh atlas a k h cs psi chi lam
                     (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                     n0 G m:real->A->real^N^N` THEN
  ABBREV_TAC `X = \i. sum(0..r) (\r'. pde_hs2 (s + 2) (pde_mx_tder r'
                        (pde_mx_u atlas a cs chi lam
                           (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                           i (Hm:real->A->real^N^N)) tau)) +
                      pde_hs2 s (pde_mx_tder r (pde_mx_g atlas a cs chi lam i Hm) tau)` THEN
  SUBGOAL_THEN
   `sum(0..r) (\r'. pde_mx_ym (atlas:((A->bool)#(A->real^N))->bool) a k h cs psi chi lam
                      (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                      n0 G m r' (s + 2) tau) +
    pde_mx_gm atlas a k h cs psi chi lam E n0 G m r s tau =
    sum {i | i < n0} (X:num->real)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[pde_mx_ym; pde_mx_gm] THEN EXPAND_TAC "X" THEN
    SIMP_TAC[SUM_ADD; FINITE_NUMSEG_LT] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pde_mx_ym] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!j. j < n0
        ==> pde_upto (&0) (b' - a) (:real^N)
              (pde_mx_u atlas a cs chi lam
                 (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                 j (Hm:real->A->real^N^N)) /\
            pde_upto (&0) (b' - a) (:real^N) (pde_mx_g atlas a cs chi lam j Hm) /\
            pde_tsol (b' - a) ((aaT:num->real->real^N->real^N^N) j)
              ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) j)
              ((ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) j)
              (pde_mx_g atlas a cs chi lam j Hm) (\x. vec 0) (pde_mx_u atlas a cs chi lam E j Hm)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o (fun th -> MP th (ASSUME `(j:num) < n0`)) o
                SPECL [`m:num`; `j:num`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol")) (concl th) &&
      is_forall (concl th) && not (can (find_term ((=) `Cq:num->real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Cq:num->real) i * (X:num->real) i` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "X" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term ((=) `Cq:num->real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < n0 ==> &0 <= (X:num->real) j` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "X" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC PDE_HS2_POS THEN MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN
      EXISTS_TAC `b' - a:real` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC PDE_HS2_POS THEN MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN
      EXISTS_TAC `b' - a:real` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:num->real`; `sum {i | i < n0} (X:num->real)`; `{i:num | i < n0}`]
                SUM_POS_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_REFL; IN_ELIM_THM] THEN ASM_SIMP_TAC[]);;

let PDE_MX_R1_YM = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G t1 r s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\ &0 < t1 /\ t1 < b' - a
     ==> ?C. &0 <= C /\
             !m tau. &0 < tau /\ tau <= t1
                     ==> pde_mx_gm atlas a k h cs psi chi lam E n0 G (SUC m) r s tau <=
                         C * sum(0..r) (\r'. pde_mx_ym atlas a k h cs psi chi lam E n0 G m r'
                                                (s + 2) tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`; `t1:real`; `r:num`; `s:num`] PDE_MX_R1_TIME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[pde_mx_gm; pde_mx_ym] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `tau:real`] o check (fun th ->
    can (find_term ((=) `C:real`)) (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[]);;

let PDE_MX_R1T_YM = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G t1 s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\ &0 < t1 /\ t1 < b' - a
     ==> ?C. &0 <= C /\
             !m tau. &0 < tau /\ tau <= t1
                     ==> pde_mx_gm atlas a k h cs psi chi lam E n0 G (SUC m) 0 s tau <=
                         C * pde_mx_ym atlas a k h cs psi chi lam E n0 G m 0 (s + 1) tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`; `t1:real`; `s:num`] PDE_MX_R1_TIGHT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[pde_mx_gm; pde_mx_ym; PDE_MX_TDER_0]);;

let PDE_MX_R0_GM = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G t1 r s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\ &0 < t1 /\ t1 < b' - a
     ==> ?B. &0 <= B /\
             !tau. &0 < tau /\ tau <= t1
                   ==> pde_mx_gm atlas a k h cs psi chi lam E n0 G 0 r s tau <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`] PDE_MX_ITER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. ?Bi. i < n0
             ==> &0 <= Bi /\
                 !tau. &0 < tau /\ tau < (t1 + (b' - a)) / &2
                       ==> pde_hs2 s (pde_mx_tder r
                             (pde_mx_g atlas a cs chi lam i
                                (pde_mx_hh atlas a k h cs psi chi lam
                                  (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                                  n0 (G:real->A->real^N^N) 0)) tau) <= Bi`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) < n0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_MX_BASE_HS2 THEN EXISTS_TAC `b' - a:real` THEN
    FIRST_ASSUM(MP_TAC o (fun th -> MP th (ASSUME `(i:num) < n0`)) o SPECL [`0`; `i:num`] o
                check (fun th -> is_forall (concl th) &&
                  can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol")) (concl th))) THEN
    SIMP_TAC[] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Bf:num->real`)] THEN
  EXISTS_TAC `sum {i | i < n0} (\i. (Bf:num->real) i)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th ->
      can (find_term ((=) `Bf:num->real`)) (concl th))) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN REWRITE_TAC[pde_mx_gm] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (find_term ((=) `Bf:num->real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC);;

let PDE_MX_R3_YM = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G t1 s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\ &0 < t1 /\ t1 < b' - a
     ==> ?C. &0 <= C /\
             !m t. &0 <= t /\ t <= t1
                   ==> pde_mx_ym atlas a k h cs psi chi lam E n0 G m 0 (s + 1) t <=
                       C * real_integral (real_interval[&0,t])
                             (\r. pde_mx_gm atlas a k h cs psi chi lam E n0 G m 0 s r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`] PDE_MX_ITER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. ?Ci. i < n0
             ==> !f u. pde_upto (&0) (b' - a) (:real^N) f /\ (!t. pde_zper (f t)) /\
                       pde_tsol (b' - a) ((aaT:num->real->real^N->real^N^N) i)
                         ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) i)
                         ((ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) i)
                         f (\y. vec 0) u
                       ==> !t. &0 <= t /\ t <= t1
                               ==> pde_hs2 (s + 1) (u t) <=
                                   Ci * real_integral (real_interval[&0,t]) (\r. pde_hs2 s (f r))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) < n0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `i:num`] PDE_MX_DATA_PIECE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_TORUS_ENERGY THEN EXISTS_TAC `(lamT:num->real) i` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Ce:num->real`)] THEN
  EXISTS_TAC `sum {i | i < n0} (\i. abs((Ce:num->real) i))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `t:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `Hm = pde_mx_hh atlas a k h cs psi chi lam
                     (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                     n0 G m:real->A->real^N^N` THEN
  SUBGOAL_THEN
   `!i. i < n0
        ==> pde_tsol (b' - a) ((aaT:num->real->real^N->real^N^N) i)
              ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) i)
              ((ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) i)
              (pde_mx_g atlas a cs chi lam i (Hm:real->A->real^N^N)) (\x. vec 0)
              (pde_mx_u atlas a cs chi lam
                 (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                 i Hm) /\
            pde_upto (&0) (b' - a) (:real^N) (pde_mx_g atlas a cs chi lam i Hm) /\
            (!tau. pde_zper (pde_mx_g atlas a cs chi lam i Hm tau))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o (fun th -> MP th (ASSUME `(i:num) < n0`)) o
                SPECL [`m:num`; `i:num`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol")) (concl th) &&
      is_forall (concl th) && not (can (find_term ((=) `Ce:num->real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n0
        ==> (\r. pde_hs2 s (pde_mx_g atlas a cs chi lam i (Hm:real->A->real^N^N) r))
              real_integrable_on real_interval[&0,t] /\
            &0 <= real_integral (real_interval[&0,t])
                     (\r. pde_hs2 s (pde_mx_g atlas a cs chi lam i Hm r))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\r. pde_hs2 s (pde_mx_g atlas a cs chi lam i (Hm:real->A->real^N^N) r))
                    real_integrable_on real_interval[&0,t]` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC PDE_UPTO_HS2_CONT THEN
      EXISTS_TAC `b' - a:real` THEN ASM_SIMP_TAC[ETA_AX] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_HS2_POS THEN MATCH_MP_TAC PDE_ML_UPTO_SLICE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b' - a:real`] THEN ASM_SIMP_TAC[OPEN_UNIV] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[pde_mx_ym; pde_mx_gm; PDE_MX_TDER_0] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\i r. pde_hs2 s (pde_mx_g atlas a (cs:num->(A->bool)#(A->real^N)) chi lam i
                                     (Hm:real->A->real^N^N) r)`;
                 `real_interval[&0,t]`; `{i:num | i < n0}`] REAL_INTEGRAL_SUM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Ce:num->real) i * real_integral (real_interval[&0,t])
                (\r. pde_hs2 s (pde_mx_g atlas a cs chi lam i (Hm:real->A->real^N^N) r))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o (fun th -> MP th (ASSUME `(i:num) < n0`)) o SPEC `i:num` o
                check (fun th -> can (find_term ((=) `Ce:num->real`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`pde_mx_g atlas a cs chi lam i (Hm:real->A->real^N^N)`;
      `pde_mx_u atlas a cs chi lam
         (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
         i (Hm:real->A->real^N^N)`]) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o (fun th -> MP th (ASSUME `(i:num) < n0`)) o SPEC `i:num` o
                    check (fun th -> is_forall (concl th) &&
                      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol")) (concl th) &&
                      not (can (find_term ((=) `Ce:num->real`)) (concl th)) &&
                      not (can (find_term ((=) `m:num`)) (concl th)))) THEN
      SIMP_TAC[];
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((Ce:num->real) i)` THEN
  REWRITE_TAC[REAL_ABS_LE] THEN
  MP_TAC(ISPECL [`\i. abs((Ce:num->real) i)`; `sum {i | i < n0} (\i. abs((Ce:num->real) i))`;
                 `{i:num | i < n0}`] SUM_POS_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; REAL_ABS_POS; REAL_LE_REFL; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Analytic core, part 10: geometric decay of the summed H^s norms of the    *)
(* torus solutions of the Neumann iterates.  Time order 0 by the Volterra    *)
(* recursion with the Bielecki weight exp(mu t) (PDE_MX_DECAY0), all time    *)
(* orders by induction with the time trading (PDE_MX_DECAY_ALL).             *)
(* ========================================================================= *)

let PDE_MX_HAS_INTEGRAL_EXP = prove
 (`!mu t. &0 < mu /\ &0 <= t
          ==> ((\r. exp(mu * r)) has_real_integral (exp(mu * t) - &1) / mu)
              (real_interval[&0,t])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. exp(mu * r) / mu`; `\r. exp(mu * r)`; `&0`; `t:real`]
                REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_EXP_0] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:real` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REAL_DIFF_TAC THEN
    MATCH_MP_TAC(REAL_FIELD `~(mu = &0) ==> ((mu * &1) * e) / mu = e`) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_EXP_0] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

let PDE_MX_BIELECKI_ARITH = prove
 (`!C3 C1 A0 q e mu.
     &0 <= C3 /\ &0 <= C1 /\ &0 <= A0 /\ &0 <= q /\ &1 <= e /\ &2 * (C3 * C1) <= mu /\ &0 < mu
     ==> C3 * ((C1 * A0 * q) * ((e - &1) / mu)) <= A0 * (inv(&2) * q) * e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= A0 * q /\ &0 <= (e - &1) / mu` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL]; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(mu / &2) * ((A0 * q) * ((e - &1) / mu))` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `C3 * ((C1 * A0 * q) * ((e - &1) / mu)) =
                  (C3 * C1) * ((A0 * q) * ((e - &1) / mu))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(mu / &2) * ((A0 * q) * ((e - &1) / mu)) = (A0 * q) * (e - &1) / &2`
  SUBST1_TAC THENL [UNDISCH_TAC `&0 < mu` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `A0 * (inv(&2) * q) * e = (A0 * q) * e / &2` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= A0 * q` THEN REAL_ARITH_TAC);;

let PDE_MX_DECAY0 = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G t1 s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\ &0 < t1 /\ t1 < b' - a
     ==> ?A. &0 <= A /\
             !m tau. &0 < tau /\ tau <= t1
                     ==> pde_mx_ym atlas a k h cs psi chi lam E n0 G m 0 s tau <=
                         A * inv(&2) pow m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`; `t1:real`; `s:num`] PDE_MX_R3_YM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C3:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`; `t1:real`; `s:num`] PDE_MX_R1T_YM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`; `t1:real`; `0`; `s:num`] PDE_MX_R0_GM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`] PDE_MX_YM_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`] PDE_MX_ITER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `mu = &2 * (C3 * C1) + &1` THEN
  SUBGOAL_THEN `&0 < mu /\ &2 * (C3 * C1) <= mu` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN SUBGOAL_THEN `&0 <= C3 * C1` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `A0 = C3 * B0 * t1` THEN
  SUBGOAL_THEN `&0 <= A0` ASSUME_TAC THENL
   [EXPAND_TAC "A0" THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m t. &0 < t /\ t <= t1
          ==> pde_mx_ym atlas a k h cs psi chi lam
                (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                n0 (G:real->A->real^N^N) m 0 (s + 1) t <=
              A0 * inv(&2) pow m * exp(mu * t)`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C3 * real_integral (real_interval[&0,t])
                    (\r. pde_mx_gm atlas a k h cs psi chi lam
                           (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                           n0 (G:real->A->real^N^N) 0 0 s r)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `C3:real`)) (concl th) && is_forall (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A0:real` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C3 * (B0 * t)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
          ONCE_REWRITE_TAC[GSYM REAL_INTEGRAL_OPEN_INTERVAL] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `real_integral (real_interval(&0,t)) (\r:real. B0)` THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_INTEGRAL_LE THEN
            REWRITE_TAC[REAL_INTEGRABLE_ON_OPEN_INTERVAL; REAL_INTEGRABLE_CONST] THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
              FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `s:num`; `t:real`] o check (fun th ->
                can (find_term (fun t -> is_const t && fst(dest_const t) = "real_continuous_on"))
                  (concl th))) THEN
              ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
              REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
              FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
                can (find_term ((=) `B0:real`)) (concl th) && is_forall (concl th))) THEN
              ASM_REAL_ARITH_TAC];
            REWRITE_TAC[REAL_INTEGRAL_OPEN_INTERVAL] THEN
            ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
          EXPAND_TAC "A0" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `mu * t:real` REAL_EXP_LE_X) THEN
        SUBGOAL_THEN `&0 <= mu * t` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C3 * real_integral (real_interval[&0,t])
                  (\r. pde_mx_gm atlas a k h cs psi chi lam
                         (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                         n0 (G:real->A->real^N^N) (SUC m) 0 s r)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `C3:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C3 * ((C1 * A0 * inv(&2) pow m) * ((exp(mu * t) - &1) / mu))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`mu:real`; `t:real`] PDE_MX_HAS_INTEGRAL_EXP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `C1 * A0 * inv(&2) pow m` o MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
      DISCH_THEN(fun th -> ASSUME_TAC th THEN
                           ASSUME_TAC(MATCH_MP HAS_REAL_INTEGRAL_INTEGRABLE th) THEN
                           MP_TAC(MATCH_MP REAL_INTEGRAL_UNIQUE th)) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[GSYM REAL_INTEGRAL_OPEN_INTERVAL] THEN
      MATCH_MP_TAC REAL_INTEGRAL_LE THEN
      ASM_REWRITE_TAC[REAL_INTEGRABLE_ON_OPEN_INTERVAL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`SUC m`; `s:num`; `t:real`] o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "real_continuous_on"))
            (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C1 * pde_mx_ym atlas a k h cs psi chi lam
                         (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                         n0 (G:real->A->real^N^N) m 0 (s + 1) r` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `C1:real`)) (concl th) && is_forall (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
        can (find_term ((=) `A0:real`)) (concl th) && is_forall (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_ASSOC]];
      ALL_TAC] THEN
    REWRITE_TAC[real_pow] THEN MATCH_MP_TAC PDE_MX_BIELECKI_ARITH THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_INV_EQ; REAL_POS] THEN
    MP_TAC(SPEC `mu * t:real` REAL_EXP_LE_X) THEN
    SUBGOAL_THEN `&0 <= mu * t` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `A0 * exp(mu * t1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `tau:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_mx_ym atlas a k h cs psi chi lam
                (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                n0 (G:real->A->real^N^N) m 0 (s + 1) tau` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pde_mx_ym] THEN MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC PDE_HS2_MONO THEN CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN EXISTS_TAC `b' - a:real` THEN
    FIRST_X_ASSUM(MP_TAC o (fun th -> MP th (ASSUME `(i:num) < n0`)) o SPECL [`m:num`; `i:num`] o
                  check (fun th -> is_forall (concl th) &&
                    can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol")) (concl th))) THEN
    SIMP_TAC[] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A0 * inv(&2) pow m * exp(mu * tau)` THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * q * e:real = (a * e) * q`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[REAL_POW_LE; REAL_LE_INV_EQ; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let PDE_MX_DECAY_ALL = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G t1.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\ &0 < t1 /\ t1 < b' - a
     ==> !r s. ?A. &0 <= A /\
                   !m tau r'. &0 < tau /\ tau <= t1 /\ r' <= r
                              ==> pde_mx_ym atlas a k h cs psi chi lam E n0 G m r' s tau <=
                                  A * inv(&2) pow m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`] PDE_MX_YM_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [X_GEN_TAC `s:num` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                   `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                   `G:real->A->real^N^N`; `t1:real`; `s:num`] PDE_MX_DECAY0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `A:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `A:real` THEN ASM_REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:num` THEN
  FIRST_ASSUM(X_CHOOSE_THEN `As:real` STRIP_ASSUME_TAC o SPEC `s:num`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `A2:real` STRIP_ASSUME_TAC o SPEC `s + 2`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`; `t1:real`; `r:num`; `s:num`] PDE_MX_R2_YM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`; `t1:real`; `r:num`; `s:num`] PDE_MX_R1_YM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C1t:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`; `t1:real`; `r:num`; `s:num`] PDE_MX_R0_GM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `As + C2 * (&(r + 1) * A2 + B + &2 * C1t * &(r + 1) * A2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `tau:real`; `r':num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= inv(&2) pow m` ASSUME_TAC THENL
   [SIMP_TAC[REAL_POW_LE; REAL_LE_INV_EQ; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C2 * (&(r + 1) * A2 + B + &2 * C1t * &(r + 1) * A2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  ASM_CASES_TAC `r':num <= r` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `As * inv(&2) pow m` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `As:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `r' = SUC r` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. sum(0..r) (\r''. pde_mx_ym atlas a k h cs psi chi lam
                           (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                           n0 (G:real->A->real^N^N) m r'' (s + 2) tau) <=
        &(r + 1) * A2 * inv(&2) pow m`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..r) (\r'':num. A2 * inv(&2) pow m')` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `A2:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; REAL_MUL_ASSOC; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_mx_gm atlas a k h cs psi chi lam
      (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
      n0 (G:real->A->real^N^N) m r s tau <=
    (B + &2 * C1t * &(r + 1) * A2) * inv(&2) pow m`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &2 * C1t * &(r + 1) * A2` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THENL
     [REWRITE_TAC[real_pow; REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B:real` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `B:real`)) (concl th) && is_forall (concl th))) THEN
        ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C1t * sum(0..r) (\r''. pde_mx_ym atlas a k h cs psi chi lam
                         (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                         n0 (G:real->A->real^N^N) n r'' (s + 2) tau)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `C1t:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C1t * (&(r + 1) * A2 * inv(&2) pow n)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[real_pow] THEN
    SUBGOAL_THEN `&0 <= B * (inv(&2) * inv(&2) pow n)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_LE_INV_EQ; REAL_POS];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C2 * (sum(0..r) (\r''. pde_mx_ym atlas a k h cs psi chi lam
                       (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                       n0 (G:real->A->real^N^N) m r'' (s + 2) tau) +
                    pde_mx_gm atlas a k h cs psi chi lam E n0 G m r s tau)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `C2:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C2 * (&(r + 1) * A2 * inv(&2) pow m +
                    (B + &2 * C1t * &(r + 1) * A2) * inv(&2) pow m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= As * inv(&2) pow m` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The analytic core: all space-time derivatives of the torus solutions      *)
(* u i (H m) decay geometrically in m, uniformly on                          *)
(* (0,t1] x R^N for t1 < b' - a: the decay of the summed H^s norms           *)
(* (PDE_MX_DECAY_ALL) and the torus Sobolev inequality for space-time jets   *)
(* (PDE_MX_JET_SOBOLEV).                                                     *)
(* ========================================================================= *)

let PDE_MX_JETS_SUMMABLE = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G
     ==> !i l t1. i < n0 /\ ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l /\
                  t1 < b' - a
                  ==> ?C q. &0 <= q /\ q < &1 /\
                            !m t y. &0 < t /\ t <= t1
                                    ==> norm(iterated_partial l
                                          (\w. pde_mx_u atlas a cs chi lam E i
                                                 (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)
                                                 (drop(fstcart w)) (sndcart w))
                                          (pastecart (lift t) y)) <= C * q pow m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `l:num list`; `t1:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 < t1` THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`&0`; `&0`] THEN REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC] THEN
  MP_TAC(INST_TYPE [`:(N,N)finite_prod`,`:K`] PDE_MX_JET_SOBOLEV) THEN
  DISCH_THEN(X_CHOOSE_THEN `CS:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`; `t1:real`] PDE_MX_DECAY_ALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`pde_ntime l`; `dimindex(:N) + (LENGTH l - pde_ntime l)`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                 `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `G:real->A->real^N^N`] PDE_MX_ITER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `sqrt(CS * A)` THEN EXISTS_TAC `sqrt(inv(&2))` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LT THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `t:real`; `y:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM PDE_SQRT_POW; GSYM SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  SUBGOAL_THEN
   `pde_tsol (b' - a) ((aaT:num->real->real^N->real^N^N) i)
      ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) i)
      ((ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) i)
      (pde_mx_g atlas a cs chi lam i (pde_mx_hh atlas a k h cs psi chi lam
         (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
         n0 (G:real->A->real^N^N) m))
      (\x. vec 0)
      (pde_mx_u atlas a cs chi lam E i (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)) /\
    (!j. j < n0
         ==> smooth_map_on (:real^N)
               (pde_mx_tder (pde_ntime l)
                  (pde_mx_u atlas a cs chi lam E j (pde_mx_hh atlas a k h cs psi chi lam E n0 G m))
                  t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o (fun th -> MP th (ASSUME `(i:num) < n0`)) o
                    SPECL [`m:num`; `i:num`] o check (fun th -> is_forall (concl th) &&
                      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol"))
                        (concl th))) THEN
      SIMP_TAC[];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC PDE_MX_TDER_SMOOTH THEN
      EXISTS_TAC `b' - a:real` THEN
      FIRST_X_ASSUM(MP_TAC o (fun th -> MP th (ASSUME `(j:num) < n0`)) o
                    SPECL [`m:num`; `j:num`] o check (fun th -> is_forall (concl th) &&
                      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol"))
                        (concl th))) THEN
      SIMP_TAC[] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `CS * pde_hs2 (dimindex(:N) + (LENGTH l - pde_ntime l))
                     (pde_mx_tder (pde_ntime l)
                        (pde_mx_u atlas a cs chi lam
                           (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                           i (pde_mx_hh atlas a k h cs psi chi lam E n0 (G:real->A->real^N^N) m)) t)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `CS:real`)) (concl th) && is_forall (concl th))) THEN
    EXISTS_TAC `b' - a:real` THEN
    UNDISCH_TAC `pde_tsol (b' - a) ((aaT:num->real->real^N->real^N^N) i)
      ((bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) i)
      ((ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) i)
      (pde_mx_g atlas a cs chi lam i (pde_mx_hh atlas a k h cs psi chi lam
         (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
         n0 (G:real->A->real^N^N) m))
      (\x. vec 0)
      (pde_mx_u atlas a cs chi lam E i (pde_mx_hh atlas a k h cs psi chi lam E n0 G m))` THEN
    SIMP_TAC[pde_tsol] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(c * a) * q:real = c * (a * q)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_mx_ym atlas a k h cs psi chi lam
                (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                n0 (G:real->A->real^N^N) m (pde_ntime l) (dimindex(:N) + (LENGTH l - pde_ntime l)) t` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pde_mx_ym] THEN
    MP_TAC(ISPECL
     [`\i. pde_hs2 (dimindex(:N) + (LENGTH l - pde_ntime l))
            (pde_mx_tder (pde_ntime l)
               (pde_mx_u atlas a cs chi lam
                  (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                  i (pde_mx_hh atlas a k h cs psi chi lam E n0 (G:real->A->real^N^N) m)) t)`;
      `sum {i | i < n0}
         (\i. pde_hs2 (dimindex(:N) + (LENGTH l - pde_ntime l))
               (pde_mx_tder (pde_ntime l)
                  (pde_mx_u atlas a cs chi lam
                     (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                     i (pde_mx_hh atlas a k h cs psi chi lam E n0 (G:real->A->real^N^N) m)) t))`;
      `{i:num | i < n0}`] SUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_REFL; IN_ELIM_THM] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_HS2_POS THEN ASM_SIMP_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `A:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[LE_REFL]]);;

(* ========================================================================= *)
(* Limits on the tori.  The partial sums of the torus solutions u i (H m)    *)
(* converge with all space-time derivatives (PDM_UPTO_LIMIT) to families     *)
(* GG i smooth up to t = 0.                                                  *)
(* ========================================================================= *)

let PDE_MX_GEOM_CAUCHY = prove
 (`!C q d. &0 <= q /\ q < &1 /\ &0 < d
           ==> ?N0. !(x:num->real^K) m n.
                      (!m. norm(x m) <= C * q pow m) /\ N0 <= m /\ N0 <= n
                      ==> norm(vsum(0..m) x - vsum(0..n) x) < d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real`; `(d * (&1 - q)) / (abs C + &1)`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0:num` THEN
  SUBGOAL_THEN `abs C * q pow N0 < d * (&1 - q)` ASSUME_TAC THENL
   [UNDISCH_TAC `q pow N0 < (d * (&1 - q)) / (abs C + &1)` THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < abs C + &1`] THEN
    MP_TAC(SPECL [`q:real`; `N0:num`] REAL_POW_LE) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(x:num->real^K) m n. (!m. norm(x m) <= C * q pow m) /\ N0 <= n /\ n <= m
                          ==> norm(vsum(0..m) x - vsum(0..n) x) < d`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`x:num->real^K`; `0`; `n:num`; `m:num`] VSUM_COMBINE_R) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^K = b`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum(n + 1..m) (\k. abs C * q pow k)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C * q pow k` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL] THEN
    ASM_CASES_TAC `m < n + 1` THENL
     [ASM_SIMP_TAC[SUM_TRIV_NUMSEG; REAL_MUL_RZERO]; ALL_TAC] THEN
    MP_TAC(ISPECL [`q:real`; `n + 1`; `m:num`] SUM_GP_MULTIPLIED) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&1 - q) * sum(n + 1..m) (\k. q pow k) <= q pow N0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`q:real`; `SUC m`] REAL_POW_LE) THEN
      SUBGOAL_THEN `q pow (n + 1) <= q pow N0` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sum(n + 1..m) (\k. q pow k)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[REAL_POW_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `(abs C * sum(n + 1..m) (\k. q pow k)) * (&1 - q) < d * (&1 - q)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs C * q pow N0` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(c * s) * a = c * (a * s)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(ARITH_RULE `n <= m \/ m <= n:num`) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[NORM_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let PDE_MX_TORUS_LIMITS = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G i.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\ i < n0
     ==> ?GG. pde_upto (&0) (b' - a) (:real^N) (\t y. GG(pastecart (lift t) y)) /\
              (!t y. &0 <= t /\ t < b' - a
                     ==> ((\n. vsum(0..n) (\m. pde_mx_u atlas a cs chi lam E i
                                                (pde_mx_hh atlas a k h cs psi chi lam E n0 G m) t y))
                          --> GG(pastecart (lift t) y)) sequentially) /\
              (!l t y. ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l /\
                       &0 < t /\ t < b' - a
                       ==> ((\n. vsum(0..n) (\m. iterated_partial l
                                   (\w. pde_mx_u atlas a cs chi lam E i
                                          (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)
                                          (drop(fstcart w)) (sndcart w))
                                   (pastecart (lift t) y)))
                            --> iterated_partial l GG (pastecart (lift t) y)) sequentially)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a < b'` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pde_mx_data]); ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. pde_upto (&0) (b' - a) (:real^N)
          (pde_mx_u atlas a cs chi lam
             (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
             i (pde_mx_hh atlas a (k:real->A->real^N^N) h cs psi chi lam E n0 G m))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                      real^(N,N)finite_prod`;
                   `i:num`; `pde_mx_hh atlas a (k:real->A->real^N^N) h cs psi chi lam
                               (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                                  real^(N,N)finite_prod) n0 (G:real->A->real^N^N) m`]
                  PDE_MX_U_TSOL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                     `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                     `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                     `psi:num->A->real`; `chi:num->A->real`; `lam:num->real`;
                     `aaT:num->real->real^N->real^N^N`;
                     `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                     `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                     `lamT:num->real`;
                     `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                        real^(N,N)finite_prod`; `G:real->A->real^N^N`] PDE_MX_HH_TFAM) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      SIMP_TAC[pde_tsol]];
    ALL_TAC] THEN
  ABBREV_TAC `CU = \m (w:real^(1,N)finite_sum).
                 pde_mx_u atlas a cs chi lam
                   (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                      real^(N,N)finite_prod) i
                   (pde_mx_hh atlas a (k:real->A->real^N^N) h cs psi chi lam E n0 G m)
                   (drop(fstcart w)) (sndcart w)` THEN
  SUBGOAL_THEN
   `!m. smooth_map_on (interval(lift(&0),lift(b' - a)) PCROSS (:real^N))
          ((CU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) m)`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fe:real^(1,N)finite_sum->real^(N,N)finite_prod`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `Fe:real^(1,N)finite_sum->real^(N,N)finite_prod` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
      MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      EXPAND_TAC "CU" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`drop s`; `y:real^N`]) THEN REWRITE_TAC[LIFT_DROP] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - e),lift(b' - a)) PCROSS (:real^N)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?ee FF. !n. &0 < ee n /\
                smooth_map_on (interval(lift(&0 - ee n),lift(b' - a)) PCROSS (:real^N))
                  ((FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) n) /\
                !t y. &0 <= t /\ t < b' - a
                      ==> FF n (pastecart (lift t) y) =
                          vsum(0..n) (\m. pde_mx_u atlas a cs chi lam
                            (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                               real^(N,N)finite_prod) i
                            (pde_mx_hh atlas a (k:real->A->real^N^N) h cs psi chi lam E n0 G m) t y)`
  (STRIP_ASSUME_TAC o REWRITE_RULE[FORALL_AND_THM]) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`&0`; `b' - a`; `(:real^N)`;
                   `\m. pde_mx_u atlas a cs chi lam
                          (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                             real^(N,N)finite_prod) i
                          (pde_mx_hh atlas a (k:real->A->real^N^N) h cs psi chi lam E n0 G m)`;
                   `0..n`] PDE_MX_UPTO_VSUM) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG; ETA_AX] THEN
    REWRITE_TAC[pde_upto; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l n t y. &0 < t /\ t < b' - a
              ==> iterated_partial l ((FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) n)
                    (pastecart (lift t) y) =
                  vsum(0..n) (\m. iterated_partial l
                    ((CU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) m)
                    (pastecart (lift t) y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `iterated_partial l (\w. vsum(0..n) (\m. (CU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) m w))
                       (pastecart (lift t) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
      EXISTS_TAC `interval(lift(&0),lift(b' - a)) PCROSS (:real^N)` THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_INTERVAL_1;
               LIFT_DROP; IN_UNIV; FORALL_PASTECART] THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`s:real^1`; `z:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `drop s`; `z:real^N`] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "vsum")) (concl th) &&
        can (find_term ((=) `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial"))
               (concl th)))) THEN
      REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "CU" THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
      MP_TAC(ISPECL [`l:num list`; `interval(lift(&0),lift(b' - a)) PCROSS (:real^N)`;
                     `CU:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `0..n`]
                    PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS;
                   IN_INTERVAL_1; LIFT_DROP; IN_UNIV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&0`; `b' - a`; `(:real^N)`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`]
                PDM_UPTO_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; REAL_SUB_LT] THEN
    MAP_EVERY X_GEN_TAC [`l:num list`; `t1:real`] THEN STRIP_TAC THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                      real^(N,N)finite_prod`; `G:real->A->real^N^N`] PDE_MX_JETS_SUMMABLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `l:num list`; `t1:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`C:real`; `q:real`; `d:real`]
             (INST_TYPE [`:(N,N)finite_prod`,`:K`] PDE_MX_GEOM_CAUCHY)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0:num` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `t < b' - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m':num` THEN EXPAND_TAC "CU" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `GG:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `GG:real^(1,N)finite_sum->real^(N,N)finite_prod` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:real^N`] o check (fun th ->
      can (find_term ((=) `GG:real^(1,N)finite_sum->real^(N,N)finite_prod`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial")) (concl th)))) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `t:real`] o check (fun th ->
    can (find_term ((=) `GG:real^(1,N)finite_sum->real^(N,N)finite_prod`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `t:real`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; IN_UNIV] THEN
  SUBGOAL_THEN
   `iterated_partial l ((FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) n)
      (pastecart (lift t) y) =
    vsum(0..n) (\m. iterated_partial l
      ((CU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) m) (pastecart (lift t) y))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "CU" THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* Limits of torus solutions.  If torus solutions with zero data converge    *)
(* with all space-time derivatives and their forcings converge pointwise,    *)
(* the limit solves the torus equation with the limit forcing                *)
(* (PDE_MX_TSOL_LIMIT).  The family pde_mx_rq of families smooth up to 0 is  *)
(* a time family on M (PDE_MX_RQ_TFAM).                                      *)
(* ========================================================================= *)

let PDE_MX_STOP_LIM = prove
 (`!(a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
    (V:num->real^(1,N)finite_sum->real^K) V0 w.
     (!l. ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l
          ==> ((\n. iterated_partial l (V n) w) --> iterated_partial l V0 w) sequentially)
     ==> ((\n. pde_stop a b c (V n) w) --> pde_stop a b c V0 w) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> ((\n. partial_derivative (1 + i) (partial_derivative (1 + j) (V n)) w) -->
                partial_derivative (1 + i) (partial_derivative (1 + j) V0) w) sequentially) /\
    (!i. 1 <= i /\ i <= dimindex(:N)
         ==> ((\n. partial_derivative (1 + i) (V n) w) --> partial_derivative (1 + i) V0 w)
             sequentially) /\
    ((\n. (V:num->real^(1,N)finite_sum->real^K) n w) --> V0 w) sequentially`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `[1 + i; 1 + j]`);
      FIRST_X_ASSUM(MP_TAC o SPEC `[1 + i]`);
      FIRST_X_ASSUM(MP_TAC o SPEC `[]:num list`)] THEN
    REWRITE_TAC[iterated_partial; ALL; PDE_HEAT_DIMINDEX_ST; ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[pde_stop] THEN
  REPEAT(MATCH_MP_TAC LIM_ADD THEN CONJ_TAC) THENL
   [MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LIM_CMUL THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`sequentially`; `(**) ((b:real^(1,N)finite_sum->num->real^K^K) w i)`;
                   `\n. partial_derivative (1 + i) ((V:num->real^(1,N)finite_sum->real^K) n) w`;
                   `partial_derivative (1 + i) (V0:real^(1,N)finite_sum->real^K) w`] LIM_LINEAR) THEN
    ASM_SIMP_TAC[REWRITE_RULE[ETA_AX] MATRIX_VECTOR_MUL_LINEAR];
    MP_TAC(ISPECL [`sequentially`; `(**) ((c:real^(1,N)finite_sum->real^K^K) w)`;
                   `\n. (V:num->real^(1,N)finite_sum->real^K) n w`;
                   `(V0:real^(1,N)finite_sum->real^K) w`] LIM_LINEAR) THEN
    ASM_SIMP_TAC[REWRITE_RULE[ETA_AX] MATRIX_VECTOR_MUL_LINEAR]]);;

let PDE_MX_TSOL_LIMIT = prove
 (`!Tm (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc
    (P:num->real->real^N->real^K) fn f GG.
     &0 < Tm /\
     (!n. pde_tsol Tm aa bb cc (fn n) (\x. vec 0) (P n)) /\
     pde_upto (&0) Tm (:real^N) (\t y. GG(pastecart (lift t) y)) /\
     (!t y. &0 <= t /\ t < Tm ==> ((\n. P n t y) --> GG(pastecart (lift t) y)) sequentially) /\
     (!l t y. ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l /\ &0 < t /\ t < Tm
              ==> ((\n. iterated_partial l (\w. P n (drop(fstcart w)) (sndcart w))
                          (pastecart (lift t) y)) -->
                   iterated_partial l GG (pastecart (lift t) y)) sequentially) /\
     (!t y. &0 < t /\ t < Tm ==> ((\n. fn n t y) --> f t y) sequentially)
     ==> pde_tsol Tm aa bb cc f (\x. vec 0) (\t y. GG(pastecart (lift t) y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = interval(lift(&0),lift Tm) PCROSS (:real^N)` THEN
  SUBGOAL_THEN `open(S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!t y. pastecart (lift t) y IN (S:real^(1,N)finite_sum->bool) <=> &0 < t /\ t < Tm`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (S:real^(1,N)finite_sum->bool) (GG:real^(1,N)finite_sum->real^K)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pde_upto (&0) Tm (:real^N) (\t y. (GG:real^(1,N)finite_sum->real^K)
                                                   (pastecart (lift t) y))` THEN
    REWRITE_TAC[pde_upto; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fe:real^(1,N)finite_sum->real^K`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `Fe:real^(1,N)finite_sum->real^K` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART] THEN MAP_EVERY X_GEN_TAC [`s:real^1`; `z:real^N`] THEN
      ONCE_REWRITE_TAC[GSYM LIFT_DROP] THEN ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`drop s`; `z:real^N`] o check (fun th ->
        can (find_term ((=) `Fe:real^(1,N)finite_sum->real^K`)) (concl th) && is_forall(concl th))) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - e),lift Tm) PCROSS (:real^N)` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "S" THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pde_tsol] THEN REPEAT CONJ_TAC THENL
   [(* periodicity *)
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[pde_zper] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `kk:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. (P:num->real->real^N->real^K) n t x` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x + basis kk:real^N`] o check (fun th ->
      can (find_term ((=) `GG:real^(1,N)finite_sum->real^K`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial")) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol")) (concl th))) THEN
    REWRITE_TAC[pde_tsol; pde_zper] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    (* initial value *)
    X_GEN_TAC `y:real^N` THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. (P:num->real->real^N->real^K) n (&0) y` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `GG:real^(1,N)finite_sum->real^K`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial")) (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `!n. (P:num->real->real^N->real^K) n (&0) y = vec 0`
        (fun th -> REWRITE_TAC[th; LIM_CONST]) THEN
      GEN_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol")) (concl th))) THEN
      SIMP_TAC[pde_tsol]];
    ALL_TAC] THEN
  (* the equation *)
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (lift t) y IN (S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?FU:real^(1,N)finite_sum->real^K.
        (?e. &0 < e /\ smooth_map_on (interval(lift(&0 - e),lift Tm) PCROSS (:real^N)) FU) /\
        (!t y. &0 <= t /\ t < Tm ==> FU(pastecart (lift t) y) = (P:num->real->real^N->real^K) n t y)`
  MP_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_tsol")) (concl th))) THEN
    REWRITE_TAC[pde_tsol; pde_upto; IN_UNIV] THEN MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `FU:num->real^(1,N)finite_sum->real^K`
      (STRIP_ASSUME_TAC o REWRITE_RULE[FORALL_AND_THM]))] THEN
  SUBGOAL_THEN
   `!n l. iterated_partial l ((FU:num->real^(1,N)finite_sum->real^K) n) (pastecart (lift t) y) =
          iterated_partial l (\w. (P:num->real->real^N->real^K) n (drop(fstcart w)) (sndcart w))
                           (pastecart (lift t) y)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[FORALL_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `z:real^N`] THEN
    ONCE_REWRITE_TAC[GSYM LIFT_DROP] THEN ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `drop s`; `z:real^N`]) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `partial_derivative 1 (GG:real^(1,N)finite_sum->real^K) (pastecart (lift t) y) =
    pde_stop (\z. aa (drop(fstcart z)) (sndcart z)) (\z i. bb (drop(fstcart z)) (sndcart z) i)
             (\z. cc (drop(fstcart z)) (sndcart z)) GG (pastecart (lift t) y) + f t y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. partial_derivative 1 ((FU:num->real^(1,N)finite_sum->real^K) n)
                                         (pastecart (lift t) y)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MP_TAC(GEN `n:num` (SPECL [`n:num`; `[1]`] (ASSUME
        `!n l. iterated_partial l ((FU:num->real^(1,N)finite_sum->real^K) n) (pastecart (lift t) y) =
               iterated_partial l (\w. (P:num->real->real^N->real^K) n (drop(fstcart w)) (sndcart w))
                                (pastecart (lift t) y)`))) THEN
      REWRITE_TAC[iterated_partial] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`[1]`; `t:real`; `y:real^N`] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial")) (concl th) &&
        can (find_term ((=) `GG:real^(1,N)finite_sum->real^K`)) (concl th))) THEN
      ASM_REWRITE_TAC[ALL; iterated_partial; PDE_HEAT_DIMINDEX_ST] THEN
      DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. partial_derivative 1 ((FU:num->real^(1,N)finite_sum->real^K) n) (pastecart (lift t) y) =
          pde_stop (\z. aa (drop(fstcart z)) (sndcart z)) (\z i. bb (drop(fstcart z)) (sndcart z) i)
                   (\z. cc (drop(fstcart z)) (sndcart z)) (FU n) (pastecart (lift t) y) +
          (fn:num->real->real^N->real^K) n t y`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC PDE_TSOL_ST_EQ THEN
      MAP_EVERY EXISTS_TAC [`Tm:real`; `\x:real^N. vec 0:real^K`;
                            `(P:num->real->real^N->real^K) n`] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th) &&
        can (find_term ((=) `FU:num->real^(1,N)finite_sum->real^K`)) (concl th))) THEN
      EXISTS_TAC `e:real` THEN ASM_SIMP_TAC[ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_ADD THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC PDE_MX_STOP_LIM THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial")) (concl th) &&
      can (find_term ((=) `GG:real^(1,N)finite_sum->real^K`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`GG:real^(1,N)finite_sum->real^K`; `t:real`; `y:real^N`] PDE_ST_TIME_DERIV) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDE_LOP_STOP_CANON THEN
  MAP_EVERY EXISTS_TAC [`&0`; `Tm:real`] THEN
  UNDISCH_TAC `smooth_map_on (S:real^(1,N)finite_sum->bool) (GG:real^(1,N)finite_sum->real^K)` THEN
  EXPAND_TAC "S" THEN SIMP_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The limit of the Neumann series solves the equation on [a,b')             *)
(* (PDE_MX_SERIES_SOL).                                                      *)
(* ========================================================================= *)

let PDE_MX_RQ_TFAM = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E
    (Q:num->real->real^N->real^(N,N)finite_prod).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' <= b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     (!j. j < n0 ==> pde_upto (&0) (b' - a) (:real^N) (Q j))
     ==> pde_tfam_from atlas a b' (pde_mx_rq atlas a k h cs psi lam n0 Q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pde_mx_rq atlas a k h cs psi lam n0 (Q:num->real->real^N->real^(N,N)finite_prod) =
                (\t x. (matrify:real^(N,N)finite_prod->real^N^N)
                    (vsum {j | j < n0}
                       (\j. (vectorize:real^N^N->real^(N,N)finite_prod)
                              (pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) j)
                                 ((\j t z. (matrify:real^(N,N)finite_prod->real^N^N)
                                     (pde_mt_comm (pde_mlaa atlas (cs j) (k:real->A->real^N^N) t)
                                        (pde_mlbt atlas (cs j) k h t)
                                        (\z. lift(pde_mx_psic cs psi j z))
                                        (\z. Q j (t - a) (inv((lam:num->real) j) % z + inv(&2) % vec 1))
                                        z))
                                  j t) x))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_mx_rq]; ALL_TAC] THEN
  MATCH_MP_TAC PDE_MX_CHART_SUM_TFAM THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                 `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                 `lamT:num->real`;
                 `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod`;
                 `j:num`] PDE_MX_DATA_PSIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cs:num->(A->bool)#(A->real^N)) j IN atlas /\ compact((ks:num->real^N->bool) j) /\
                ks j SUBSET IMAGE (SND(cs j)) (FST(cs j)) /\ a < b'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_mx_data (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b'
                   (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E` THEN
    REWRITE_TAC[pde_mx_data; pde_cover] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_upto a b' (:real^N)
      (\t z. (Q:num->real->real^N->real^(N,N)finite_prod) j (t - a)
               (inv((lam:num->real) j) % z + inv(&2) % vec 1))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&0`; `b' - a`; `(Q:num->real->real^N->real^(N,N)finite_prod) j`;
                   `inv((lam:num->real) j)`; `inv(&2) % vec 1:real^N`] PDM_UPTO_AFFINE) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`&0`; `b' - a`; `(:real^N)`;
                   `\t x. (Q:num->real->real^N->real^(N,N)finite_prod) j t
                            (inv((lam:num->real) j) % x + inv(&2) % vec 1)`;
                   `--a:real`] PDE_MT_UPTO_SHIFT) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; REAL_ARITH `&0 - --a = a /\ (b' - a) - --a = b'`] THEN
    REWRITE_TAC[GSYM real_sub; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `(cs:num->(A->bool)#(A->real^N)) j`]
                PDE_MT_CHART_COEFF_UPTO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[VECTORIZE_MATRIFY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`a:real`; `b':real`; `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))`;
                   `pde_mlaa atlas ((cs:num->(A->bool)#(A->real^N)) j) (k:real->A->real^N^N)`;
                   `pde_mlbt atlas ((cs:num->(A->bool)#(A->real^N)) j) (k:real->A->real^N^N) h`;
                   `\z. lift(pde_mx_psic (cs:num->(A->bool)#(A->real^N)) psi j z)`;
                   `\t z. (Q:num->real->real^N->real^(N,N)finite_prod) j (t - a)
                            (inv((lam:num->real) j) % z + inv(&2) % vec 1)`] PDE_MT_COMM_UPTO) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC PDE_MT_UPTO_OPEN_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MATRIFY_0] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN EXISTS_TAC `(:real^N) DIFF (ks:num->real^N->bool) j` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV; LIFT_NUM]]);;

(* Pointwise limits of the torus forcings. *)

let PDE_MX_G_LIM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a cs chi lam i (Fn:num->real->A->real^N^N) F0 t y.
     smooth_manifold_atlas top atlas /\ cs i IN atlas /\
     (!x. x IN topspace top
          ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod) (Fn n (t + a) x)) -->
               vectorize(F0 (t + a) x)) sequentially)
     ==> ((\n. pde_mx_g atlas a cs chi lam i (Fn n) t y) -->
          pde_mx_g atlas a cs chi lam i F0 t y) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_g; pdm_transplant; pdm_periodize] THEN
  ABBREV_TAC `z0 = (lam:num->real) i % (pdm_frac (y:real^N) - inv(&2) % vec 1)` THEN
  ASM_CASES_TAC `(z0:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THENL
   [ALL_TAC; ASM_REWRITE_TAC[pde_mx_psic; VECTOR_MUL_LZERO; LIM_CONST]] THEN
  MATCH_MP_TAC LIM_CMUL THEN REWRITE_TAC[metric_local] THEN
  MP_TAC(ISPECL
   [`sequentially`;
    `\v. (vectorize:real^N^N->real^(N,N)finite_prod)
           (transp (matrix (chart_jac ((cs:num->(A->bool)#(A->real^N)) i)
                    (chart_at atlas (chart_inv (cs i) (z0:real^N))) (chart_inv (cs i) z0))) **
            (matrify:real^(N,N)finite_prod->real^N^N) v **
            matrix (chart_jac (cs i) (chart_at atlas (chart_inv (cs i) z0)) (chart_inv (cs i) z0)))`;
    `\n. (vectorize:real^N^N->real^(N,N)finite_prod)
           ((Fn:num->real->A->real^N^N) n (t + a)
              (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) (z0:real^N)))`;
    `(vectorize:real^N^N->real^(N,N)finite_prod)
       ((F0:real->A->real^N^N) (t + a) (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) (z0:real^N)))`]
   LIM_LINEAR) THEN
  REWRITE_TAC[PDE_MX_TRIPLE_LINEAR; MATRIFY_VECTORIZE] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let PDE_MX_RQ_CONG = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) a (k:real->A->real^N^N) h cs psi lam n0
    (P1:num->real->real^N->real^(N,N)finite_prod) P2 t x.
     (!j. j < n0 ==> P1 j (t - a) = P2 j (t - a))
     ==> pde_mx_rq atlas a k h cs psi lam n0 P1 t x = pde_mx_rq atlas a k h cs psi lam n0 P2 t x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mx_rq] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[]);;

(* Each torus limit solves the torus equation with forcing g i F_inf. *)

let PDE_MX_GG_TSOL = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G
    (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G /\
     (!j. j < n0
          ==> pde_upto (&0) (b' - a) (:real^N) (\t y. GG j (pastecart (lift t) y)) /\
              (!t y. &0 <= t /\ t < b' - a
                     ==> ((\n. vsum(0..n) (\m. pde_mx_u atlas a cs chi lam E j
                                  (pde_mx_hh atlas a k h cs psi chi lam E n0 G m) t y))
                          --> GG j (pastecart (lift t) y)) sequentially) /\
              (!l t y. ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l /\
                       &0 < t /\ t < b' - a
                       ==> ((\n. vsum(0..n) (\m. iterated_partial l
                                   (\w. pde_mx_u atlas a cs chi lam E j
                                          (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)
                                          (drop(fstcart w)) (sndcart w))
                                   (pastecart (lift t) y)))
                            --> iterated_partial l (GG j) (pastecart (lift t) y)) sequentially)) /\
     i < n0
     ==> pde_tsol (b' - a) (aaT i) (bbT i) (ccT i)
           (pde_mx_g atlas a cs chi lam i
              (\t x. G t x + pde_mx_rq atlas a k h cs psi lam n0
                               (\j t y. GG j (pastecart (lift t) y)) t x))
           (\x. vec 0) (\t y. GG i (pastecart (lift t) y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pde_mx_data]) THEN
  ABBREV_TAC `HH = pde_mx_hh atlas a (k:real->A->real^N^N) h cs psi chi lam
                     (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                        real^(N,N)finite_prod) n0 (G:real->A->real^N^N)` THEN
  SUBGOAL_THEN `!m. pde_tfam_from atlas a b' ((HH:num->real->A->real^N^N) m)` ASSUME_TAC THENL
   [EXPAND_TAC "HH" THEN MATCH_MP_TAC PDE_MX_HH_TFAM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `b:real`; `ks:num->real^N->bool`;
                          `aaT:num->real->real^N->real^N^N`;
                          `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j m. j < n0
          ==> pde_upto (&0) (b' - a) (:real^N)
                (pde_mx_u atlas a cs chi lam
                   (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                      real^(N,N)finite_prod) j ((HH:num->real->A->real^N^N) m)) /\
              (!y. pde_mx_u atlas a cs chi lam E j (HH m) (&0) y = vec 0)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                      real^(N,N)finite_prod`; `j:num`; `(HH:num->real->A->real^N^N) m`]
                  PDE_MX_U_TSOL) THEN
    ASM_SIMP_TAC[pde_tsol];
    ALL_TAC] THEN
  ABBREV_TAC `CU = \j m (w:real^(1,N)finite_sum).
                 pde_mx_u atlas a cs chi lam
                   (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                      real^(N,N)finite_prod) j ((HH:num->real->A->real^N^N) m)
                   (drop(fstcart w)) (sndcart w)` THEN
  SUBGOAL_THEN
   `!j m. j < n0
          ==> smooth_map_on (interval(lift(&0),lift(b' - a)) PCROSS (:real^N))
                ((CU:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod) j m)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "CU" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_MX_CANON_SMOOTH THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < n0
        ==> smooth_map_on (interval(lift(&0),lift(b' - a)) PCROSS (:real^N))
              ((GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`b' - a`; `\t y. (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) j
                                     (pastecart (lift t) y)`] PDE_MX_CANON_SMOOTH) THEN
    ASM_SIMP_TAC[LIFT_DROP; PASTECART_FST_SND; ETA_AX];
    ALL_TAC] THEN
  (* the main step: PDE_MX_TSOL_LIMIT *)
  MATCH_MP_TAC PDE_MX_TSOL_LIMIT THEN
  EXISTS_TAC `\n tau y. vsum(0..SUC n) (\m. pde_mx_u atlas a cs chi lam
                 (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                    real^(N,N)finite_prod) i ((HH:num->real->A->real^N^N) m) tau y)` THEN
  EXISTS_TAC `\n tau y. vsum(0..SUC n) (\m. pde_mx_g atlas a cs chi lam i
                 ((HH:num->real->A->real^N^N) m) tau y)` THEN
  ASM_SIMP_TAC[REAL_SUB_LT] THEN REPEAT CONJ_TAC THENL
   [(* the partial sums solve *)
    GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                      real^(N,N)finite_prod`; `HH:num->real->A->real^N^N`; `i:num`]
                  PDE_MX_PSUM_TSOL) THEN
    ASM_SIMP_TAC[];
    (* values *)
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`t:real`; `y:real^N`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP SEQ_OFFSET) THEN REWRITE_TAC[GSYM ADD1];
    (* derivatives *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!n. iterated_partial l
            (\w. vsum(0..SUC n) (\m. pde_mx_u atlas a cs chi lam
                   (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                      real^(N,N)finite_prod) i ((HH:num->real->A->real^N^N) m)
                   (drop(fstcart w)) (sndcart w))) (pastecart (lift t) y) =
          vsum(0..SUC n) (\m. iterated_partial l
            ((CU:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod) i m) (pastecart (lift t) y))`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`l:num list`; `interval(lift(&0),lift(b' - a)) PCROSS (:real^N)`;
                     `(CU:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod) i`;
                     `0..SUC n`] PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FINITE_NUMSEG; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (y:real^N)`) THEN
      ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
      EXPAND_TAC "CU" THEN REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`l:num list`; `t:real`; `y:real^N`] o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP SEQ_OFFSET) THEN REWRITE_TAC[GSYM ADD1] THEN
    EXPAND_TAC "CU" THEN REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* the forcings *)
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(GEN `n:num` (ISPECL
   [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `cs:num->(A->bool)#(A->real^N)`;
    `chi:num->A->real`; `lam:num->real`; `i:num`; `HH:num->real->A->real^N^N`; `0..SUC n`;
    `t:real`; `y:real^N`] PDE_MX_G_VSUM)) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC PDE_MX_G_LIM THEN EXISTS_TAC `top:A topology` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_mx_data]) THEN
  SUBGOAL_THEN `!j. j < n0 ==> (cs:num->(A->bool)#(A->real^N)) j IN atlas` ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                   (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. (matrify:real^(N,N)finite_prod->real^N^N)
          (vsum(0..SUC n) (\m. (vectorize:real^N^N->real^(N,N)finite_prod)
                                 ((HH:num->real->A->real^N^N) m (t + a) x))) =
        (G:real->A->real^N^N) (t + a) x +
        pde_mx_rq atlas a (k:real->A->real^N^N) h cs psi lam n0
          (\j tau y. vsum(0..n) (\m. pde_mx_u atlas a cs chi lam
             (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
             j (HH m) tau y)) (t + a) x`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "HH" THEN MATCH_MP_TAC PDE_MX_FSUM_REC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `b':real`; `ks:num->real^N->bool`;
                          `aaT:num->real->real^N->real^N^N`;
                          `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTORIZE_ADD] THEN MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
  MATCH_MP_TAC PDE_MX_RQ_LIM THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[REAL_ARITH `(t + a) - a:real = t`] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC PDE_ML_UPTO_SLICE_OPEN THEN MAP_EVERY EXISTS_TAC [`&0`; `b' - a`] THEN
      ASM_SIMP_TAC[OPEN_UNIV; REAL_LT_IMP_LE];
      MP_TAC(ISPECL [`&0`; `b' - a`; `(:real^N)`;
                     `\t y. (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) j
                             (pastecart (lift t) y)`; `t:real`] PDE_ML_UPTO_SLICE_OPEN) THEN
      ASM_SIMP_TAC[OPEN_UNIV; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `z:real^N`] THEN DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`t:real`; `z:real^N`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\n. partial_derivative p
          (\y. vsum(0..n) (\m. pde_mx_u atlas a cs chi lam
                 (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                    real^(N,N)finite_prod) j ((HH:num->real->A->real^N^N) m) t y)) z) =
    (\n. vsum(0..n) (\m. iterated_partial [1 + p]
           ((CU:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod) j m) (pastecart (lift t) z))) /\
    partial_derivative p (\y. (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) j
                               (pastecart (lift t) y)) z =
    iterated_partial [1 + p] (GG j) (pastecart (lift t) z)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`[p:num]`; `(:real^N)`;
                     `\m y. pde_mx_u atlas a cs chi lam
                              (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                                 real^(N,N)finite_prod) j ((HH:num->real->A->real^N^N) m) t y`;
                     `0..n`] PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
      REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG; IN_UNIV; iterated_partial] THEN
      ANTS_TAC THENL
       [X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC PDE_ML_UPTO_SLICE_OPEN THEN MAP_EVERY EXISTS_TAC [`&0`; `b' - a`] THEN
        ASM_SIMP_TAC[OPEN_UNIV; REAL_LT_IMP_LE];
        DISCH_THEN(fun th -> REWRITE_TAC[th; ETA_AX])] THEN
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(CU:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod) j m`;
                     `&0`; `b' - a`; `[p:num]`; `t:real`; `z:real^N`] PDE_SLAB_SLICE_ITERATED) THEN
      ASM_SIMP_TAC[ALL; MAP; iterated_partial] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "CU" THEN
      REWRITE_TAC[FUN_EQ_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      MP_TAC(ISPECL [`(GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) j`;
                     `&0`; `b' - a`; `[p:num]`; `t:real`; `z:real^N`] PDE_SLAB_SLICE_ITERATED) THEN
      ASM_SIMP_TAC[ALL; MAP; iterated_partial]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`[1 + p]`; `t:real`; `z:real^N`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[ALL; PDE_HEAT_DIMINDEX_ST] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "CU" THEN REWRITE_TAC[]);;

(* Existence on [a,b') with zero initial data. *)

let PDE_MX_SERIES_SOL = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h n0 cs ks psi chi lam aaT bbT ccT lamT E G.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ b' < b /\
     pde_mx_data (top,atlas) a b' k h n0 cs ks psi chi lam aaT bbT ccT lamT E /\
     pde_tfam_from atlas a b' G
     ==> ?v. pde_mlin_sol (top,atlas) a b' k h G (\x. mat 0) v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pde_mx_data]) THEN
  SUBGOAL_THEN
   `?GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod.
      !j. j < n0
          ==> pde_upto (&0) (b' - a) (:real^N) (\t y. GG j (pastecart (lift t) y)) /\
              (!t y. &0 <= t /\ t < b' - a
                     ==> ((\n. vsum(0..n) (\m. pde_mx_u atlas a cs chi lam
                                  (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                                     real^(N,N)finite_prod) j
                                  (pde_mx_hh atlas a (k:real->A->real^N^N) h cs psi chi lam E n0
                                     (G:real->A->real^N^N) m) t y))
                          --> GG j (pastecart (lift t) y)) sequentially) /\
              (!l t y. ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l /\
                       &0 < t /\ t < b' - a
                       ==> ((\n. vsum(0..n) (\m. iterated_partial l
                                   (\w. pde_mx_u atlas a cs chi lam E j
                                          (pde_mx_hh atlas a k h cs psi chi lam E n0 G m)
                                          (drop(fstcart w)) (sndcart w))
                                   (pastecart (lift t) y)))
                            --> iterated_partial l (GG j) (pastecart (lift t) y)) sequentially)`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j:num < n0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_MX_TORUS_LIMITS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `b:real`; `ks:num->real^N->bool`;
                          `aaT:num->real->real^N->real^N^N`;
                          `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Finf = \t x. (G:real->A->real^N^N) t x +
                     pde_mx_rq atlas a (k:real->A->real^N^N) h cs psi lam n0
                       (\j t y. (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) j
                                  (pastecart (lift t) y)) t x` THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b' (Finf:real->A->real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "Finf" THEN MATCH_MP_TAC PDE_MX_TFAM_ADD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC PDE_MX_RQ_TFAM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `b:real`; `ks:num->real^N->bool`; `chi:num->A->real`;
                          `aaT:num->real->real^N->real^N^N`;
                          `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`;
                          `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                             real^(N,N)finite_prod`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i t y. i < n0 /\ &0 <= t /\ t < b' - a
            ==> pde_mx_u atlas a cs chi lam
                  (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                     real^(N,N)finite_prod) i (Finf:real->A->real^N^N) t y =
                (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i (pastecart (lift t) y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                      real^(N,N)finite_prod`; `G:real->A->real^N^N`;
                   `GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `i:num`]
                  PDE_MX_GG_TSOL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[pde_mx_u] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_mx_data]) THEN
    MP_TAC(ISPECL [`b' - a`; `(lamT:num->real) i`; `(aaT:num->real->real^N->real^N^N) i`;
                   `(bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) i`;
                   `(ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod) i`;
                   `pde_mx_g atlas a cs chi lam i (Finf:real->A->real^N^N)`;
                   `\t y. (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                            (pastecart (lift t) y)`] PDE_MT_TSOL_OP_UNIQUE) THEN
    ASM_SIMP_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(MP_TAC o SPEC
      `(E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod) i`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b':real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `chi:num->A->real`; `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                   `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                   `lamT:num->real`;
                   `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                      real^(N,N)finite_prod`; `i:num`; `Finf:real->A->real^N^N`] PDE_MX_G_UPTO) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `pde_mx_s atlas a cs psi chi lam
                (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod)
                n0 (Finf:real->A->real^N^N)` THEN
  MATCH_MP_TAC PDE_MX_MLIN_SOL_CONG THEN
  EXISTS_TAC `\t x. (Finf:real->A->real^N^N) t x -
                    pde_mx_r atlas a (k:real->A->real^N^N) h cs psi chi lam
                      (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                         real^(N,N)finite_prod) n0 Finf t x` THEN
  EXISTS_TAC `\x:A. mat 0:real^N^N` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_MX_PARAMETRIX THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `ks:num->real^N->bool`;
                          `aaT:num->real->real^N->real^N^N`;
                          `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pde_mx_r atlas a (k:real->A->real^N^N) h cs psi chi lam
      (E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->real^(N,N)finite_prod) n0
      (Finf:real->A->real^N^N) t x =
    pde_mx_rq atlas a k h cs psi lam n0
      (\j t y. (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) j (pastecart (lift t) y)) t x`
  SUBST1_TAC THENL
   [REWRITE_TAC[PDE_MX_R_RQ] THEN MATCH_MP_TAC PDE_MX_RQ_CONG THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "Finf" THEN REWRITE_TAC[] THEN MATRIX_ARITH_TAC);;

(* ========================================================================= *)
(* From [a,b') to [a,b) by uniqueness (patching, PDE_MX_PATCH), initial      *)
(* data, and the theorem PDE_MLIN_FROM_TORUS.                                *)
(* ========================================================================= *)

let PDE_MX_TFAM_SUBINTERVAL = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) a b b' (v:real->A->real^N^N).
     pde_tfam_from atlas a b v /\ b' <= b ==> pde_tfam_from atlas a b' v`,
  REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `b:real` THEN ASM_SIMP_TAC[]);;

let PDE_MX_MLIN_SOL_SUBINTERVAL = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h f v0 v.
     pde_mlin_sol (top,atlas) a b k h f v0 v /\ b' <= b
     ==> pde_mlin_sol (top,atlas) a b' k h f v0 v`,
  REWRITE_TAC[pde_mlin_sol] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC PDE_MX_TFAM_SUBINTERVAL THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let PDE_MX_TRHESS_CONG = prove
 (`!top atlas (K:A->real^N^N) h (v:A->real^N^N) w x.
     smooth_manifold_atlas top atlas /\ x IN topspace top /\
     (!y. y IN topspace top ==> v y = w y)
     ==> pde_trhess atlas K h v x = pde_trhess atlas K h w x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_trhess] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PDE_ML_LTRHESS_LOCAL THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[metric_local] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM SET_TAC[]);;

(* Patching solutions on [a,b') for b' -> b. *)

let PDE_MX_PATCH = prove
 (`!top atlas a b (k:real->A->real^N^N) h G.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas h /\ (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ a < b /\
     (!b'. a < b' /\ b' < b ==> ?v. pde_mlin_sol (top,atlas) a b' k h G (\x. mat 0) v)
     ==> ?v. pde_mlin_sol (top,atlas) a b k h G (\x. mat 0) v`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `bb = \n. b - (b - a) / &(n + 2)` THEN
  SUBGOAL_THEN `!n. a < (bb:num->real) n /\ bb n < b` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "bb" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (b - a) / &(n + 2) /\ (b - a) / &(n + 2) < b - a` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_OF_NUM_LT; ARITH_RULE `0 < n + 2`] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH_RULE `0 < n + 2`] THEN
      MATCH_MP_TAC(REAL_ARITH `x * &1 < x * y ==> x < x * y`) THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN
      ASM_REWRITE_TAC[REAL_SUB_LT; REAL_OF_NUM_LT] THEN ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (bb:num->real) m <= bb n` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "bb" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= x ==> b - x <= b - y`) THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_SUB_LE; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t < b ==> ?n. t < (bb:num->real) n` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "bb" THEN REWRITE_TAC[] THEN
    MP_TAC(SPEC `(b - a) / (b - t)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
    MATCH_MP_TAC(REAL_ARITH `x < b - t ==> t < b - x`) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH_RULE `0 < n + 2`] THEN
    UNDISCH_TAC `(b - a) / (b - t) <= &n` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&0 < b - t` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?vv:num->real->A->real^N^N.
                  !n. pde_mlin_sol (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a
                        ((bb:num->real) n) (k:real->A->real^N^N) h (G:real->A->real^N^N)
                        (\x. mat 0) (vv n)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n t x. m <= n /\ a <= t /\ t < (bb:num->real) m /\ x IN topspace top
              ==> (vv:num->real->A->real^N^N) m t x = vv n t x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `(bb:num->real) m`; `k:real->A->real^N^N`; `h:A->real^N^N`;
                   `G:real->A->real^N^N`; `\x:A. mat 0:real^N^N`;
                   `(vv:num->real->A->real^N^N) m`; `(vv:num->real->A->real^N^N) n`]
                  PDE_MLIN_UNIQUE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[REAL_LT_TRANS];
        MATCH_MP_TAC PDE_MX_TFAM_SUBINTERVAL THEN EXISTS_TAC `b:real` THEN
        ASM_MESON_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC PDE_MX_MLIN_SOL_SUBINTERVAL THEN EXISTS_TAC `(bb:num->real) n` THEN
        ASM_SIMP_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `NN = \t. (minimal) (\n. t < (bb:num->real) n)` THEN
  SUBGOAL_THEN
   `!t. t < b ==> t < (bb:num->real) (NN t) /\ !m. m < NN t ==> ~(t < bb m)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXPAND_TAC "NN" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `\n. t < (bb:num->real) n` MINIMAL) THEN REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n t x. a <= t /\ t < (bb:num->real) n /\ x IN topspace top
            ==> (vv:num->real->A->real^N^N) (NN t) t x = vv n t x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `t < b` ASSUME_TAC THENL
     [MP_TAC(ASSUME `!n. a < (bb:num->real) n /\ bb n < b`) THEN
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      can (find_term ((=) `NN:real->num`)) (concl th) && is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `vv:num->real->A->real^N^N`)) (concl th) && is_forall (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mlin_sol")) (concl th)))) THEN
    ASM_REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\t x. (vv:num->real->A->real^N^N) (NN t) t x` THEN
  REWRITE_TAC[pde_mlin_sol] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    (* initial value *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `a:real`; `x:A`]) THEN
    ASM_SIMP_TAC[REAL_LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mlin_sol")) (concl th))) THEN
    REWRITE_TAC[pde_mlin_sol] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    (* the equation *)
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    ABBREV_TAC `m = (NN:real->num) t` THEN
    SUBGOAL_THEN `t < (bb:num->real) m` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\s. (vv:num->real->A->real^N^N) m s x$i$j` THEN
    EXISTS_TAC `min (t - a) ((bb:num->real) m - t)` THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mlin_sol")) (concl th))) THEN
    REWRITE_TAC[pde_mlin_sol] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]] THEN
  (* the time family *)
  REWRITE_TAC[pde_tfam_from] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?ee FF. !n. &0 < ee n /\
                smooth_map_on (interval(lift(a - ee n),lift((bb:num->real) n)) PCROSS
                               IMAGE (SND c) (FST (c:(A->bool)#(A->real^N))))
                  ((FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) n) /\
                !t y. a <= t /\ t < bb n /\ y IN IMAGE (SND c) (FST c)
                      ==> FF n (pastecart (lift t) y) =
                          (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas c ((vv:num->real->A->real^N^N) n t) y)`
  (STRIP_ASSUME_TAC o REWRITE_RULE[FORALL_AND_THM]) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mlin_sol")) (concl th))) THEN
    REWRITE_TAC[pde_mlin_sol; pde_tfam_from] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n t y. a <= t /\ t < (bb:num->real) n /\ y IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
            ==> metric_local atlas c ((vv:num->real->A->real^N^N) (NN t) t) y =
                metric_local atlas c (vv n t) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[metric_local] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(ee:num->real) 0` THEN
  EXISTS_TAC `\w. if drop(fstcart w) < (bb:num->real) 0
                  then (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) 0 w
                  else FF ((NN:real->num) (drop(fstcart w))) w` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP; ETA_AX] THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `t < (bb:num->real) ((NN:real->num) t)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[ETA_AX]]] THEN
  (* smoothness, locally *)
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`s0:real^1`; `y0:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `drop s0 < (bb:num->real) 0` THENL
   [EXISTS_TAC `interval(lift(a - (ee:num->real) 0),lift((bb:num->real) 0)) PCROSS
                IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) 0` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop s0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = (NN:real->num) (drop s0)` THEN
  SUBGOAL_THEN `drop s0 < (bb:num->real) m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `interval(lift a,lift((bb:num->real) m)) PCROSS
              IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      can (find_term (fun t -> t = `a:real`)) (concl th) && is_forall(concl th) &&
      can (find_term (fun t -> t = `b:real`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_mlin_sol")) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) m` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - (ee:num->real) m),lift((bb:num->real) m)) PCROSS
                IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
      can (find_term ((=) `ee:num->real`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th)))) THEN
    ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
              FSTCART_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `z:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pastecart s z = pastecart (lift(drop s)) (z:real^N)` SUBST1_TAC THENL
   [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `drop s < b` ASSUME_TAC THENL
   [MP_TAC(ASSUME `!n. a < (bb:num->real) n /\ bb n < b`) THEN
    DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. a <= drop s /\ drop s < (bb:num->real) n
        ==> (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) n (pastecart (lift(drop s)) z) =
            (vectorize:real^N^N->real^(N,N)finite_prod)
              (metric_local atlas (c:(A->bool)#(A->real^N)) ((vv:num->real->A->real^N^N) m (drop s)) z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
     `(vectorize:real^N^N->real^(N,N)finite_prod)
        (metric_local atlas (c:(A->bool)#(A->real^N)) ((vv:num->real->A->real^N^N) n (drop s)) z)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`)) (concl th) &&
        is_forall (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      AP_TERM_TAC THEN TRANS_TAC EQ_TRANS
       `metric_local atlas (c:(A->bool)#(A->real^N))
          ((vv:num->real->A->real^N^N) (NN(drop s)) (drop s)) z` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `NN:real->num`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_local")) (concl th))) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `NN:real->num`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_local")) (concl th))) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `a <= drop s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `drop s < (bb:num->real) ((NN:real->num) (drop s))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* Initial data: constant families and tr_k Hess_h v0. *)

let PDE_MX_TFAM_CONST = prove
 (`!top atlas a b (v0:A->real^N^N).
     smooth_manifold_atlas top atlas /\ mfd_tensor2_smooth atlas v0
     ==> pde_tfam_from atlas a b (\t:real. v0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PDE_MT_UPTO_TIME_CONST THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C];
    RULE_ASSUM_TAC(REWRITE_RULE[mfd_tensor2_smooth]) THEN
    ASM_SIMP_TAC[GSYM o_DEF; ETA_AX]]);;

let PDE_MX_MLIN_SOL_CONST = prove
 (`!top atlas a b (k:real->A->real^N^N) h (v0:A->real^N^N).
     smooth_manifold_atlas top atlas /\ mfd_tensor2_smooth atlas v0
     ==> pde_mlin_sol (top,atlas) a b k h (\t x. --(pde_trhess atlas (k t) h v0 x)) v0
                      (\t:real. v0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mlin_sol] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_MX_TFAM_CONST THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_ADD_RNEG; MAT_0_COMPONENT] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST]]);;

let PDE_MX_LOP_UPTO = prove
 (`!a b (U:real^N->bool) (A:real->real^N->real^N^N) (B:real->real^N->num->real^K^K) C
    (W:real->real^N->real^K).
     open U /\
     pde_upto a b U (\t z. (vectorize:real^N^N->real^(N,N)finite_prod) (A t z)) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> pde_upto a b U (\t z. (vectorize:real^K^K->real^(K,K)finite_prod) (B t z i))) /\
     pde_upto a b U (\t z. (vectorize:real^K^K->real^(K,K)finite_prod) (C t z)) /\
     pde_upto a b U W
     ==> pde_upto a b U (\t z. pde_lop A B C W t z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lop] THEN
  SUBGOAL_THEN `!i j. pde_upto a b U (\t z. lift((A:real->real^N->real^N^N) t z$i$j))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                   `\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)`;
                   `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                            ((A:real->real^N->real^N^N) t z)`] PDE_MT_UPTO_LINEAR) THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> pde_upto a b U (\t z. partial_derivative i ((W:real->real^N->real^K) t) z) /\
            !j. 1 <= j /\ j <= dimindex(:N)
                ==> pde_upto a b U
                      (\t z. partial_derivative i (partial_derivative j (W t)) z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC PDE_MT_UPTO_PARTIAL_OPEN THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                     `\t z. partial_derivative j ((W:real->real^N->real^K) t) z`; `i:num`]
                    PDE_MT_UPTO_PARTIAL_OPEN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_MT_UPTO_PARTIAL_OPEN THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[ETA_AX] THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC PDE_MT_UPTO_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC) THENL
   [MATCH_MP_TAC PDE_MT_UPTO_VSUM_OPEN THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_MT_UPTO_VSUM_OPEN THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_MT_UPTO_SCALAR_MUL_OPEN THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC PDE_MT_UPTO_VSUM_OPEN THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                   `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `\t z. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((B:real->real^N->num->real^K^K) t z i)`;
                   `\t z. partial_derivative i ((W:real->real^N->real^K) t) z`]
                  PDE_MT_UPTO_BILINEAR_OPEN) THEN
    ASM_SIMP_TAC[MATRIFY_VECTORIZE; INST_TYPE [`:K`,`:N`] LRG_BILINEAR_MATRIFY_MUL; ETA_AX];
    MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                   `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `\t z. (vectorize:real^K^K->real^(K,K)finite_prod) ((C:real->real^N->real^K^K) t z)`;
                   `W:real->real^N->real^K`] PDE_MT_UPTO_BILINEAR_OPEN) THEN
    ASM_SIMP_TAC[MATRIFY_VECTORIZE; INST_TYPE [`:K`,`:N`] LRG_BILINEAR_MATRIFY_MUL; ETA_AX]]);;

let PDE_MX_TRHESS_TFAM = prove
 (`!top atlas a b (k:real->A->real^N^N) h (v0:A->real^N^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ a < b /\ mfd_tensor2_smooth atlas v0
     ==> pde_tfam_from atlas a b (\t x. pde_trhess atlas (k t) h v0 x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDM_TFAM_FROM_UPTO; ETA_AX] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  MATCH_MP_TAC PDM_UPTO_CONG THEN
  EXISTS_TAC `\t z. pde_lop (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N))
                            (pde_mlbt atlas c k h) (pde_mlct atlas c k h)
                            (\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                     (metric_local atlas c (v0:A->real^N^N) z)) t z` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                  PDE_MT_CHART_COEFF_UPTO) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_MX_LOP_UPTO THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC PDE_MT_UPTO_TIME_CONST THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mfd_tensor2_smooth]) THEN
    ASM_SIMP_TAC[GSYM o_DEF; ETA_AX];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[PDE_LOP_LOP0] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `(k:real->A->real^N^N) t`; `h:A->real^N^N`;
                 `v0:A->real^N^N`; `z:real^N`] PDE_ML_TRHESS_CHART) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (v0:A->real^N^N)`; `z:real^N`]
                PDE_ML_LOP0_FORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[mfd_tensor2_smooth]) THEN ASM_SIMP_TAC[];
      ASM_MESON_TAC[riemannian_metric]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PDE_ML_COEFF_FUN; o_DEF]]);;

(* Existence on M: the statement M3 of pc_pde_iface. *)

let PDE_MLIN_HOLDS = prove
 (`!(u:A->bool) (n:N->bool). PDE_MLIN_STATEMENT u n`,
  REWRITE_TAC[PDE_MLIN_STATEMENT] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `GF = \t x. (f:real->A->real^N^N) t x + pde_trhess atlas ((k:real->A->real^N^N) t) h v0 x` THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b (GF:real->A->real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "GF" THEN MATCH_MP_TAC PDE_MX_TFAM_ADD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_MX_TRHESS_TFAM THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w. pde_mlin_sol (top,atlas) a b (k:real->A->real^N^N) h GF (\x. mat 0) w`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_MX_PATCH THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `b':real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `b':real`; `k:real->A->real^N^N`; `h:A->real^N^N`] PDE_MX_DATA_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `cs:num->(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `ks:num->real^N->bool` (X_CHOOSE_THEN `psi:num->A->real`
      (X_CHOOSE_THEN `chi:num->A->real` (X_CHOOSE_THEN `lam:num->real`
      (X_CHOOSE_THEN `aaT:num->real->real^N->real^N^N`
      (X_CHOOSE_THEN `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`
      (X_CHOOSE_THEN `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`
      (X_CHOOSE_THEN `lamT:num->real`
      (X_CHOOSE_TAC `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                       real^(N,N)finite_prod`))))))))))) THEN
    MATCH_MP_TAC PDE_MX_SERIES_SOL THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `n0:num`; `cs:num->(A->bool)#(A->real^N)`;
                          `ks:num->real^N->bool`; `psi:num->A->real`; `chi:num->A->real`;
                          `lam:num->real`; `aaT:num->real->real^N->real^N^N`;
                          `bbT:num->real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `ccT:num->real->real^N->real^(N,N)finite_prod^(N,N)finite_prod`;
                          `lamT:num->real`;
                          `E:num->(real->real^N->real^(N,N)finite_prod)->real->real^N->
                             real^(N,N)finite_prod`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_MX_TFAM_SUBINTERVAL THEN
    EXISTS_TAC `b:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `\t x. (v0:A->real^N^N) x + (w:real->A->real^N^N) t x` THEN
  MATCH_MP_TAC PDE_MX_MLIN_SOL_CONG THEN
  EXISTS_TAC `\t x. --(pde_trhess atlas ((k:real->A->real^N^N) t) h (v0:A->real^N^N) x) +
                    (GF:real->A->real^N^N) t x` THEN
  EXISTS_TAC `\x. (v0:A->real^N^N) x + mat 0` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`;
                   `\t x. --(pde_trhess atlas ((k:real->A->real^N^N) t) h (v0:A->real^N^N) x)`;
                   `GF:real->A->real^N^N`; `v0:A->real^N^N`; `\x:A. mat 0:real^N^N`;
                   `\t:real. (v0:A->real^N^N)`; `w:real->A->real^N^N`] PDE_MX_MLIN_SOL_ADD) THEN
    ASM_SIMP_TAC[PDE_MX_MLIN_SOL_CONST; ETA_AX];
    EXPAND_TAC "GF" THEN REWRITE_TAC[MATRIX_ADD_RID] THEN REPEAT STRIP_TAC THEN
    MATRIX_ARITH_TAC]);;

let PDE_MLIN_FROM_TORUS = prove
 (`!(u:A->bool) (n:N->bool).
        PDE_TORUS_LIN_STATEMENT n (:(N,N)finite_prod) ==> PDE_MLIN_STATEMENT u n`,
  REWRITE_TAC[PDE_MLIN_HOLDS]);;

