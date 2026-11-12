(* ========================================================================= *)
(* Unit pc_pde_mtor (the linear theory on M, second part): from charts of    *)
(* M to tori.  Time shifts, the chart coefficients of tr_k Hess_h up to the  *)
(* initial time on relatively compact chart pieces, their transplants to     *)
(* torus coefficients (pde_tcoeff), transplants of cut-off chart solutions   *)
(* and the torus solution operators.                                         *)
(* ========================================================================= *)

needs "src/pc_pde_mlop.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Time shifts of pde_upto.                                                  *)
(* ========================================================================= *)

let PDE_MT_SHIFT_SMOOTH = prove
 (`!a b (U:real^N->bool) (FG:real^(1,N)finite_sum->real^K) d.
     open U /\ smooth_map_on (interval(lift a,lift b) PCROSS U) FG
     ==> smooth_map_on (interval(lift(a - d),lift(b - d)) PCROSS U)
                       (\z. FG(pastecart (lift(drop(fstcart z) + d)) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. (FG:real^(1,N)finite_sum->real^K) (pastecart (lift(drop(fstcart z) + d)) (sndcart z))) =
    FG o (\z. z + pastecart (lift d) (vec 0:real^N))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_RID; LIFT_ADD; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PDE_IN_SLAB] THEN
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN
    REWRITE_TAC[FSTCART_ADD; SNDCART_ADD; FSTCART_PASTECART; SNDCART_PASTECART;
                DROP_ADD; LIFT_DROP; VECTOR_ADD_RID] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST; ETA_AX]]);;

let PDE_MT_UPTO_SHIFT = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K) d.
     open U /\ pde_upto a b U u
     ==> pde_upto (a - d) (b - d) U (\s. u (s + d))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`e:real`;
    `\z. (FG:real^(1,N)finite_sum->real^K) (pastecart (lift(drop(fstcart z) + d)) (sndcart z))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`a - e:real`; `b:real`; `U:real^N->bool`;
                   `FG:real^(1,N)finite_sum->real^K`; `d:real`] PDE_MT_SHIFT_SMOOTH) THEN
    ASM_REWRITE_TAC[REAL_ARITH `(a - e) - d = (a - d) - e`];
    REPEAT STRIP_TAC THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* pde_upto from a smooth extension on an open neighbourhood of the          *)
(* half-closed slab (PDE_SEELEY), the entries of the coefficient matrices,   *)
(* and the chart coefficients of tr_k Hess_h smooth up to the initial time   *)
(* on the whole chart image (PDE_MT_CHART_COEFF_UPTO).                       *)
(* ========================================================================= *)

let PDE_MT_UPTO_FROM_OPEN = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K) O G.
     open U /\ a < b /\ open O /\
     {pastecart (lift t) y | a <= t /\ t < b /\ y IN U} SUBSET O /\
     smooth_map_on O G /\
     (!t y. a <= t /\ t < b /\ y IN U ==> G(pastecart (lift t) y) = u t y)
     ==> pde_upto a b U u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_SEELEY THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!w. w IN {pastecart (lift t) y | a <= t /\ t < b /\ y IN U}
        ==> (u:real->real^N->real^K) (drop(fstcart w)) (sndcart w) = G w`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `G:real^(1,N)finite_sum->real^K` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval(lift a,lift b) PCROSS (U:real^N->bool) SUBSET O` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{pastecart (lift t) y | a <= t /\ t < b /\ (y:real^N) IN U}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; PDE_IN_SLAB; IN_ELIM_THM] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`drop(fstcart(w:real^(1,N)finite_sum))`;
                                         `sndcart(w:real^(1,N)finite_sum)`] THEN
    ASM_SIMP_TAC[LIFT_DROP; PASTECART_FST_SND; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[pde_upto_classical] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `G:real^(1,N)finite_sum->real^K` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w:real^(1,N)finite_sum` THEN REWRITE_TAC[PDE_IN_SLAB] THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`drop(fstcart(w:real^(1,N)finite_sum))`;
                            `sndcart(w:real^(1,N)finite_sum)`] THEN
      ASM_SIMP_TAC[LIFT_DROP; PASTECART_FST_SND; REAL_LT_IMP_LE];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  EXISTS_TAC `iterated_partial l (G:real^(1,N)finite_sum->real^K)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_ITERATED_PARTIAL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  X_GEN_TAC `w:real^(1,N)finite_sum` THEN REWRITE_TAC[PDE_IN_SLAB] THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`drop(fstcart(w:real^(1,N)finite_sum))`;
                        `sndcart(w:real^(1,N)finite_sum)`] THEN
  ASM_SIMP_TAC[LIFT_DROP; PASTECART_FST_SND; REAL_LT_IMP_LE]);;

(* The coefficient matrices depend on K only through K at the point. *)

let PDE_MT_MLBB_KPOINT = prove
 (`!(K:real^N->real^N^N) K' H y c.
     K y = K' y ==> pde_mlbb K H y c = pde_mlbb K' H y c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mlbb; pde_jgi] THEN ASM_REWRITE_TAC[]);;

let PDE_MT_MLCC_KPOINT = prove
 (`!(K:real^N->real^N^N) K' H y.
     K y = K' y ==> pde_mlcc K H y = pde_mlcc K' H y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mlcc; pde_jgi] THEN ASM_REWRITE_TAC[]);;

let PDE_MT_MLBB_ENTRY = prove
 (`!(K:real^N->real^N^N) H y c r s.
     1 <= r /\ r <= dimindex(:(N,N)finite_prod) /\ 1 <= s /\ s <= dimindex(:(N,N)finite_prod)
     ==> (pde_mlbb K H y c)$r$s =
         pde_jtrhess (dimindex(:N)) (\i j. &0) (pde_jgi K y)
           (\e i j. if e = c then (matrify(basis s:real^(N,N)finite_prod):real^N^N)$i$j
                    else &0)
           (\p q i j. &0) (pde_jhc H y) (pde_jhdc H y)
           (1 + (r - 1) DIV dimindex(:N)) (1 + (r - 1) MOD dimindex(:N))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[pde_mlbb; matrix; LAMBDA_BETA] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_PROD]) THEN
  ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
  MP_TAC(SPECL [`dimindex(:N)`; `r:num`] PDE_ML_INDEX_SPLIT) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[LAMBDA_BETA]);;

let PDE_MT_MLCC_ENTRY = prove
 (`!(K:real^N->real^N^N) H y r s.
     1 <= r /\ r <= dimindex(:(N,N)finite_prod) /\ 1 <= s /\ s <= dimindex(:(N,N)finite_prod)
     ==> (pde_mlcc K H y)$r$s =
         pde_jtrhess (dimindex(:N))
           (\i j. (matrify(basis s:real^(N,N)finite_prod):real^N^N)$i$j) (pde_jgi K y)
           (\c i j. &0) (\p q i j. &0) (pde_jhc H y) (pde_jhdc H y)
           (1 + (r - 1) DIV dimindex(:N)) (1 + (r - 1) MOD dimindex(:N))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[pde_mlcc; matrix; LAMBDA_BETA] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_PROD]) THEN
  ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
  MP_TAC(SPECL [`dimindex(:N)`; `r:num`] PDE_ML_INDEX_SPLIT) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[LAMBDA_BETA]);;

(* Atoms on space-time sets. *)

let PDE_MT_ATOM_HC = prove
 (`!S (U:real^N->bool) H m a b.
     open S /\ metric_field U H /\
     (!x:real^(1,N)finite_sum. x IN S ==> sndcart x IN U)
     ==> smooth_map_on S (\x. lift(christoffel H (sndcart x) (basis a) (basis b)$m))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN
   `(\x:real^(1,N)finite_sum.
       lift(christoffel (H:real^N->real^N^N) (sndcart x) (basis a) (basis b)$m)) =
    (\z. lift(christoffel H z (basis a) (basis b)$m)) o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[PDE_SMOOTH_CHR_ENTRY] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]]);;

let PDE_MT_ATOM_HDC = prove
 (`!S (U:real^N->bool) H c m a b.
     open S /\ metric_field U H /\
     (!x:real^(1,N)finite_sum. x IN S ==> sndcart x IN U)
     ==> smooth_map_on S
           (\x. lift(frechet_derivative (\z. christoffel H z (basis a) (basis b))
                                        (at (sndcart x)) (basis c)$m))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN
   `(\x:real^(1,N)finite_sum.
       lift(frechet_derivative (\z. christoffel (H:real^N->real^N^N) z (basis a) (basis b))
                               (at (sndcart x)) (basis c)$m)) =
    ((\v:real^N. lift(v$m)) o
     partial_derivative c (\z. christoffel H z (basis a) (basis b))) o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; partial_derivative]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART];
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let PDE_MT_ATOM_KINV = prove
 (`!S (KK:real^(1,N)finite_sum->real^N^N) i j.
     open S /\ smooth_map_on S ((vectorize:real^N^N->real^(N,N)finite_prod) o KK) /\
     (!x. x IN S ==> ~(det(KK x) = &0))
     ==> smooth_map_on S (\x. lift(matrix_inv(KK x)$i$j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(matrix_inv((KK:real^(1,N)finite_sum->real^N^N) x)$i$j)) =
    (\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$i$j)) o
    ((vectorize:real^N^N->real^(N,N)finite_prod) o (\x. matrix_inv(KK x)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[]);;

(* Space-time smoothness of the coefficient matrices of an invertible field. *)

let PDE_MT_SMOOTH_COMPWISE = prove
 (`!s (f:real^M->real^N).
     open s /\ (!k. 1 <= k /\ k <= dimindex(:N) ==> smooth_map_on s (\x. lift(f x$k)))
     ==> smooth_map_on s f`,
  MESON_TAC[SMOOTH_MAP_ON_COMPONENTWISE]);;

let PDE_MT_COEFF_ST_SMOOTH = prove
 (`!S (U:real^N->bool) (KK:real^(1,N)finite_sum->real^N^N) H.
     open S /\ metric_field U H /\ (!x. x IN S ==> sndcart x IN U) /\
     smooth_map_on S ((vectorize:real^N^N->real^(N,N)finite_prod) o KK) /\
     (!x. x IN S ==> ~(det(KK x) = &0))
     ==> smooth_map_on S
           (\x. (vectorize:real^N^N->real^(N,N)finite_prod) (transp(matrix_inv(KK x)))) /\
         (!c. smooth_map_on S
                (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                       (pde_mlbb (\y. KK(pastecart (fstcart x) y)) H (sndcart x) c))) /\
         smooth_map_on S
           (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                           ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                  (pde_mlcc (\y. KK(pastecart (fstcart x) y)) H (sndcart x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. pde_jgi (\y. (KK:real^(1,N)finite_sum->real^N^N) (pastecart (fstcart x) y))
                (sndcart x) = (\a b. matrix_inv(KK x)$a$b)`
  ASSUME_TAC THENL [REWRITE_TAC[pde_jgi; PASTECART_FST_SND]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN MATCH_MP_TAC PDE_MT_SMOOTH_COMPWISE THEN
  ASM_REWRITE_TAC[] THENL
   [X_GEN_TAC `r:num` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
    MP_TAC(SPECL [`dimindex(:N)`; `r:num`] PDE_ML_INDEX_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[TRANSP_COMPONENT] THEN
    MATCH_MP_TAC PDE_MT_ATOM_KINV THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:num` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[VECTORIZE_COMPONENT; DIMINDEX_FINITE_PROD] THEN
    MP_TAC(SPECL [`dimindex(:N) * dimindex(:N)`; `r:num`] PDE_ML_INDEX_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PDE_MT_MLBB_ENTRY; DIMINDEX_FINITE_PROD];
    X_GEN_TAC `r:num` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[VECTORIZE_COMPONENT; DIMINDEX_FINITE_PROD] THEN
    MP_TAC(SPECL [`dimindex(:N) * dimindex(:N)`; `r:num`] PDE_ML_INDEX_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PDE_MT_MLCC_ENTRY; DIMINDEX_FINITE_PROD]] THEN
  MATCH_MP_TAC PDE_SM_JTRHESS THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; PDE_MT_ATOM_KINV] THEN
  REWRITE_TAC[pde_jhc; pde_jhdc] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  FIRST [MATCH_MP_TAC PDE_MT_ATOM_HC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC PDE_MT_ATOM_HDC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* The chart coefficients are smooth up to the initial time. *)

let PDE_MT_CHART_COEFF_UPTO = prove
 (`!top atlas a b (k:real->A->real^N^N) h (c:(A->bool)#(A->real^N)).
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ a < b
     ==> pde_upto a b (IMAGE (SND c) (FST c))
           (\t z. (vectorize:real^N^N->real^(N,N)finite_prod) (pde_mlaa atlas c k t z)) /\
         (!i. pde_upto a b (IMAGE (SND c) (FST c))
                (\t z. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                  ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                         (pde_mlbt atlas c k h t z i))) /\
         pde_upto a b (IMAGE (SND c) (FST c))
           (\t z. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                             ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                    (pde_mlct atlas c k h t z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                             (metric_local atlas c (h:A->real^N^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < b
        ==> metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                         (metric_local atlas c ((k:real->A->real^N^N) t))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  UNDISCH_TAC `pde_tfam_from atlas a b (k:real->A->real^N^N)` THEN
  REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [pde_upto]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FK:real^(1,N)finite_sum->real^(N,N)finite_prod`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC
   `S = {x | x IN interval(lift(a - e),lift b) PCROSS
                  IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) /\
             (\x. lift(det((matrify:real^(N,N)finite_prod->real^N^N)
                             ((FK:real^(1,N)finite_sum->real^(N,N)finite_prod) x)))) x IN
             (:real^1) DIFF {vec 0}}` THEN
  SUBGOAL_THEN `open (S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
    MATCH_MP_TAC CONTINUOUS_ON_DET_VECTORIZE THEN
    REWRITE_TAC[VECTORIZE_MATRIFY; ETA_AX] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN S
        ==> x IN interval(lift(a - e),lift b) PCROSS
                 IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) /\
            ~(det((matrify:real^(N,N)finite_prod->real^N^N)
                    ((FK:real^(1,N)finite_sum->real^(N,N)finite_prod) x)) = &0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING; LIFT_EQ;
                                   GSYM LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. a <= t /\ t < b /\ y IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)
          ==> (matrify:real^(N,N)finite_prod->real^N^N)
                ((FK:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) y)) =
              metric_local atlas c ((k:real->A->real^N^N) t) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIFY_VECTORIZE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{pastecart (lift t) y | a <= t /\ t < b /\
                            y IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)}
    SUBSET (S:real^(1,N)finite_sum->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_DIFF; IN_UNIV; IN_SING;
                 LIFT_EQ; GSYM LIFT_NUM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                   `metric_local atlas (c:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t)`;
                   `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                 `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `\x. (matrify:real^(N,N)finite_prod->real^N^N)
                        ((FK:real^(1,N)finite_sum->real^(N,N)finite_prod) x)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N)`]
                PDE_MT_COEFF_ST_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^(1,N)finite_sum` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `det:real^N^N->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[PDE_IN_SLAB] THEN SIMP_TAC[];
      REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY; ETA_AX] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - e),lift b) PCROSS
                  IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    REWRITE_TAC[] THEN STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_MT_UPTO_FROM_OPEN THEN
    MAP_EVERY EXISTS_TAC [`S:real^(1,N)finite_sum->bool`;
      `\x. (vectorize:real^N^N->real^(N,N)finite_prod)
             (transp(matrix_inv((matrify:real^(N,N)finite_prod->real^N^N)
                                 ((FK:real^(1,N)finite_sum->real^(N,N)finite_prod) x))))`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[pde_mlaa];
    GEN_TAC THEN MATCH_MP_TAC PDE_MT_UPTO_FROM_OPEN THEN
    MAP_EVERY EXISTS_TAC [`S:real^(1,N)finite_sum->bool`;
      `\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                     ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
             (pde_mlbb (\y. (matrify:real^(N,N)finite_prod->real^N^N)
                              ((FK:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                 (pastecart (fstcart x) y)))
                       (metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N))
                       (sndcart x) i)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; pde_mlbt] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC PDE_MT_MLBB_KPOINT THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PDE_MT_UPTO_FROM_OPEN THEN
    MAP_EVERY EXISTS_TAC [`S:real^(1,N)finite_sum->bool`;
      `\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                     ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
             (pde_mlcc (\y. (matrify:real^(N,N)finite_prod->real^N^N)
                              ((FK:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                 (pastecart (fstcart x) y)))
                       (metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N))
                       (sndcart x))`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; pde_mlct] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC PDE_MT_MLCC_KPOINT THEN
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Uniform ellipticity of the principal chart coefficient                    *)
(* transp(matrix_inv K) on compact pieces and compact time intervals         *)
(* (PDE_MT_CHART_ELLIPTIC), through |v|^2 <= trace K (v . K^-1 v) for        *)
(* positive definite K.                                                      *)
(* ========================================================================= *)

let PDE_MT_TRACE_COVAR = prove
 (`!A:real^N^N. trace(A ** transp A) = norm(vectorize A) pow 2`,
  GEN_TAC THEN REWRITE_TAC[trace; NORM_VECTORIZE_POW_2] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT; TRANSP_COMPONENT; NORM_POW_2; dot] THEN
  REWRITE_TAC[REAL_POW_2]);;

let PDE_MT_INV_LOWER = prove
 (`!K:real^N^N. positive_definite K
     ==> !v. norm v pow 2 <= trace K * (v dot (matrix_inv K ** v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `positive_definite(matrix_inv(K:real^N^N))` MP_TAC THENL
   [ASM_REWRITE_TAC[POSITIVE_DEFINITE_INV]; ALL_TAC] THEN
  REWRITE_TAC[POSITIVE_DEFINITE_COVARIANCE_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(K:real^N^N) = matrix_inv (S:real^N^N) ** transp(matrix_inv S)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM MATRIX_INV_INV] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP; MATRIX_INV_TRANSP];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv(matrix_inv (S:real^N^N) ** transp(matrix_inv S)) = transp S ** (S:real^N^N)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP; INVERTIBLE_MATRIX_INV;
                 MATRIX_INV_TRANSP; MATRIX_INV_INV];
    ALL_TAC] THEN
  REWRITE_TAC[PDE_MT_TRACE_COVAR; GSYM MATRIX_VECTOR_MUL_ASSOC;
              DOT_MATRIX_TRANSP_RMUL; GSYM NORM_POW_2] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  REWRITE_TAC[NORM_POS_LE] THEN
  SUBGOAL_THEN `v = matrix_inv (S:real^N^N) ** (S ** v)` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE]);;

let PDE_MT_TRACE_LE = prove
 (`!K:real^N^N. trace K <= &(dimindex(:N)) * norm(vectorize K)`,
  GEN_TAC THEN REWRITE_TAC[trace] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\i. norm(vectorize(K:real^N^N)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((K:real^N^N)$i)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> x <= y`) THEN
      REWRITE_TAC[COMPONENT_LE_NORM];
      REWRITE_TAC[PDE_ROW_LE_VECTORIZE]];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]);;

let PDE_MT_ELL_ARITH = prove
 (`!x tr q nk B n. x <= tr * q /\ tr <= n * nk /\ nk <= B /\ &0 <= q /\ &0 < n * B /\ &0 <= n
                   ==> inv(n * B) * x <= q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x <= (n * B) * q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tr * q` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `n * nk` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_MESON_TAC[REAL_MUL_SYM]);;

let PDE_MT_CHART_ELLIPTIC = prove
 (`!top atlas a b b' (k:real->A->real^N^N) (c:(A->bool)#(A->real^N)) L.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ a <= b' /\ b' < b /\
     compact L /\ L SUBSET IMAGE (SND c) (FST c)
     ==> ?lam0. &0 < lam0 /\
                !t z. a <= t /\ t <= b' /\ z IN L
                      ==> transp(pde_mlaa atlas c k t z) = pde_mlaa atlas c k t z /\
                          !v. lam0 * norm v pow 2 <= v dot (pde_mlaa atlas c k t z ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pde_tfam_from atlas a b (k:real->A->real^N^N)` THEN
  REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [pde_upto]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FK:real^(1,N)finite_sum->real^(N,N)finite_prod`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?B. &0 < B /\
        !t z. a <= t /\ t <= b' /\ z IN L
              ==> norm((FK:real^(1,N)finite_sum->real^(N,N)finite_prod)
                         (pastecart (lift t) z)) <= B`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `compact (IMAGE (FK:real^(1,N)finite_sum->real^(N,N)finite_prod)
                     (interval[lift a,lift b'] PCROSS (L:real^N->bool)))`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - e),lift b) PCROSS
                  IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN MATCH_MP_TAC PCROSS_MONO THEN
      ASM_REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      GEN_TAC THEN MAP_EVERY UNDISCH_TAC [`&0 < e`; `b' < b`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  EXISTS_TAC `inv(&(dimindex(:N)) * B)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `z IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t < b` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`t <= b'`; `b' < b`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `positive_definite(metric_local atlas (c:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t) z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[positive_definite; symmetric_matrix] THEN
    SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                    (metric_local atlas c ((k:real->A->real^N^N) t))` MP_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
    REWRITE_TAC[metric_field] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pde_mlaa] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP POSITIVE_DEFINITE_IMP_SYMMETRIC) THEN
  SUBGOAL_THEN
   `transp(matrix_inv(metric_local atlas (c:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t) z)) =
    matrix_inv(metric_local atlas c (k t) z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_INV_TRANSP] THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN
  MATCH_MP_TAC PDE_MT_ELL_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`trace(metric_local atlas (c:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t) z)`;
    `norm((vectorize:real^N^N->real^(N,N)finite_prod)
            (metric_local atlas (c:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t) z))`] THEN
  REWRITE_TAC[PDE_MT_TRACE_LE; REAL_POS] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `metric_local atlas (c:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t) z`
             PDE_MT_INV_LOWER) THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod)
        (metric_local atlas (c:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t) z) =
      (FK:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) z)`
    SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM POSITIVE_DEFINITE_INV]) THEN
    REWRITE_TAC[positive_definite] THEN STRIP_TAC THEN
    ASM_CASES_TAC `v:real^N = vec 0` THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL; REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`]]);;

(* ========================================================================= *)
(* Torus coefficients for a chart piece (PDE_MT_TORUS_COEFF): the scaled     *)
(* chart coefficients lam^-2 pde_mlaa, lam^-1 pde_mlbt, pde_mlct             *)
(* transplanted to Z^N-periodic admissible coefficients on [0, b' - a),      *)
(* agreeing near the piece in the torus coordinates x = z / lam + 1/2.       *)
(* ========================================================================= *)

let PDE_MT_UPTO_OPEN_SUBSET = prove
 (`!a b (U:real^N->bool) V (u:real->real^N->real^K).
     pde_upto a b U u /\ V SUBSET U ==> pde_upto a b V u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `FG:real^(1,N)finite_sum->real^K`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let PDE_MT_UPTO_LINEAR = prove
 (`!a b (U:real^N->bool) (L:real^P->real^Q) (f:real->real^N->real^P).
     open U /\ linear L /\ pde_upto a b U f ==> pde_upto a b U (\t x. L(f t x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^P`
      STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `(L:real^P->real^Q) o (FG:real^(1,N)finite_sum->real^P)`] THEN
  ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]);;

let PDE_MT_VEC_CMUL_LINEAR = prove
 (`!c. linear (\x:real^(M,M)finite_prod. (vectorize:real^M^M->real^(M,M)finite_prod)
                                           (c %% (matrify x:real^M^M)))`,
  GEN_TAC THEN REWRITE_TAC[VECTORIZE_CMUL; VECTORIZE_MATRIFY] THEN
  REWRITE_TAC[LINEAR_SCALING]);;

let PDE_MT_UPTO_RESTRICT_LINEAR = prove
 (`!a b b' (U:real^N->bool) U1 (G:real->real^N->real^P) (L:real^P->real^Q).
     open U1 /\ U1 SUBSET U /\ b' <= b /\ pde_upto a b U G /\ linear L
     ==> pde_upto a b' U1 (\t z. L(G t z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_MT_UPTO_LINEAR THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PDE_MT_UPTO_OPEN_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `b:real` THEN
  ASM_REWRITE_TAC[]);;

let PDE_MT_TORUS_COEFF = prove
 (`!top atlas a b b' (k:real->A->real^N^N) h (c:(A->bool)#(A->real^N)) L lam.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b k /\ a < b' /\ b' < b /\
     compact L /\ L SUBSET IMAGE (SND c) (FST c) /\
     &0 < lam /\ L SUBSET ball(vec 0,lam / &4)
     ==> ?aaT bbT ccT lamT V.
           pde_tcoeff (b' - a) lamT (aaT:real->real^N->real^N^N)
                      (bbT:real->real^N->num->real^(N,N)finite_prod^(N,N)finite_prod) ccT /\
           open V /\ L SUBSET V /\ V SUBSET IMAGE (SND c) (FST c) /\
           !t z. a <= t /\ t < b' /\ z IN V
                 ==> aaT (t - a) (inv lam % z + inv(&2) % vec 1) =
                       inv(lam pow 2) %% pde_mlaa atlas c k t z /\
                     (!i. 1 <= i /\ i <= dimindex(:N)
                          ==> bbT (t - a) (inv lam % z + inv(&2) % vec 1) i =
                              inv lam %% pde_mlbt atlas c k h t z i) /\
                     ccT (t - a) (inv lam % z + inv(&2) % vec 1) = pde_mlct atlas c k h t z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->bool`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`]
                PDM_EUCLID_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^N->real` (X_CHOOSE_THEN `U1:real^N->bool`
    (X_CHOOSE_THEN `L1:real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(U1:real^N->bool) SUBSET L1` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[REAL_ARITH `~(&1 = &0)`]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `b':real`; `k:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `L1:real^N->bool`] PDE_MT_CHART_ELLIPTIC) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                PDE_MT_CHART_COEFF_UPTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC [`a < b'`; `b' < b`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(U1:real^N->bool) SUBSET IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `b' <= b` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  (* the principal coefficient *)
  SUBGOAL_THEN
   `?BB. pde_upto a b' (:real^N)
           (\t x. (vectorize:real^N^N->real^(N,N)finite_prod) (BB t x)) /\
         (!t. pde_zper (BB t)) /\
         (!t x. a <= t /\ t < b'
                ==> transp(BB t x) = BB t x /\
                    !v. min (inv(lam pow 2) * lam0) (&1) * norm v pow 2 <= v dot (BB t x ** v)) /\
         ?V. open V /\ L SUBSET V /\
             !t z. a <= t /\ t < b' /\ z IN V
                   ==> BB t (inv lam % z + inv(&2) % vec 1) =
                       inv(lam pow 2) %% pde_mlaa atlas (c:(A->bool)#(A->real^N)) k t z`
  (X_CHOOSE_THEN `BB:real->real^N->real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `V1:real^N->bool` STRIP_ASSUME_TAC))))) THENL
   [MATCH_MP_TAC PDM_COEFF_TRANSPLANT_PRINCIPAL THEN EXISTS_TAC `U1:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT];
      MP_TAC(ISPECL [`a:real`; `b:real`; `b':real`;
         `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `U1:real^N->bool`;
         `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t z)`;
         `\x:real^(N,N)finite_prod. (vectorize:real^N^N->real^(N,N)finite_prod)
                                      (inv(lam pow 2) %% (matrify x:real^N^N))`]
        PDE_MT_UPTO_RESTRICT_LINEAR) THEN
      ASM_REWRITE_TAC[PDE_MT_VEC_CMUL_LINEAR; MATRIFY_VECTORIZE];
      MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `z:real^N`] o
        check (fun th -> can (find_term ((=) `lam0:real`)) (concl th) && is_forall(concl th))) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[TRANSP_MATRIX_CMUL] THEN
      X_GEN_TAC `v:real^N` THEN REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  (* the first-order coefficients *)
  SUBGOAL_THEN
   `!i. ?H V. pde_upto a b' (:real^N) H /\ (!t. pde_zper (H t)) /\ open V /\ L SUBSET V /\
              !t z. a <= t /\ t < b' /\ z IN V
                    ==> H t (inv lam % z + inv(&2) % vec 1) =
                        (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                   ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                          (inv lam %% pde_mlbt atlas (c:(A->bool)#(A->real^N))
                                        (k:real->A->real^N^N) h t z i)`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`a:real`; `b':real`; `lam:real`;
                   `\t z. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                     ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                            (inv lam %% pde_mlbt atlas (c:(A->bool)#(A->real^N))
                                          (k:real->A->real^N^N) h t z i)`;
                   `U1:real^N->bool`; `L:real^N->bool`] PDM_COEFF_TRANSPLANT_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`a:real`; `b:real`; `b':real`;
         `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `U1:real^N->bool`;
         `\t z. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                           ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                  (pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) h t z i)`;
         `\x:real^((N,N)finite_prod,(N,N)finite_prod)finite_prod.
            (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                       ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
              (inv lam %% (matrify x:real^(N,N)finite_prod^(N,N)finite_prod))`]
        PDE_MT_UPTO_RESTRICT_LINEAR) THEN
      ASM_REWRITE_TAC[PDE_MT_VEC_CMUL_LINEAR; MATRIFY_VECTORIZE];
      REWRITE_TAC[] THEN MESON_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN
      `HB:num->real->real^N->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod`
      (X_CHOOSE_THEN `VB:num->real^N->bool` (LABEL_TAC "HB")))] THEN
  (* the zeroth-order coefficient *)
  SUBGOAL_THEN
   `?H V. pde_upto a b' (:real^N) H /\ (!t. pde_zper (H t)) /\ open V /\ L SUBSET V /\
          !t z. a <= t /\ t < b' /\ z IN V
                ==> H t (inv lam % z + inv(&2) % vec 1) =
                    (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                               ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                      (pde_mlct atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) h t z)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`a:real`; `b':real`; `lam:real`;
                   `\t z. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                     ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                            (pde_mlct atlas (c:(A->bool)#(A->real^N))
                                          (k:real->A->real^N^N) h t z)`;
                   `U1:real^N->bool`; `L:real^N->bool`] PDM_COEFF_TRANSPLANT_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`a:real`; `b:real`; `b':real`;
         `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `U1:real^N->bool`;
         `\t z. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                           ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                  (pde_mlct atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) h t z)`;
         `\x:real^((N,N)finite_prod,(N,N)finite_prod)finite_prod. x`]
        PDE_MT_UPTO_RESTRICT_LINEAR) THEN
      ASM_REWRITE_TAC[LINEAR_ID; ETA_AX];
      REWRITE_TAC[] THEN MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN
      `HC:real->real^N->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod`
      (X_CHOOSE_THEN `VC:real^N->bool` STRIP_ASSUME_TAC))] THEN
  MAP_EVERY EXISTS_TAC
   [`\s x. (BB:real->real^N->real^N^N) (s + a) x`;
    `\s x i. if 1 <= i /\ i <= dimindex(:N)
             then (matrify:real^((N,N)finite_prod,(N,N)finite_prod)finite_prod
                           ->real^(N,N)finite_prod^(N,N)finite_prod)
                    ((HB:num->real->real^N->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                       i (s + a) x)
             else mat 0`;
    `\s x. (matrify:real^((N,N)finite_prod,(N,N)finite_prod)finite_prod
                    ->real^(N,N)finite_prod^(N,N)finite_prod)
             ((HC:real->real^N->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod) (s + a) x)`;
    `min (inv(lam pow 2) * lam0) (&1)`;
    `(U1:real^N->bool) INTER V1 INTER VC INTER
     INTERS (IMAGE (VB:num->real^N->bool) (1..dimindex(:N)))`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pde_tcoeff] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT];
      MP_TAC(ISPECL [`a:real`; `b':real`; `(:real^N)`;
                     `\t x. (vectorize:real^N^N->real^(N,N)finite_prod)
                              ((BB:real->real^N->real^N^N) t x)`; `a:real`]
                    PDE_MT_UPTO_SHIFT) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; REAL_SUB_REFL];
      X_GEN_TAC `i:num` THEN ASM_CASES_TAC `1 <= i /\ i <= dimindex(:N)` THEN
      ASM_REWRITE_TAC[VECTORIZE_MATRIFY; PDE_UPTO_CONST] THEN
      MP_TAC(ISPECL [`a:real`; `b':real`; `(:real^N)`;
                     `(HB:num->real->real^N->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                        i`; `a:real`] PDE_MT_UPTO_SHIFT) THEN
      USE_THEN "HB" (MP_TAC o SPEC `i:num`) THEN SIMP_TAC[OPEN_UNIV; REAL_SUB_REFL; ETA_AX];
      MP_TAC(ISPECL [`a:real`; `b':real`; `(:real^N)`;
                     `HC:real->real^N->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod`;
                     `a:real`] PDE_MT_UPTO_SHIFT) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; REAL_SUB_REFL; VECTORIZE_MATRIFY; ETA_AX];
      X_GEN_TAC `t:real` THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[ETA_AX];
        MATCH_MP_TAC PDE_ZPER_COMPOSE THEN ASM_REWRITE_TAC[ETA_AX];
        X_GEN_TAC `i:num` THEN ASM_CASES_TAC `1 <= i /\ i <= dimindex(:N)` THEN
        ASM_REWRITE_TAC[PDE_ZPER_CONST] THEN MATCH_MP_TAC PDE_ZPER_COMPOSE THEN
        USE_THEN "HB" (MP_TAC o SPEC `i:num`) THEN SIMP_TAC[ETA_AX]];
      MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `transp:real^N^N->real^N^N`)) (concl th) &&
        can (find_term ((=) `BB:real->real^N->real^N^N`)) (concl th))) THEN
      MAP_EVERY UNDISCH_TAC [`&0 <= t`; `t < b' - a`] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_INTERS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "HB" (MP_TAC o SPEC `i:num`) THEN
    SIMP_TAC[];
    ASM_REWRITE_TAC[SUBSET_INTER; SUBSET_INTERS; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "HB" (MP_TAC o SPEC `i:num`) THEN
    SIMP_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U1:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN
    REWRITE_TAC[IN_INTER; IN_INTERS; FORALL_IN_IMAGE; IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_SUB_ADD; MATRIFY_VECTORIZE]]);;

(* ========================================================================= *)
(* The operator pde_lop0 applied to a cut-off map p w (p real^1-valued): the *)
(* product rule                                                              *)
(*   L(p w) = p L(w) + [L,p] w,                                              *)
(* with the first-order commutator pde_mt_comm (coefficients from A, B and   *)
(* the derivatives of p up to order two).                                    *)
(* ========================================================================= *)

let pde_mt_comm = new_definition
 `pde_mt_comm (A:real^N->real^N^N) (B:real^N->num->real^K^K) (p:real^N->real^1)
              (w:real^N->real^K) (z:real^N) =
    vsum(1..dimindex(:N))
      (\i. vsum(1..dimindex(:N))
             (\j. A z$i$j %
                  (drop(partial_derivative i p z) % partial_derivative j w z +
                   drop(partial_derivative j p z) % partial_derivative i w z +
                   drop(partial_derivative i (partial_derivative j p) z) % w z))) +
    vsum(1..dimindex(:N)) (\i. drop(partial_derivative i p z) % (B z i ** w z))`;;

let PDE_MT_PARTIAL_MUL_OPEN = prove
 (`!U (p:real^N->real^1) (w:real^N->real^K) j y.
     open U /\ smooth_map_on U p /\ smooth_map_on U w /\ y IN U
     ==> partial_derivative j (\z. drop(p z) % w z) y =
         drop(p y) % partial_derivative j w y + drop(partial_derivative j p y) % w y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_MUL THEN
  ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE]);;

let PDE_MT_PARTIAL2_MUL_OPEN = prove
 (`!U (p:real^N->real^1) (w:real^N->real^K) i j z.
     open U /\ smooth_map_on U p /\ smooth_map_on U w /\ z IN U
     ==> partial_derivative i (partial_derivative j (\z. drop(p z) % w z)) z =
         drop(p z) % partial_derivative i (partial_derivative j w) z +
         drop(partial_derivative i p z) % partial_derivative j w z +
         drop(partial_derivative j p z) % partial_derivative i w z +
         drop(partial_derivative i (partial_derivative j p) z) % w z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`;
                 `partial_derivative j (\z. drop((p:real^N->real^1) z) % (w:real^N->real^K) z)`;
                 `\y. drop((p:real^N->real^1) y) % partial_derivative j (w:real^N->real^K) y +
                      drop(partial_derivative j p y) % w y`;
                 `U:real^N->bool`; `z:real^N`] PARTIAL_DERIVATIVE_LOCAL_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_MT_PARTIAL_MUL_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U (partial_derivative j (p:real^N->real^1)) /\
    smooth_map_on U (partial_derivative j (w:real^N->real^K))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U (\y. drop((p:real^N->real^1) y) % partial_derivative j (w:real^N->real^K) y) /\
    smooth_map_on U (\y. drop(partial_derivative j (p:real^N->real^1) y) % (w:real^N->real^K) y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`;
                 `\y. drop((p:real^N->real^1) y) % partial_derivative j (w:real^N->real^K) y`;
                 `\y. drop(partial_derivative j (p:real^N->real^1) y) % (w:real^N->real^K) y`;
                 `z:real^N`] PARTIAL_DERIVATIVE_ADD) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `p:real^N->real^1`; `partial_derivative j (w:real^N->real^K)`;
                 `i:num`; `z:real^N`] PDE_MT_PARTIAL_MUL_OPEN) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `partial_derivative j (p:real^N->real^1)`; `w:real^N->real^K`;
                 `i:num`; `z:real^N`] PDE_MT_PARTIAL_MUL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN VECTOR_ARITH_TAC);;

let PDE_MT_LOP0_CUTOFF = prove
 (`!U (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (p:real^N->real^1)
    (w:real^N->real^K) z.
     open U /\ z IN U /\ smooth_map_on U p /\ smooth_map_on U w
     ==> pde_lop0 A B C (\z. drop(p z) % w z) z =
         drop(p z) % pde_lop0 A B C w z + pde_mt_comm A B p w z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lop0; pde_mt_comm] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `p:real^N->real^1`; `w:real^N->real^K`]
                PDE_MT_PARTIAL2_MUL_OPEN) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `p:real^N->real^1`; `w:real^N->real^K`]
                PDE_MT_PARTIAL_MUL_OPEN) THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(VECTOR_ARITH
   `s1 = r % s1' + t1 /\ s2 = r % s2' + t2 /\ c = r % c'
    ==> s1 + s2 + c:real^K = r % (s1' + s2' + c') + (t1 + t2)`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM VSUM_LMUL; GSYM VSUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM VSUM_LMUL; GSYM VSUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
    REWRITE_TAC[GSYM VSUM_LMUL; GSYM VSUM_ADD_NUMSEG];
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL]]);;

(* ========================================================================= *)
(* The dilation x = z / lam + 1/2.  The torus operator pde_lop at x, for     *)
(* coefficients equal to lam^-2 A, lam^-1 B, C at x, is the operator         *)
(* pde_lop0 A B C of the dilated map at z.                                   *)
(* ========================================================================= *)

let PDE_MT_LOP_DILATE = prove
 (`!lam (aaT:real->real^N->real^N^N) (bbT:real->real^N->num->real^K^K) ccT
    (w:real->real^N->real^K) s (A:real^N->real^N^N) (B:real^N->num->real^K^K) C z.
     smooth_map_on (:real^N) (w s) /\
     aaT s (inv lam % z + inv(&2) % vec 1) = inv(lam pow 2) %% A z /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> bbT s (inv lam % z + inv(&2) % vec 1) i = inv lam %% B z i) /\
     ccT s (inv lam % z + inv(&2) % vec 1) = C z
     ==> pde_lop aaT bbT ccT w s (inv lam % z + inv(&2) % vec 1) =
         pde_lop0 A B C (\z. w s (inv lam % z + inv(&2) % vec 1)) z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lop; pde_lop0] THEN
  MP_TAC(GEN `l:num list`
    (ISPECL [`l:num list`; `(w:real->real^N->real^K) s`; `inv lam`; `inv(&2) % vec 1:real^N`]
            PDM_ITERATED_PARTIAL_AFFINE)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (\z. (w:real->real^N->real^K) s (inv lam % z + inv(&2) % vec 1)) z =
        inv lam % partial_derivative i (w s) (inv lam % z + inv(&2) % vec 1)`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`[i:num]`; `z:real^N`]) THEN
    REWRITE_TAC[iterated_partial; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. partial_derivative i
            (partial_derivative j
               (\z. (w:real->real^N->real^K) s (inv lam % z + inv(&2) % vec 1))) z =
          inv(lam pow 2) %
          partial_derivative i (partial_derivative j (w s)) (inv lam % z + inv(&2) % vec 1)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`[i:num; j:num]`; `z:real^N`]) THEN
    REWRITE_TAC[iterated_partial; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_INV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(VECTOR_ARITH
   `s1:real^K = s1' /\ s2 = s2' ==> s1 + s2 + c = s1' + s2' + c`) THEN
  CONJ_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MATRIX_CMUL_COMPONENT; VECTOR_MUL_ASSOC; REAL_MUL_SYM];
    ASM_SIMP_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_RMUL]]);;

(* ========================================================================= *)
(* From torus solutions to cut-off chart functions.  If w solves the torus   *)
(* equation on [0,b'-a) with coefficients agreeing on V with lam^-2 A,       *)
(* lam^-1 B, C (dilation x = z/lam + 1/2, time shift t - a), and psi is      *)
(* a cutoff vanishing off a compact Lp in V, then psi(z) w(t-a,x) solves the *)
(* chart equation with the operator pde_lop0 of A t, B t, C t and the        *)
(* forcing psi g - [L,psi] w at every z in R^N.                              *)
(* ========================================================================= *)

let PDE_MT_HVD_SHIFT = prove
 (`!(f:real->real^K) D a t.
     ((\r. f(drop r)) has_vector_derivative D) (at (lift(t - a)))
     ==> ((\r. f(drop r - a)) has_vector_derivative D) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\r:real^1. r - lift a) has_vector_derivative (vec 1 - vec 0)) (at (lift t))`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID; HAS_VECTOR_DERIVATIVE_CONST];
    REWRITE_TAC[VECTOR_SUB_RZERO] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`\r:real^1. r - lift a`; `\r:real^1. (f:real->real^K)(drop r)`;
                 `vec 1:real^1`; `D:real^K`; `lift t`] VECTOR_DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_DEF; DROP_SUB; LIFT_DROP; DROP_VEC; VECTOR_MUL_LID; GSYM LIFT_SUB]);;

let PDE_MT_LOP0_ZERO_OPEN = prove
 (`!S (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (FF:real^N->real^K) z.
     open S /\ z IN S /\ (!y. y IN S ==> FF y = vec 0)
     ==> pde_lop0 A B C FF z = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lop0] THEN
  SUBGOAL_THEN
   `!l. iterated_partial l (FF:real^N->real^K) z = vec 0`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. partial_derivative i (FF:real^N->real^K) z = vec 0) /\
    (!i j. partial_derivative i (partial_derivative j (FF:real^N->real^K)) z = vec 0) /\
    FF z = vec 0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `[i:num]`);
      FIRST_X_ASSUM(MP_TAC o SPEC `[i:num; j:num]`);
      FIRST_X_ASSUM(MP_TAC o SPEC `[]:num list`)] THEN
    REWRITE_TAC[iterated_partial];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; MATRIX_VECTOR_MUL_RZERO; VSUM_0; VECTOR_ADD_LID]);;

let PDE_MT_COMM_ZERO_OPEN = prove
 (`!S (A:real^N->real^N^N) (B:real^N->num->real^K^K) (p:real^N->real^1) w z.
     open S /\ z IN S /\ (!y. y IN S ==> p y = vec 0)
     ==> pde_mt_comm A B p w z = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mt_comm] THEN
  SUBGOAL_THEN
   `!l. iterated_partial l (p:real^N->real^1) z = vec 0`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. partial_derivative i (p:real^N->real^1) z = vec 0) /\
    (!i j. partial_derivative i (partial_derivative j (p:real^N->real^1)) z = vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `[i:num]`);
      FIRST_X_ASSUM(MP_TAC o SPEC `[i:num; j:num]`)] THEN
    REWRITE_TAC[iterated_partial];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_RZERO;
                  VSUM_0]);;

let PDE_MT_UNTRANS_EQ = prove
 (`!a b' lam (aaT:real->real^N->real^N^N) (bbT:real->real^N->num->real^K^K) ccT
    (A:real->real^N->real^N^N) (B:real->real^N->num->real^K^K) C V
    (w:real->real^N->real^K) g (psi:real^N->real) Lp.
     (!t z. a <= t /\ t < b' /\ z IN V
            ==> aaT (t - a) (inv lam % z + inv(&2) % vec 1) = inv(lam pow 2) %% A t z /\
                (!i. 1 <= i /\ i <= dimindex(:N)
                     ==> bbT (t - a) (inv lam % z + inv(&2) % vec 1) i = inv lam %% B t z i) /\
                ccT (t - a) (inv lam % z + inv(&2) % vec 1) = C t z) /\
     pde_tsol (b' - a) aaT bbT ccT g (\x. vec 0) w /\
     smooth_map_on (:real^N) (\z. lift(psi z)) /\
     compact Lp /\ Lp SUBSET V /\ (!z. ~(z IN Lp) ==> psi z = &0)
     ==> !t z. a < t /\ t < b'
               ==> ((\s. psi z % w (drop s - a) (inv lam % z + inv(&2) % vec 1))
                    has_vector_derivative
                    (pde_lop0 (A t) (B t) (C t)
                       (\z. psi z % w (t - a) (inv lam % z + inv(&2) % vec 1)) z -
                     pde_mt_comm (A t) (B t) (\z. lift(psi z))
                       (\z. w (t - a) (inv lam % z + inv(&2) % vec 1)) z +
                     psi z % g (t - a) (inv lam % z + inv(&2) % vec 1))) (at (lift t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "agr") (CONJUNCTS_THEN2 (LABEL_TAC "sol")
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) ((w:real->real^N->real^K) (t - a))` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_UPTO_SLICE_SMOOTH THEN EXISTS_TAC `b' - a:real` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[pde_tsol]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N)
      (\z. (w:real->real^N->real^K) (t - a) (inv lam % z + inv(&2) % vec 1))`
  ASSUME_TAC THENL [MATCH_MP_TAC PDM_SMOOTH_AFFINE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^N) IN Lp` THENL
   [ALL_TAC;
    (* off the support: everything vanishes near z *)
    SUBGOAL_THEN `open((:real^N) DIFF Lp)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    SUBGOAL_THEN `(psi:real^N->real) z = &0` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN
     `pde_lop0 ((A:real->real^N->real^N^N) t) ((B:real->real^N->num->real^K^K) t) (C t)
        (\z. (psi:real^N->real) z % (w:real->real^N->real^K) (t - a)
                                       (inv lam % z + inv(&2) % vec 1)) z = vec 0 /\
      pde_mt_comm ((A:real->real^N->real^N^N) t) ((B:real->real^N->num->real^K^K) t)
        (\z. lift((psi:real^N->real) z))
        (\z. (w:real->real^N->real^K) (t - a) (inv lam % z + inv(&2) % vec 1)) z = vec 0`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC PDE_MT_LOP0_ZERO_OPEN; MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN] THEN
      EXISTS_TAC `(:real^N) DIFF Lp` THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO; LIFT_NUM];
      REWRITE_TAC[VECTOR_SUB_REFL; HAS_VECTOR_DERIVATIVE_CONST]]] THEN
  (* on the support *)
  SUBGOAL_THEN `(z:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "agr" (MP_TAC o SPECL [`t:real`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`lam:real`; `aaT:real->real^N->real^N^N`; `bbT:real->real^N->num->real^K^K`;
                 `ccT:real->real^N->real^K^K`; `w:real->real^N->real^K`; `t - a:real`;
                 `(A:real->real^N->real^N^N) t`; `(B:real->real^N->num->real^K^K) t`;
                 `(C:real->real^N->real^K^K) t`; `z:real^N`] PDE_MT_LOP_DILATE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `(A:real->real^N->real^N^N) t`;
                 `(B:real->real^N->num->real^K^K) t`; `(C:real->real^N->real^K^K) t`;
                 `\z. lift((psi:real^N->real) z)`;
                 `\z. (w:real->real^N->real^K) (t - a) (inv lam % z + inv(&2) % vec 1)`;
                 `z:real^N`] PDE_MT_LOP0_CUTOFF) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
  REMOVE_THEN "sol" (MP_TAC o el 3 o CONJUNCTS o REWRITE_RULE[pde_tsol]) THEN
  DISCH_THEN(MP_TAC o SPECL [`t - a:real`; `inv lam % z + inv(&2) % vec 1:real^N`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`\s. (w:real->real^N->real^K) s (inv lam % z + inv(&2) % vec 1)`;
                 `pde_lop0 ((A:real->real^N->real^N^N) t) ((B:real->real^N->num->real^K^K) t)
                    (C t) (\z. (w:real->real^N->real^K) (t - a) (inv lam % z + inv(&2) % vec 1)) z +
                  g (t - a) (inv lam % z + inv(&2) % vec 1)`; `a:real`; `t:real`]
                PDE_MT_HVD_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((psi:real^N->real) z %
     pde_lop0 ((A:real->real^N->real^N^N) t) ((B:real->real^N->num->real^K^K) t) (C t)
       (\z. (w:real->real^N->real^K) (t - a) (inv lam % z + inv(&2) % vec 1)) z +
     pde_mt_comm (A t) (B t) (\z. lift(psi z))
       (\z. w (t - a) (inv lam % z + inv(&2) % vec 1)) z) -
    pde_mt_comm (A t) (B t) (\z. lift(psi z))
       (\z. w (t - a) (inv lam % z + inv(&2) % vec 1)) z +
    psi z % (g:real->real^N->real^K) (t - a) (inv lam % z + inv(&2) % vec 1) =
    psi z % (pde_lop0 (A t) (B t) (C t)
                (\z. w (t - a) (inv lam % z + inv(&2) % vec 1)) z +
             g (t - a) (inv lam % z + inv(&2) % vec 1))`
  SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Torus solution operators.  For admissible torus coefficients there is     *)
(* a map E from forcings to solutions with zero initial data (M4,            *)
(* PDE_TORUS_LIN_HOLDS of pc_pde_texist); solutions are unique               *)
(* (PDE_TORUS_UNIQUE).                                                       *)
(* ========================================================================= *)

let PDE_MT_TSOL_OP = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc.
     &0 < tmax /\ pde_tcoeff tmax lam aa bb cc
     ==> ?E. !g:real->real^N->real^K.
               pde_upto (&0) tmax (:real^N) g /\ (!t. pde_zper (g t))
               ==> pde_tsol tmax aa bb cc g (\x. vec 0) (E g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  X_GEN_TAC `g:real->real^N->real^K` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:N)`; `(:K)`] PDE_TORUS_LIN_HOLDS) THEN
  REWRITE_TAC[PDE_TORUS_LIN_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `lam:real` THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; PDE_ZPER_CONST]);;

let PDE_MT_TSOL_OP_UNIQUE = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc g u.
     &0 < tmax /\ pde_tcoeff tmax lam aa bb cc /\
     pde_tsol tmax aa bb cc g (\x. vec 0) u
     ==> !E. (!g:real->real^N->real^K.
                pde_upto (&0) tmax (:real^N) g /\ (!t. pde_zper (g t))
                ==> pde_tsol tmax aa bb cc g (\x. vec 0) (E g)) /\
             pde_upto (&0) tmax (:real^N) g /\ (!t. pde_zper (g t))
             ==> !t y. &0 <= t /\ t < tmax ==> E g t y = u t y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC PDE_TORUS_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `aa:real->real^N->real^N^N`;
                        `bb:real->real^N->num->real^K^K`; `cc:real->real^N->real^K^K`;
                        `g:real->real^N->real^K`; `\x:real^N. vec 0:real^K`] THEN
  ASM_SIMP_TAC[ETA_AX]);;

(* ========================================================================= *)
(* From chart solutions to torus solutions.  If W solves a chart equation    *)
(* dW/dt = L(t) W + G on an open set U0 and psi is a cutoff vanishing off    *)
(* a compact Lp of U0 inside the agreement set V and inside ball(0,lam/4),   *)
(* then the transplant of psi W(. + a) solves the torus equation with the    *)
(* transplanted forcing psi G - [L,psi] W.                                   *)
(* ========================================================================= *)

let PDE_MT_LOP0_LOCAL = prove
 (`!S (A:real^N->real^N^N) (B:real^N->num->real^K^K) C (F1:real^N->real^K) F2 z.
     open S /\ z IN S /\ (!y. y IN S ==> F1 y = F2 y)
     ==> pde_lop0 A B C F1 z = pde_lop0 A B C F2 z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!l. iterated_partial l (F1:real^N->real^K) z = iterated_partial l F2 z`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(GEN `i:num` (SPEC `[i:num]` th)) THEN
    MP_TAC(GEN `i:num` (GEN `j:num` (SPEC `[i:num; j:num]` th))) THEN
    MP_TAC(SPEC `[]:num list` th)) THEN
  REWRITE_TAC[iterated_partial] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[pde_lop0]);;

let PDE_MT_LOP0_COEFF_AT = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) C A' B' C' (FF:real^N->real^K) z.
     A z = A' z /\ (!i. 1 <= i /\ i <= dimindex(:N) ==> B z i = B' z i) /\ C z = C' z
     ==> pde_lop0 A B C FF z = pde_lop0 A' B' C' FF z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lop0] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]);;

(* Reduction of a periodic torus equation to points of the unit cube. *)

let PDE_MT_FRAC_DECOMP = prove
 (`!x:real^N. pdm_frac x IN interval[vec 0,vec 1] /\
              x = pdm_frac x + pdm_floorv x /\
              (!i. 1 <= i /\ i <= dimindex(:N) ==> integer(pdm_floorv x$i))`,
  GEN_TAC THEN REWRITE_TAC[IN_INTERVAL; CART_EQ; VECTOR_ADD_COMPONENT; VEC_COMPONENT] THEN
  SIMP_TAC[PDM_FRAC_COMPONENT; PDM_FLOORV_COMPONENT; FLOOR; FRAC_FLOOR] THEN
  REPEAT STRIP_TAC THEN TRY REAL_ARITH_TAC THEN
  MP_TAC(SPEC `(x:real^N)$i` FLOOR) THEN REAL_ARITH_TAC);;

let PDE_MT_ZPER_EQ_REDUCE = prove
 (`!(aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc
    (u:real->real^N->real^K) GG s.
     pde_zper (aa s) /\ pde_zper (cc s) /\ (!i. pde_zper (\y. bb s y i)) /\
     (!r. pde_zper (u r)) /\ smooth_map_on (:real^N) (u s) /\ pde_zper GG /\
     (!y. y IN interval[vec 0,vec 1]
          ==> ((\r. u (drop r) y) has_vector_derivative (pde_lop aa bb cc u s y + GG y))
              (at (lift s)))
     ==> !x. ((\r. u (drop r) x) has_vector_derivative (pde_lop aa bb cc u s x + GG x))
             (at (lift s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `x:real^N` PDE_MT_FRAC_DECOMP) THEN
  ABBREV_TAC `y:real^N = pdm_frac x` THEN ABBREV_TAC `m:real^N = pdm_floorv x` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^N->real^K. pde_zper w ==> w x = w y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `x:real^N`)) THEN
    MATCH_MP_TAC PDE_ZPER_INTEGER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\r. (u:real->real^N->real^K) (drop r) x) = (\r. u (drop r) y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_lop (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc
            (u:real->real^N->real^K) s x + GG x =
    pde_lop aa bb cc u s y + GG y`
  SUBST1_TAC THENL
   [REWRITE_TAC[PDE_LOP_LOP0] THEN BINOP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC PDE_ZPER_LOP0 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

(* The unit cube lies in the open box where pdm_transplant is given by the  *)
(* formula; dilation facts.                                                  *)

let PDE_MT_CUBE_IN_BOX = prove
 (`!y:real^N. y IN interval[vec 0,vec 1]
              ==> y IN interval(--(&1 / &4) % vec 1,(&1 + &1 / &4) % vec 1)`,
  GEN_TAC THEN
  SIMP_TAC[IN_INTERVAL; VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let PDE_MT_DILATE_INV = prove
 (`!lam (y:real^N). &0 < lam
     ==> inv lam % (lam % (y - inv(&2) % vec 1)) + inv(&2) % vec 1 = y /\
         lam % ((inv lam % y + inv(&2) % vec 1) - inv(&2) % vec 1) = y`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RINV; REAL_LT_IMP_NZ;
               VECTOR_MUL_LID; VECTOR_ARITH `(a + b) - b:real^N = a`] THEN
  VECTOR_ARITH_TAC);;

let PDE_MT_DILATE_OPEN = prove
 (`!lam. &0 < lam
     ==> open(IMAGE (\x:real^N. lam % x + --(lam % inv(&2) % vec 1))
                    (interval(--(&1 / &4) % vec 1,(&1 + &1 / &4) % vec 1))) /\
         (!z. z IN IMAGE (\x:real^N. lam % x + --(lam % inv(&2) % vec 1))
                         (interval(--(&1 / &4) % vec 1,(&1 + &1 / &4) % vec 1))
              ==> inv lam % z + inv(&2) % vec 1 IN
                  interval(--(&1 / &4) % vec 1,(&1 + &1 / &4) % vec 1)) /\
         (!y. y IN interval(--(&1 / &4) % vec 1,(&1 + &1 / &4) % vec 1)
              ==> lam % (y - inv(&2) % vec 1) IN
                  IMAGE (\x:real^N. lam % x + --(lam % inv(&2) % vec 1))
                        (interval(--(&1 / &4) % vec 1,(&1 + &1 / &4) % vec 1)))`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC OPEN_AFFINITY THEN ASM_SIMP_TAC[OPEN_INTERVAL; REAL_LT_IMP_NZ];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv lam % (lam % (y:real^N) + --(lam % inv(&2) % vec 1)) + inv(&2) % vec 1 = y`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; VECTOR_MUL_RNEG; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    VECTOR_ARITH_TAC;
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC]);;

(* The cut-off chart function and its forcing vanish off Lp. *)

let PDE_MT_CUT_SUPPORT = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) U0 (W:real^N->real^K) G
    (psi:real^N->real) Lp z.
     compact Lp /\ (!z. ~(z IN Lp) ==> psi z = &0) /\ ~(z IN Lp)
     ==> (if z IN U0 then psi z % W z else vec 0) = vec 0 /\
         (if z IN U0 then psi z % G z - pde_mt_comm A B (\z. lift(psi z)) W z
          else vec 0) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(psi:real^N->real) z = &0` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; COND_ID; VECTOR_SUB_LZERO] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VECTOR_NEG_EQ_0] THEN
  MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN EXISTS_TAC `(:real^N) DIFF Lp` THEN
  ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV; LIFT_NUM]);;

let PDE_MT_TRANS_EQ_CUBE = prove
 (`!a b' lam (aaT:real->real^N->real^N^N) (bbT:real->real^N->num->real^K^K) ccT
    (A:real->real^N->real^N^N) (B:real->real^N->num->real^K^K) C V U0
    (W:real->real^N->real^K) G (psi:real^N->real) Lp u GG s y.
     (!t z. a <= t /\ t < b' /\ z IN V
            ==> aaT (t - a) (inv lam % z + inv(&2) % vec 1) = inv(lam pow 2) %% A t z /\
                (!i. 1 <= i /\ i <= dimindex(:N)
                     ==> bbT (t - a) (inv lam % z + inv(&2) % vec 1) i = inv lam %% B t z i) /\
                ccT (t - a) (inv lam % z + inv(&2) % vec 1) = C t z) /\
     open U0 /\ (!t. a <= t /\ t < b' ==> smooth_map_on U0 (W t)) /\
     (!t z. a < t /\ t < b' /\ z IN U0
            ==> ((\s. W (drop s) z) has_vector_derivative
                 (pde_lop0 (A t) (B t) (C t) (W t) z + G t z)) (at (lift t))) /\
     &0 < lam /\ smooth_map_on (:real^N) (\z. lift(psi z)) /\
     compact Lp /\ Lp SUBSET V /\ Lp SUBSET U0 /\ Lp SUBSET ball(vec 0,lam / &4) /\
     (!z. ~(z IN Lp) ==> psi z = &0) /\
     (!r. u r = pdm_transplant lam (\z. if z IN U0 then psi z % W (r + a) z else vec 0)) /\
     (!r. GG r = pdm_transplant lam
                   (\z. if z IN U0
                        then psi z % G (r + a) z -
                             pde_mt_comm (A (r + a)) (B (r + a)) (\z. lift(psi z)) (W (r + a)) z
                        else vec 0)) /\
     &0 < s /\ s < b' - a /\ y IN interval[vec 0,vec 1]
     ==> ((\r. u (drop r) y) has_vector_derivative (pde_lop aaT bbT ccT u s y + GG s y))
         (at (lift s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "agr") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[PDE_LOP_LOP0] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `y IN interval(--(&1 / &4) % vec 1:real^N,(&1 + &1 / &4) % vec 1)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[PDE_MT_CUBE_IN_BOX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lam:real`; `y:real^N`] PDE_MT_DILATE_INV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `lam:real` PDE_MT_DILATE_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* support of the cut-off functions *)
  SUBGOAL_THEN
   `!r z. lam / &4 < norm z
          ==> (if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (r + a) z
               else vec 0) = vec 0 /\
              (if z IN U0
               then psi z % G (r + a) z -
                    pde_mt_comm ((A:real->real^N->real^N^N) (r + a))
                      ((B:real->real^N->num->real^K^K) (r + a)) (\z. lift(psi z)) (W (r + a)) z
               else vec 0) = vec 0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC PDE_MT_CUT_SUPPORT THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Lp:real^N->bool) SUBSET ball(vec 0,lam / &4)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_MESON_TAC[REAL_LT_ANTISYM];
    ALL_TAC] THEN
  (* transplants at points of the box *)
  SUBGOAL_THEN
   `!r x. x IN interval(--(&1 / &4) % vec 1:real^N,(&1 + &1 / &4) % vec 1)
          ==> pdm_transplant lam
                (\z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (r + a) z
                     else vec 0) x =
              (if lam % (x - inv(&2) % vec 1) IN U0
               then psi (lam % (x - inv(&2) % vec 1)) %
                    W (r + a) (lam % (x - inv(&2) % vec 1))
               else vec 0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) PDM_TRANSPLANT_EQ (lhand w))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pdm_transplant lam
      (\z. if z IN U0
           then (psi:real^N->real) z % (G:real->real^N->real^K) (s + a) z -
                pde_mt_comm ((A:real->real^N->real^N^N) (s + a))
                  ((B:real->real^N->num->real^K^K) (s + a)) (\z. lift(psi z))
                  ((W:real->real^N->real^K) (s + a)) z
           else vec 0) y =
    (if lam % (y - inv(&2) % vec 1) IN U0
     then psi (lam % (y - inv(&2) % vec 1)) % G (s + a) (lam % (y - inv(&2) % vec 1)) -
          pde_mt_comm (A (s + a)) (B (s + a)) (\z. lift(psi z)) (W (s + a))
                      (lam % (y - inv(&2) % vec 1))
     else vec 0)`
  SUBST1_TAC THENL
   [W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) PDM_TRANSPLANT_EQ (lhand w))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. pdm_transplant lam
           (\z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (drop r + a) z
                else vec 0) y) =
    (\r. if lam % (y - inv(&2) % vec 1) IN U0
         then psi (lam % (y - inv(&2) % vec 1)) % W (drop r + a) (lam % (y - inv(&2) % vec 1))
         else vec 0)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* smoothness of the cut-off function and of its transplant *)
  SUBGOAL_THEN
   `smooth_map_on (:real^N)
      (\z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (s + a) z
           else vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDM_ZERO_EXT_SMOOTH THEN EXISTS_TAC `Lp:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U0:real^N->bool`; `\z. lift((psi:real^N->real) z)`;
                     `(W:real->real^N->real^K) (s + a)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N)
      (pdm_transplant lam
        (\z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (s + a) z
             else vec 0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDM_TRANSPLANT_SMOOTH THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* the operator: dilation, then locality *)
  MP_TAC(ISPECL [`lam:real`; `aaT:real->real^N->real^N^N`; `bbT:real->real^N->num->real^K^K`;
                 `ccT:real->real^N->real^K^K`;
                 `\r:real. pdm_transplant lam
                     (\z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (s + a) z
                          else vec 0)`;
                 `s:real`;
                 `\z:real^N. lam pow 2 %% (aaT:real->real^N->real^N^N) s (inv lam % z + inv(&2) % vec 1)`;
                 `\(z:real^N) (i:num). lam %%
                     (bbT:real->real^N->num->real^K^K) s (inv lam % z + inv(&2) % vec 1) i`;
                 `\z:real^N. (ccT:real->real^N->real^K^K) s (inv lam % z + inv(&2) % vec 1)`;
                 `lam % (y - inv(&2) % vec 1):real^N`] PDE_MT_LOP_DILATE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_POW_NZ; REAL_LT_IMP_NZ; MATRIX_CMUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[PDE_LOP_LOP0] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `lam % (y - inv(&2) % vec 1) IN
    IMAGE (\x:real^N. lam % x + --(lam % inv(&2) % vec 1))
          (interval(--(&1 / &4) % vec 1,(&1 + &1 / &4) % vec 1))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `z0:real^N = lam % (y - inv(&2) % vec 1)` THEN
  ABBREV_TAC `Z = IMAGE (\x:real^N. lam % x + --(lam % inv(&2) % vec 1))
                        (interval(--(&1 / &4) % vec 1,(&1 + &1 / &4) % vec 1))` THEN
  (* locality on Z: the dilated transplant is the cut-off chart function *)
  MP_TAC(ISPECL
   [`Z:real^N->bool`;
    `\z:real^N. lam pow 2 %% (aaT:real->real^N->real^N^N) s (inv lam % z + inv(&2) % vec 1)`;
    `\(z:real^N) (i:num). lam %%
        (bbT:real->real^N->num->real^K^K) s (inv lam % z + inv(&2) % vec 1) i`;
    `\z:real^N. (ccT:real->real^N->real^K^K) s (inv lam % z + inv(&2) % vec 1)`;
    `\z. pdm_transplant lam
           (\z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (s + a) z
                else vec 0) (inv lam % z + inv(&2) % vec 1)`;
    `\z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (s + a) z
         else vec 0`;
    `z0:real^N`] PDE_MT_LOP0_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `inv lam % z + inv(&2) % vec 1 IN
      interval(--(&1 / &4) % vec 1:real^N,(&1 + &1 / &4) % vec 1)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`lam:real`; `z:real^N`] PDE_MT_DILATE_INV) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `(z0:real^N) IN Lp` THENL
   [ALL_TAC;
    (* off the support *)
    SUBGOAL_THEN
     `(if z0 IN U0
       then (psi:real^N->real) z0 % (G:real->real^N->real^K) (s + a) z0 -
            pde_mt_comm ((A:real->real^N->real^N^N) (s + a))
              ((B:real->real^N->num->real^K^K) (s + a)) (\z. lift(psi z))
              ((W:real->real^N->real^K) (s + a)) z0
       else vec 0) = vec 0`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`(A:real->real^N->real^N^N) (s + a)`;
                     `(B:real->real^N->num->real^K^K) (s + a)`; `U0:real^N->bool`;
                     `(W:real->real^N->real^K) (s + a)`; `(G:real->real^N->real^K) (s + a)`;
                     `psi:real^N->real`; `Lp:real^N->bool`; `z0:real^N`] PDE_MT_CUT_SUPPORT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(psi:real^N->real) z0 = &0` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `pde_lop0 (\z. lam pow 2 %% (aaT:real->real^N->real^N^N) s (inv lam % z + inv(&2) % vec 1))
        (\(z:real^N) (i:num). lam %%
           (bbT:real->real^N->num->real^K^K) s (inv lam % z + inv(&2) % vec 1) i)
        (\z. (ccT:real->real^N->real^K^K) s (inv lam % z + inv(&2) % vec 1))
        (\z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (s + a) z
             else vec 0) z0 = vec 0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC PDE_MT_LOP0_ZERO_OPEN THEN EXISTS_TAC `(:real^N) DIFF Lp` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO; COND_ID];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; COND_ID; VECTOR_ADD_LID] THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST]] THEN
  (* on the support *)
  SUBGOAL_THEN `(z0:real^N) IN U0 /\ z0 IN V` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "agr" (MP_TAC o SPECL [`s + a:real`; `z0:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ARITH `(s + a) - a:real = s`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\z:real^N. lam pow 2 %% (aaT:real->real^N->real^N^N) s (inv lam % z + inv(&2) % vec 1)`;
    `\(z:real^N) (i:num). lam %%
        (bbT:real->real^N->num->real^K^K) s (inv lam % z + inv(&2) % vec 1) i`;
    `\z:real^N. (ccT:real->real^N->real^K^K) s (inv lam % z + inv(&2) % vec 1)`;
    `(A:real->real^N->real^N^N) (s + a)`; `(B:real->real^N->num->real^K^K) (s + a)`;
    `(C:real->real^N->real^K^K) (s + a)`;
    `\z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (s + a) z
         else vec 0`;
    `z0:real^N`] PDE_MT_LOP0_COEFF_AT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MATRIX_CMUL_ASSOC; REAL_MUL_RINV; REAL_POW_NZ; REAL_LT_IMP_NZ;
                 MATRIX_CMUL_LID];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL
   [`U0:real^N->bool`; `(A:real->real^N->real^N^N) (s + a)`;
    `(B:real->real^N->num->real^K^K) (s + a)`; `(C:real->real^N->real^K^K) (s + a)`;
    `\z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (s + a) z
         else vec 0`;
    `\z. drop(lift((psi:real^N->real) z)) % (W:real->real^N->real^K) (s + a) z`;
    `z0:real^N`] PDE_MT_LOP0_LOCAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LIFT_DROP]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U0:real^N->bool`; `(A:real->real^N->real^N^N) (s + a)`;
                 `(B:real->real^N->num->real^K^K) (s + a)`; `(C:real->real^N->real^K^K) (s + a)`;
                 `\z. lift((psi:real^N->real) z)`; `(W:real->real^N->real^K) (s + a)`;
                 `z0:real^N`] PDE_MT_LOP0_CUTOFF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC] THEN
  (* the time derivative *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`s + a:real`; `z0:real^N`] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`\r. (W:real->real^N->real^K) r z0`;
                 `pde_lop0 ((A:real->real^N->real^N^N) (s + a))
                    ((B:real->real^N->num->real^K^K) (s + a)) (C (s + a))
                    ((W:real->real^N->real^K) (s + a)) z0 + G (s + a) z0`;
                 `--a:real`; `s:real`] PDE_MT_HVD_SHIFT) THEN
  ASM_REWRITE_TAC[REAL_SUB_RNEG] THEN
  DISCH_THEN(MP_TAC o SPEC `(psi:real^N->real) z0` o MATCH_MP HAS_VECTOR_DERIVATIVE_CMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  VECTOR_ARITH_TAC);;

let PDE_MT_TRANS_TSOL = prove
 (`!a b' lam lamT (aaT:real->real^N->real^N^N) (bbT:real->real^N->num->real^K^K) ccT
    (A:real->real^N->real^N^N) (B:real->real^N->num->real^K^K) C V U0
    (W:real->real^N->real^K) G (psi:real^N->real) Lp u GG.
     (!t z. a <= t /\ t < b' /\ z IN V
            ==> aaT (t - a) (inv lam % z + inv(&2) % vec 1) = inv(lam pow 2) %% A t z /\
                (!i. 1 <= i /\ i <= dimindex(:N)
                     ==> bbT (t - a) (inv lam % z + inv(&2) % vec 1) i = inv lam %% B t z i) /\
                ccT (t - a) (inv lam % z + inv(&2) % vec 1) = C t z) /\
     pde_tcoeff (b' - a) lamT aaT bbT ccT /\
     open U0 /\ pde_upto a b' U0 W /\
     (!t z. a < t /\ t < b' /\ z IN U0
            ==> ((\s. W (drop s) z) has_vector_derivative
                 (pde_lop0 (A t) (B t) (C t) (W t) z + G t z)) (at (lift t))) /\
     &0 < lam /\ smooth_map_on (:real^N) (\z. lift(psi z)) /\
     compact Lp /\ Lp SUBSET V /\ Lp SUBSET U0 /\ Lp SUBSET ball(vec 0,lam / &4) /\
     (!z. ~(z IN Lp) ==> psi z = &0) /\
     (!r. u r = pdm_transplant lam (\z. if z IN U0 then psi z % W (r + a) z else vec 0)) /\
     (!r. GG r = pdm_transplant lam
                   (\z. if z IN U0
                        then psi z % G (r + a) z -
                             pde_mt_comm (A (r + a)) (B (r + a)) (\z. lift(psi z)) (W (r + a)) z
                        else vec 0))
     ==> pde_tsol (b' - a) aaT bbT ccT GG (u (&0)) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_upto (&0) (b' - a) U0 (\s. (W:real->real^N->real^K) (s + a))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real`; `b':real`; `U0:real^N->bool`; `W:real->real^N->real^K`;
                   `a:real`] PDE_MT_UPTO_SHIFT) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < b' ==> smooth_map_on U0 ((W:real->real^N->real^K) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real`; `b':real`; `U0:real^N->bool`; `W:real->real^N->real^K`;
                   `t:real`] PDE_ML_UPTO_SLICE_OPEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&0`; `b' - a:real`; `lam:real`;
                 `\t z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (t + a) z
                        else vec 0`;
                 `Lp:real^N->bool`] PDM_TRANSPLANT_UPTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`&0`; `b' - a:real`; `U0:real^N->bool`;
                     `\s. (W:real->real^N->real^K) (s + a)`; `psi:real^N->real`;
                     `Lp:real^N->bool`] PDM_UPTO_CUTOFF_EXT) THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO; COND_ID]];
    REWRITE_TAC[] THEN STRIP_TAC] THEN
  REWRITE_TAC[pde_tsol] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `u = \t. pdm_transplant lam
                (\z. if z IN U0 then (psi:real^N->real) z % (W:real->real^N->real^K) (t + a) z
                     else vec 0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[PDM_TRANSPLANT_ZPER]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `x:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`aaT:real->real^N->real^N^N`; `bbT:real->real^N->num->real^K^K`;
                 `ccT:real->real^N->real^K^K`; `u:real->real^N->real^K`;
                 `(GG:real->real^N->real^K) s`; `s:real`] PDE_MT_ZPER_EQ_REDUCE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[pde_tcoeff]) THEN ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[pde_tcoeff]) THEN ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[pde_tcoeff]) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[PDM_TRANSPLANT_ZPER];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`b' - a:real`;
                     `\t. pdm_transplant lam
                            (\z. if z IN U0
                                 then (psi:real^N->real) z % (W:real->real^N->real^K) (t + a) z
                                 else vec 0)`; `s:real`] PDE_UPTO_SLICE_SMOOTH) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[PDM_TRANSPLANT_ZPER];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC PDE_MT_TRANS_EQ_CUBE THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b':real`; `lam:real`;
                            `A:real->real^N->real^N^N`; `B:real->real^N->num->real^K^K`;
                            `C:real->real^N->real^K^K`; `V:real^N->bool`; `U0:real^N->bool`;
                            `W:real->real^N->real^K`; `G:real->real^N->real^K`;
                            `psi:real^N->real`; `Lp:real^N->bool`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN REWRITE_TAC[]]);;

(* ========================================================================= *)
(* pde_upto on an open set U with initial time a is closed under bilinear    *)
(* maps, sums, finite sums and spatial partial derivatives, and contains     *)
(* time-independent smooth maps; hence the commutator pde_mt_comm of         *)
(* pde_upto coefficients and a pde_upto map is pde_upto.                     *)
(* ========================================================================= *)

let PDE_MT_UPTO_BILINEAR_OPEN = prove
 (`!a b (U:real^N->bool) (bb:real^P->real^Q->real^K) (f:real->real^N->real^P) g.
     open U /\ bilinear bb /\ pde_upto a b U f /\ pde_upto a b U g
     ==> pde_upto a b U (\t x. bb (f t x) (g t x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `F1:real^(1,N)finite_sum->real^P`
      STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `e2:real` (X_CHOOSE_THEN `F2:real^(1,N)finite_sum->real^Q`
      STRIP_ASSUME_TAC))))) THEN
  EXISTS_TAC `min e1 e2` THEN
  EXISTS_TAC `\z. (bb:real^P->real^Q->real^K) ((F1:real^(1,N)finite_sum->real^P) z)
                                              ((F2:real^(1,N)finite_sum->real^Q) z)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN];
    MATCH_MP_TAC SMOOTH_MAP_ON_BILINEAR_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `interval(lift(a - e1),lift b) PCROSS (U:real^N->bool)`;
      EXISTS_TAC `interval(lift(a - e2),lift b) PCROSS (U:real^N->bool)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN BINOP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let PDE_MT_UPTO_ADD_OPEN = prove
 (`!a b (U:real^N->bool) (f:real->real^N->real^K) g.
     open U /\ pde_upto a b U f /\ pde_upto a b U g
     ==> pde_upto a b U (\t x. f t x + g t x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `F1:real^(1,N)finite_sum->real^K`
      STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `e2:real` (X_CHOOSE_THEN `F2:real^(1,N)finite_sum->real^K`
      STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `min e1 e2` THEN
  EXISTS_TAC `\z. (F1:real^(1,N)finite_sum->real^K) z + (F2:real^(1,N)finite_sum->real^K) z` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `interval(lift(a - e1),lift b) PCROSS (U:real^N->bool)`;
      EXISTS_TAC `interval(lift(a - e2),lift b) PCROSS (U:real^N->bool)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN BINOP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let PDE_MT_UPTO_CONST_OPEN = prove
 (`!a b (U:real^N->bool) (c:real^K). pde_upto a b U (\t x. c)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PDE_MT_UPTO_OPEN_SUBSET THEN
  EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[PDE_UPTO_CONST; SUBSET_UNIV]);;

let PDE_MT_UPTO_VSUM_OPEN = prove
 (`!a b (U:real^N->bool) (f:num->real->real^N->real^K) n.
     open U /\ (!i. 1 <= i /\ i <= n ==> pde_upto a b U (f i))
     ==> pde_upto a b U (\t x. vsum(1..n) (\i. f i t x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_EQ; PDE_MT_UPTO_CONST_OPEN]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  MATCH_MP_TAC PDE_MT_UPTO_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let PDE_MT_UPTO_PARTIAL_OPEN = prove
 (`!a b (U:real^N->bool) (W:real->real^N->real^K) i.
     open U /\ pde_upto a b U W /\ 1 <= i /\ i <= dimindex(:N)
     ==> pde_upto a b U (\t x. partial_derivative i (W t) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FW:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:real`;
                        `partial_derivative (1 + i) (FW:real^(1,N)finite_sum->real^K)`] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_PCROSS; OPEN_INTERVAL] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `partial_derivative i ((W:real->real^N->real^K) t) y =
    partial_derivative i (\y. (FW:real^(1,N)finite_sum->real^K) (pastecart (lift t) y)) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDE_ST_SLICE_PARTIAL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  ASM_REAL_ARITH_TAC);;

let PDE_MT_UPTO_TIME_CONST = prove
 (`!a b (U:real^N->bool) (q:real^N->real^K).
     open U /\ smooth_map_on U q ==> pde_upto a b U (\t x. q x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_upto] THEN
  MAP_EVERY EXISTS_TAC [`&1`; `\z:real^(1,N)finite_sum. (q:real^N->real^K) (sndcart z)`] THEN
  REWRITE_TAC[REAL_LT_01; SNDCART_PASTECART] THEN
  SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (q:real^N->real^K) (sndcart z)) =
                q o (sndcart o (\z. z))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SMOOTH_MAP_ON_SNDCART_OPEN; SMOOTH_MAP_ON_ID] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
  MESON_TAC[]);;

let PDE_MT_UPTO_SCALAR_MUL_OPEN = prove
 (`!a b (U:real^N->bool) (c:real->real^N->real) (g:real->real^N->real^K).
     open U /\ pde_upto a b U (\t z. lift(c t z)) /\ pde_upto a b U g
     ==> pde_upto a b U (\t z. c t z % g t z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`; `\x y:real^K. drop x % y`;
                 `\t z. lift((c:real->real^N->real) t z)`; `g:real->real^N->real^K`]
                PDE_MT_UPTO_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP]);;

let PDE_MT_COMM_UPTO = prove
 (`!a b (U:real^N->bool) (A:real->real^N->real^N^N) (B:real->real^N->num->real^K^K)
    (p:real^N->real^1) (W:real->real^N->real^K).
     open U /\
     pde_upto a b U (\t z. (vectorize:real^N^N->real^(N,N)finite_prod) (A t z)) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> pde_upto a b U (\t z. (vectorize:real^K^K->real^(K,K)finite_prod) (B t z i))) /\
     smooth_map_on U p /\ pde_upto a b U W
     ==> pde_upto a b U (\t z. pde_mt_comm (A t) (B t) p (W t) z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mt_comm] THEN
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
   `!i. pde_upto a b U (\t z. lift(drop(partial_derivative i (p:real^N->real^1) z))) /\
        !j. pde_upto a b U
              (\t z. lift(drop(partial_derivative i (partial_derivative j p) z)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THEN TRY GEN_TAC THEN
    MATCH_MP_TAC PDE_MT_UPTO_TIME_CONST THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> pde_upto a b U (\t z. partial_derivative i ((W:real->real^N->real^K) t) z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_MT_UPTO_PARTIAL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_MT_UPTO_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC PDE_MT_UPTO_VSUM_OPEN THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THENL
   [MATCH_MP_TAC PDE_MT_UPTO_VSUM_OPEN THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_MT_UPTO_SCALAR_MUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC PDE_MT_UPTO_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC) THEN
    MATCH_MP_TAC PDE_MT_UPTO_SCALAR_MUL_OPEN THEN ASM_SIMP_TAC[ETA_AX];
    MATCH_MP_TAC PDE_MT_UPTO_SCALAR_MUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                   `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `\t z. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((B:real->real^N->num->real^K^K) t z i)`;
                   `W:real->real^N->real^K`] PDE_MT_UPTO_BILINEAR_OPEN) THEN
    ASM_SIMP_TAC[MATRIFY_VECTORIZE; INST_TYPE [`:K`,`:N`] LRG_BILINEAR_MATRIFY_MUL; ETA_AX]]);;

