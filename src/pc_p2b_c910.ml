(* ========================================================================= *)
(* Unit pc_p2b_c910 (Part 2B): MT Cor 9.10 in integrated form for            *)
(* kappa-solutions, the route P2B_COR_9_10_ROUTE_STATEMENT of pc_p2b_w920g   *)
(* (theorem P2B_COR_9_10_ROUTE) from W3 (pc_p2b_w3iface), FL8 and FL2        *)
(* (pc_p2a_fldefs).                                                          *)
(*                                                                           *)
(* First: nonnegative sectional curvature gives nonnegative scalar           *)
(* curvature; p2a_cbflow gives Riemannian slices; the reduced length is      *)
(* nonnegative (FL2: a minimizer exists, its L-integrand is nonnegative).    *)
(* ========================================================================= *)

needs "src/pc_p2b_c914.ml";;
needs "src/pc_p2b_fchart.ml";;
needs "src/pc_p2b_scalpos.ml";;

prioritize_real();;
type_invention_error := true;;

(* The frame term of P2B_FRAME_TERM (pc_p2b_scalpos) for nonnegative        *)
(* sectional curvature: adapted from that proof (same steps, weak           *)
(* inequalities).                                                            *)

let P2BX_FRAME_TERM_NONNEG = prove
 (`!U (G:real^N->real^N^N) y (M:real^N^N) i j.
     metric_field U G /\ y IN U /\ G y = transp M ** M /\ invertible M /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> &0 <= (matrix_inv M ** basis i) dot
               (G y ** lriemann G y (matrix_inv M ** basis i)
                                    (matrix_inv M ** basis j) (matrix_inv M ** basis j))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sect") STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `fi = matrix_inv(M:real^N^N) ** basis i` THEN
  ABBREV_TAC `fj = matrix_inv(M:real^N^N) ** basis j` THEN
  SUBGOAL_THEN `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1 /\
                (fj:real^N) dot (G y ** fj) = &1 /\
                (fi:real^N) dot (G y ** fj) = (if (i:num) = j then &1 else &0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["fi"; "fj"] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `i:num`]
                    P2B_FRAME_ORTHO);
      MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `j:num`; `j:num`]
                    P2B_FRAME_ORTHO);
      MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `j:num`]
                    P2B_FRAME_ORTHO)] THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(G:real^N->real^N^N) y = transp(M:real^N^N) ** M` THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `i:num = j` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(fi:real^N) = fj` SUBST_ALL_TAC THENL
     [MAP_EVERY EXPAND_TAC ["fi"; "fj"] THEN REFL_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `fj:real^N`;
                   `fj:real^N`; `fj:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(x:real^N) = --x <=> x = vec 0`] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fj) =
               (if (i:num) = j then &1 else &0)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~collinear {vec 0,fi:real^N,fj}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_LEMMA] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(fj:real^N) dot ((G:real^N->real^N^N) y ** fj) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fj) = &0` THEN
      UNDISCH_TAC `(fj:real^N) dot ((G:real^N->real^N^N) y ** fj) = &1` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `c * c = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "sect" (fun th -> MP_TAC(MATCH_MP (SPECL [`fi:real^N`; `fj:real^N`] th)
                                        (ASSUME `~collinear {vec 0,fi:real^N,fj}`))) THEN
  REWRITE_TAC[lsectional] THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_DIV_1]);;

let P2BX_LSCALAR_NONNEG = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> &0 <= lscalar G y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`]
                P2B_LSCALAR_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`;
                 `matrix_inv(M:real^N^N) ** basis j`] P2B_LRICCI_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC P2BX_FRAME_TERM_NONNEG THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P2BX_MFD_SCALAR_NONNEG = prove
 (`!top atlas (g:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v)
     ==> &0 <= mfd_scalar atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_scalar] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC P2BX_LSCALAR_NONNEG THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN
  ASM_REWRITE_TAC[mfd_sectional]);;

(* Slices of a p2a_cbflow are Riemannian metrics of a smooth atlas. *)

let P2BX_CBFLOW_SLICE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) t.
     p2a_cbflow (top,atlas) a b g /\ a <= t /\ t <= b
     ==> smooth_manifold_atlas top atlas /\ riemannian_metric atlas (g t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_cbflow; ricci_flow_from; p2a_flow_upto] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real = a` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real = b` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `ricci_flow_on (top:A topology,atlas) a b (g:real->A->real^N^N)` THEN
  REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* The reduced length of a kappa-solution is nonnegative (FL2 gives a       *)
(* minimizer; its L-integrand is nonnegative since R >= 0).                  *)

let P2BX_KLX_NONNEG = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p t q.
     P2A_FLOW_MIN_EXISTS_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\
     &0 < t /\ q IN topspace top
     ==> &0 <= p2b_klx (top,atlas) g p t q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL2") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `connected_space (top:B topology)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_cbflow (top,atlas) (--(&2 * t)) (&0) (g:real->B->real^3^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_KSOL_CBFLOW THEN EXISTS_TAC `kappa:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "FL2" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                  `--(&2 * t)`; `&0`; `g:real->B->real^3^3`; `p:B`; `q:B`;
                                  `t:real`] o
                  REWRITE_RULE[P2A_FLOW_MIN_EXISTS_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->B` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[p2b_klx; p2a_lx] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP P2A_MIN_LX) THEN
  MATCH_MP_TAC REAL_LE_DIV THEN
  SIMP_TAC[REAL_LE_MUL; REAL_POS; SQRT_POS_LE; ASSUME `&0 < t`; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[p2a_L_length] THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
  UNDISCH_TAC `p2a_min (p2a_flow_view (top,atlas) (real_interval[--(&2 * t),&0])
                          (g:real->B->real^3^3)) (&0) p t gamma` THEN
  REWRITE_TAC[p2a_min; p2a_adm] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_L_integrand; P2BX_VIEW_PROJ] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `--(&2 * t)`; `&0`; `g:real->B->real^3^3`; `&0 - s`] P2BX_CBFLOW_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC P2BX_MFD_SCALAR_NONNEG THEN EXISTS_TAC `top:B topology` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check
      (fun th -> can (find_term ((=) `topspace:(B)topology->B->bool`)) (concl th) &&
                 is_forall(concl th))) THEN
    ASM_REWRITE_TAC[P2BX_VIEW_PROJ; IN_REAL_INTERVAL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
    DISCH_THEN(MATCH_MP_TAC o el 3 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check
      (fun th -> can (find_term ((=) `topspace:(B)topology->B->bool`)) (concl th) &&
                 is_forall(concl th))) THEN
    ASM_REWRITE_TAC[P2BX_VIEW_PROJ; IN_REAL_INTERVAL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Generic real analysis.  An inequality between continuous functions off a  *)
(* null set holds everywhere; the difference bound along a segment for a     *)
(* locally Lipschitz function from an almost-everywhere bound on its         *)
(* directional derivative (Fubini on parallel lines,                         *)
(* FUBINI_NEGLIGIBLE_OFFSET, and the fundamental theorem of calculus for     *)
(* absolutely continuous functions on good lines).                           *)
(* ========================================================================= *)

let P2BX_AE_LE_CONT = prove
 (`!(s:real^M->bool) f h n.
     open s /\ (\z. lift(f z)) continuous_on s /\ (\z. lift(h z)) continuous_on s /\
     negligible n /\ (!z. z IN s /\ ~(z IN n) ==> f z <= h z)
     ==> !z. z IN s ==> f z <= h z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z0:real^M` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\z. lift((f:real^M->real) z) - lift(h z)) continuous at z0` MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_SUB THEN
    UNDISCH_TAC `(\z. lift((f:real^M->real) z)) continuous_on s` THEN
    UNDISCH_TAC `(\z. lift((h:real^M->real) z)) continuous_on s` THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at; DIST_LIFT; GSYM LIFT_SUB] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^M->real) z0 - h z0`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open(s:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z0:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `ball(z0:real^M,min d1 d2)` OPEN_NOT_NEGLIGIBLE) THEN
  REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE; REAL_LT_MIN] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `n:real^M->bool` THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL; REAL_LT_MIN] THEN X_GEN_TAC `z:real^M` THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `(z:real^M) IN n` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:real^M) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(z0:real^M,d2) SUBSET s` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real) z <= h z` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* A compact subset of an open set has a uniform closed thickening in it. *)

let P2BX_THICKEN = prove
 (`!(k:real^M->bool) s.
     compact k /\ open s /\ k SUBSET s
     ==> ?d. &0 < d /\ !y z. y IN k /\ norm(z - y) <= d ==> z IN s`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s = (:real^M)` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[IN_UNIV; REAL_LT_01]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^M->bool`; `(:real^M) DIFF s`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^M`; `z:real^M`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(z:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^M`; `z:real^M`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; dist] THEN
  UNDISCH_TAC `norm(z - y:real^M) <= d / &2` THEN UNDISCH_TAC `&0 < d` THEN
  NORM_ARITH_TAC);;

(* One good line: the function restricted to t -> y + t v is Lipschitz,     *)
(* hence absolutely continuous, and its derivative is bounded by C off a     *)
(* null set of parameters.                                                   *)

let P2BX_LINE_GOOD = prove
 (`!(f:real^M->real) n C v y L.
     (!t. &0 <= t /\ t <= &1 /\ ~(y + t % v IN n)
          ==> (\w. lift(f w)) differentiable (at (y + t % v)) /\
              drop(frechet_derivative (\w. lift(f w)) (at (y + t % v)) v) <= C) /\
     (!t1 t2. &0 <= t1 /\ t1 <= &1 /\ &0 <= t2 /\ t2 <= &1
              ==> abs(f(y + t1 % v) - f(y + t2 % v)) <= L * abs(t1 - t2)) /\
     negligible {t:real^1 | y + drop t % v IN n}
     ==> f(y + v) - f y <= C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "D") (CONJUNCTS_THEN2 (LABEL_TAC "L") ASSUME_TAC)) THEN
  ABBREV_TAC `phi = \t:real^1. lift((f:real^M->real)(y + drop t % v))` THEN
  ABBREV_TAC `ff = \t:real^1. if y + drop t % v IN n then lift C
                              else frechet_derivative (\w. lift((f:real^M->real) w))
                                     (at (y + drop t % v)) v` THEN
  MP_TAC(ISPECL [`phi:real^1->real^1`; `ff:real^1->real^1`;
                 `{t:real^1 | (y:real^M) + drop t % (v:real^M) IN (n:real^M->bool)}`;
                 `vec 0:real^1`; `vec 1:real^1`]
         FUNDAMENTAL_THEOREM_OF_CALCULUS_ABSOLUTELY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DROP_VEC; REAL_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIPSCHITZ_IMP_ABSOLUTELY_CONTINUOUS THEN
      EXISTS_TAC `L:real` THEN REWRITE_TAC[BOUNDED_INTERVAL] THEN
      EXPAND_TAC "phi" THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; GSYM LIFT_SUB; NORM_LIFT; NORM_1; DROP_SUB;
                  LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN USE_THEN "L" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
    STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    EXPAND_TAC "ff" THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "D" (MP_TAC o SPEC `drop t`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[FRECHET_DERIVATIVE_WORKS] o CONJUNCT1) THEN
    ABBREV_TAC `D = frechet_derivative (\w. lift((f:real^M->real) w)) (at (y + drop t % v))` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `linear(D:real^M->real^1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
    SUBGOAL_THEN `((\t:real^1. (y:real^M) + drop t % (v:real^M)) has_derivative
                   (\h. vec 0 + drop h % v)) (at t)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MP_TAC(ISPECL [`\x:real^1. x`; `v:real^M`] LINEAR_VMUL_DROP) THEN
      REWRITE_TAC[LINEAR_ID];
      ALL_TAC] THEN
    REWRITE_TAC[has_vector_derivative] THEN EXPAND_TAC "phi" THEN
    SUBGOAL_THEN `(\x:real^1. drop x % (D:real^M->real^1) v) =
                  D o (\h. vec 0 + drop h % (v:real^M))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTOR_ADD_LID] THEN ASM_SIMP_TAC[LINEAR_CMUL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\t:real^1. lift((f:real^M->real)(y + drop t % v))) =
                  (\w. lift(f w)) o (\t. (y:real^M) + drop t % (v:real^M))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`ff:real^1->real^1`; `(\t:real^1. lift C)`; `interval[vec 0:real^1,vec 1]`;
                 `(phi:real^1->real^1) (vec 1) - phi (vec 0)`;
                 `content(interval[vec 0:real^1,vec 1]) % lift C`] HAS_INTEGRAL_DROP_LE) THEN
  ASM_REWRITE_TAC[HAS_INTEGRAL_CONST] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN EXPAND_TAC "ff" THEN
    COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN
    UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    USE_THEN "D" (MP_TAC o SPEC `drop t`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  EXPAND_TAC "phi" THEN
  REWRITE_TAC[CONTENT_UNIT_1; VECTOR_MUL_LID; DROP_VEC; LIFT_DROP; DROP_SUB] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_RID]);;

(* The difference bound along a segment in an open set: almost every line  *)
(* parallel to v is good (FUBINI_NEGLIGIBLE_OFFSET), good base points y     *)
(* exist arbitrarily close to x, and f is Lipschitz on a compact thickening *)
(* of the segment.                                                           *)

let P2BX_LINE_BOUND = prove
 (`!(s:real^M->bool) f n C v x.
     open s /\ wan_loclip s f /\ negligible n /\
     (!t. &0 <= t /\ t <= &1 ==> x + t % v IN s) /\
     (!z. z IN s /\ ~(z IN n)
          ==> (\w. lift(f w)) differentiable (at z) /\
              drop(frechet_derivative (\w. lift(f w)) (at z) v) <= C)
     ==> f(x + v) - f x <= C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lip")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "seg") (LABEL_TAC "der"))))) THEN
  ABBREV_TAC `k = IMAGE (\t:real^1. (x:real^M) + drop t % v) (interval[vec 0,vec 1])` THEN
  SUBGOAL_THEN `compact(k:real^M->bool) /\ k SUBSET s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
      REPEAT STRIP_TAC THEN USE_THEN "seg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^M->bool`; `s:real^M->bool`] P2BX_THICKEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `kk = {y + u:real^M | y IN k /\ u IN cball(vec 0,d)}` THEN
  SUBGOAL_THEN `compact(kk:real^M->bool) /\ kk SUBSET s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL_0] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `y:real^M` THEN ASM_REWRITE_TAC[VECTOR_ADD_SUB]];
    ALL_TAC] THEN
  USE_THEN "lip" (MP_TAC o SPEC `kk:real^M->bool` o REWRITE_RULE[wan_loclip]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `L0:real`) THEN
  ABBREV_TAC `L = abs L0` THEN
  SUBGOAL_THEN `!y z:real^M. y IN kk /\ z IN kk ==> abs(f y - f z) <= L * norm(y - z)`
  (LABEL_TAC "LK") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L0 * norm(y - z:real^M)` THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z u:real^M t. z = x + u + t % v /\ norm u <= d /\ &0 <= t /\ t <= &1
                               ==> z IN kk`
  (LABEL_TAC "INK") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "kk" THEN REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN
    MAP_EVERY EXISTS_TAC [`x + t % v:real^M`; `u:real^M`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "k" THEN REWRITE_TAC[IN_IMAGE; IN_INTERVAL_1] THEN
      EXISTS_TAC `lift t` THEN ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC];
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `negligible {y:real^M | ~negligible {t:real^1 | y + drop t % v IN n}}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:real^M->bool`; `v:real^M`] FUBINI_NEGLIGIBLE_OFFSET) THEN
    ASM_SIMP_TAC[NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e /\ e <= d
        ==> ?y:real^M. norm(y - x) < e /\ negligible {t:real^1 | y + drop t % v IN n}`
  (LABEL_TAC "GOOD") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `ball(x:real^M,e)` OPEN_NOT_NEGLIGIBLE) THEN
    ASM_REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{y:real^M | ~negligible {t:real^1 | y + drop t % v IN n}}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^M`) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `ee = ((f:real^M->real)(x + v) - f x) - C` THEN
  SUBGOAL_THEN `&0 < ee` ASSUME_TAC THENL [EXPAND_TAC "ee" THEN ASM_REAL_ARITH_TAC;
                                          ALL_TAC] THEN
  USE_THEN "GOOD" (MP_TAC o SPEC `min d (ee / (&4 * (L + &1)))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "L" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^M->real)(y + v) - f y <= C` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LINE_GOOD THEN
    MAP_EVERY EXISTS_TAC [`n:real^M->bool`; `L * norm(v:real^M)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "der" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `y + t % v IN (kk:real^M->bool)` MP_TAC THENL
       [USE_THEN "INK" MATCH_MP_TAC THEN EXISTS_TAC `y - x:real^M` THEN
        EXISTS_TAC `t:real` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `norm(y - x:real^M) < min d (ee / (&4 * (L + &1)))` THEN
        REAL_ARITH_TAC;
        ASM SET_TAC[]];
      MAP_EVERY X_GEN_TAC [`t1:real`; `t2:real`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `L * norm((y + t1 % v) - (y + t2 % v):real^M)` THEN CONJ_TAC THENL
       [USE_THEN "LK" MATCH_MP_TAC THEN CONJ_TAC THEN USE_THEN "INK" MATCH_MP_TAC THEN
        EXISTS_TAC `y - x:real^M` THENL
         [EXISTS_TAC `t1:real`; EXISTS_TAC `t2:real`] THEN ASM_REWRITE_TAC[] THEN
        (CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC]) THEN
        UNDISCH_TAC `norm(y - x:real^M) < min d (ee / (&4 * (L + &1)))` THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[VECTOR_ARITH `(y + a % v) - (y + b % v):real^N = (a - b) % v`] THEN
        REWRITE_TAC[NORM_MUL] THEN
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((f:real^M->real) y - f x) <= L * norm(y - x) /\
                abs(f(y + v) - f(x + v)) <= L * norm((y + v) - (x + v))`
  MP_TAC THENL
   [CONJ_TAC THEN USE_THEN "LK" MATCH_MP_TAC THEN CONJ_TAC THEN
    USE_THEN "INK" MATCH_MP_TAC THENL
     [EXISTS_TAC `y - x:real^M` THEN EXISTS_TAC `&0`;
      EXISTS_TAC `vec 0:real^M` THEN EXISTS_TAC `&0`;
      EXISTS_TAC `y - x:real^M` THEN EXISTS_TAC `&1`;
      EXISTS_TAC `vec 0:real^M` THEN EXISTS_TAC `&1`] THEN
    REWRITE_TAC[NORM_0; REAL_POS; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REPEAT CONJ_TAC THEN TRY VECTOR_ARITH_TAC THEN
    UNDISCH_TAC `norm(y - x:real^M) < min d (ee / (&4 * (L + &1)))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `(y + v) - (x + v):real^N = y - x`] THEN
  SUBGOAL_THEN `L * norm(y - x:real^M) <= ee / &4` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(L + &1) * (ee / (&4 * (L + &1)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      EXPAND_TAC "L" THEN
      UNDISCH_TAC `norm(y - x:real^M) < min d (ee / (&4 * (L + &1)))` THEN
      EXPAND_TAC "L" THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < L + &1` MP_TAC THENL [EXPAND_TAC "L" THEN REAL_ARITH_TAC;
                                              ALL_TAC] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < L + &1` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  UNDISCH_TAC `(f:real^M->real)(y + v) - f y <= C` THEN
  UNDISCH_TAC `(f:real^M->real)(x + v) - f x - C = ee` THEN
  UNDISCH_TAC `&0 < ee` THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The gradient norm lgrad2 bounds every directional derivative              *)
(* (Cauchy-Schwarz in the metric), and the transfer of FL8 from the          *)
(* preferred chart at q to any chart c of the atlas.                         *)
(* ========================================================================= *)

let P2BX_LGRAD2_CS = prove
 (`!U (G:real^N->real^N^N) f y u.
     metric_field U G /\ y IN U /\ (\z. lift(f z)) differentiable (at y)
     ==> drop(frechet_derivative (\z. lift(f z)) (at y) u) pow 2 <=
         lgrad2 G f y * (u dot (G y ** u))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `gr = (lambda i. drop(frechet_derivative (\z. lift((f:real^N->real) z)) (at y)
                                    (basis i))):real^N` THEN
  SUBGOAL_THEN `drop(frechet_derivative (\z. lift((f:real^N->real) z)) (at y) u) =
                gr dot (u:real^N)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\z. lift((f:real^N->real) z)`; `y:real^N`; `u:real^N`]
                  WAN_FRECHET_DIR_SUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "gr" THEN
    SIMP_TAC[dot; LAMBDA_BETA] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lgrad2 (G:real^N->real^N^N) f y = gr dot (matrix_inv(G y) ** gr)`
  SUBST1_TAC THENL
   [REWRITE_TAC[lgrad2] THEN
    MP_TAC(ISPECL [`matrix_inv((G:real^N->real^N^N) y)`;
                   `\i. drop(frechet_derivative (\z. lift((f:real^N->real) z)) (at y)
                                                 (basis i))`] LRG_QUADFORM_SUM) THEN
    BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "gr" THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y /\ invertible(G y)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `transp(matrix_inv((G:real^N->real^N^N) y)) = matrix_inv(G y)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(G:real^N->real^N^N) y` SYMMETRIC_MATRIX_INV) THEN
    ASM_REWRITE_TAC[symmetric_matrix]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `matrix_inv((G:real^N->real^N^N) y) ** gr`; `u:real^N`] LRG_METRIC_CS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(matrix_inv((G:real^N->real^N^N) y) ** gr) dot (G y ** u) = gr dot (u:real^N) /\
    (matrix_inv(G y) ** gr) dot (G y ** (matrix_inv(G y) ** gr)) =
    gr dot (matrix_inv(G y) ** gr)`
  (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `(G:real^N->real^N^N) y` MATRIX_INV) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID] THEN
    REWRITE_TAC[DOT_SYM]]);;

(* Transition from the chart c' to the chart c around a common point q. *)

let P2BX_TRANS_FACTS = prove
 (`!(top:B topology) atlas (c:(B->bool)#(B->real^N)) c' q.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
     q IN FST c /\ q IN FST c'
     ==> open(IMAGE (SND c') (FST c' INTER FST c)) /\
         SND c' q IN IMAGE (SND c') (FST c' INTER FST c) /\
         (!y. y IN IMAGE (SND c') (FST c' INTER FST c)
              ==> chart_trans c' c y IN IMAGE (SND c) (FST c) /\
                  chart_inv c (chart_trans c' c y) = chart_inv c' y) /\
         chart_trans c' c (SND c' q) = SND c q /\
         (chart_trans c' c has_derivative chart_jac c' c q) (at (SND c' q)) /\
         linear(chart_jac c' c q) /\
         invertible(matrix(chart_jac c' c q))`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                       `V:B->bool`; `psi:B->real^N`; `U:B->bool`; `phi:B->real^N`; `q:B`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `U:B->bool`; `phi:B->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `V:B->bool`; `psi:B->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "IV") THEN DISCH_THEN(LABEL_TAC "IU") THEN
  SUBGOAL_THEN `(q:B) IN U INTER V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `U:B->bool`; `phi:B->real^N`; `V:B->bool`; `psi:B->real^N`]
                  CHART_OVERLAP_IMAGE_OPEN) THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `U:B->bool`; `phi:B->real^N`; `V:B->bool`; `psi:B->real^N`; `x:B`]
           CHART_TRANS_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[chart_jac; SND; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:B->real^N) (U INTER V)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                     `U:B->bool`; `phi:B->real^N`; `V:B->bool`; `psi:B->real^N`]
                    CHART_OVERLAP_IMAGE_OPEN) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CHART_TRANS_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CHART_JAC_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[chart_jac; SND] THEN MATCH_MP_TAC LRG_DIFFEO_JACOBIAN_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (psi:B->real^N) (U INTER V)`;
                          `IMAGE (phi:B->real^N) (U INTER V)`;
                          `chart_trans (V,psi) (U:B->bool,phi:B->real^N)`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* A space-time derivative in the W3 convention (chart c, space first)      *)
(* gives the derivative in the FL8 convention (chart c', time first).       *)

let P2BX_DERIV_CHART_SWAP = prove
 (`!(top:B topology) atlas (c:(B->bool)#(B->real^N)) c' q (h:real->B->real) t0 D.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
     q IN FST c /\ q IN FST c' /\
     ((\z. lift(h (drop(sndcart z)) (chart_inv c (fstcart z)))) has_derivative D)
       (at (pastecart (SND c q) (lift t0)))
     ==> ((\z. lift(h (drop(fstcart z)) (chart_inv c' (sndcart z)))) has_derivative
          (\k. D(pastecart (chart_jac c' c q (sndcart k)) (fstcart k))))
         (at (pastecart (lift t0) (SND c' q)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`; `c':(B->bool)#(B->real^N)`; `q:B`]
         P2BX_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `J = chart_jac (c':(B->bool)#(B->real^N)) c q` THEN
  ABBREV_TAC `tst = \z:real^(1,N)finite_sum.
                       pastecart (chart_trans (c':(B->bool)#(B->real^N)) c (sndcart z))
                                 (fstcart z)` THEN
  SUBGOAL_THEN
   `((tst:real^(1,N)finite_sum->real^(N,1)finite_sum) has_derivative
     (\k. pastecart ((J:real^N->real^N) (sndcart k)) (fstcart k)))
    (at (pastecart (lift t0) (SND (c':(B->bool)#(B->real^N)) q)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "tst" THEN MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\z:real^(1,N)finite_sum. chart_trans (c':(B->bool)#(B->real^N)) c (sndcart z)) =
        chart_trans c' c o sndcart /\
        (\k:real^(1,N)finite_sum. (J:real^N->real^N) (sndcart k)) = J o sndcart`
      (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_SNDCART] THEN
      ASM_REWRITE_TAC[SNDCART_PASTECART];
      SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_FSTCART; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(tst:real^(1,N)finite_sum->real^(N,1)finite_sum)
      (pastecart (lift t0) (SND (c':(B->bool)#(B->real^N)) q)) =
    pastecart (SND (c:(B->bool)#(B->real^N)) q) (lift t0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "tst" THEN ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `(\z. lift((h:real->B->real) (drop(sndcart z)) (chart_inv c (fstcart z)))) o
              (tst:real^(1,N)finite_sum->real^(N,1)finite_sum)` THEN
  UNDISCH_TAC `open(IMAGE (SND (c':(B->bool)#(B->real^N)))
                         (FST c' INTER FST (c:(B->bool)#(B->real^N))))` THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `SND (c':(B->bool)#(B->real^N)) q`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `sndcart(z:real^(1,N)finite_sum) IN
                  IMAGE (SND (c':(B->bool)#(B->real^N))) (FST c' INTER FST (c:(B->bool)#(B->real^N)))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `ball(SND (c':(B->bool)#(B->real^N)) q,d) SUBSET
                   IMAGE (SND c') (FST c' INTER FST (c:(B->bool)#(B->real^N)))` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `dist(z:real^(1,N)finite_sum,
                       pastecart (lift t0) (SND (c':(B->bool)#(B->real^N)) q))` THEN
      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
      MP_TAC(ISPEC `z - pastecart (lift t0) (SND (c':(B->bool)#(B->real^N)) q)`
                   NORM_SNDCART) THEN
      REWRITE_TAC[SNDCART_SUB; SNDCART_PASTECART] THEN NORM_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "tst" THEN REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `(\k. (D:real^(N,1)finite_sum->real^1)
             (pastecart ((J:real^N->real^N) (sndcart k)) (fstcart k))) =
      D o (\k. pastecart (J (sndcart k)) (fstcart k))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]]);;

(* Facts about kappa-solutions used throughout. *)

let P2BX_KSOL_FACTS = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
         (!t. t <= &0 ==> riemannian_metric atlas (g t)) /\
         (!t x u v. t <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional atlas (g t) x u v) /\
         (!a. a < &0 ==> p2a_cbflow (top,atlas) a (&0) g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  SUBGOAL_THEN `!a. a < &0 ==> p2a_cbflow (top,atlas) a (&0) (g:real->B->real^3^3)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_KSOL_CBFLOW THEN
    EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `connected_space (top:B topology)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. t <= &0 ==> smooth_manifold_atlas (top:B topology) atlas /\
                               riemannian_metric atlas ((g:real->B->real^3^3) t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2BX_CBFLOW_SLICE THEN
    MAP_EVERY EXISTS_TAC [`t - &1`; `&0`] THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[REAL_LE_REFL]);;

(* FL8 read in any chart c of the atlas (W3 convention), at a point where   *)
(* the chart reading of the reduced length is differentiable, for every     *)
(* c in (0,1) (the view of [a,0] with a = -2 tau/(1 - c), P2BX_KLX_VIEW):    *)
(* the directional derivative bound in space and the lower bound in time.   *)

let P2BX_FL8_CHART = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p c z D cc.
     P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ c IN atlas /\
     fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z) /\
     ((\z. lift(p2bw_cfun c (p2b_klx (top,atlas) g p) z)) has_derivative D) (at z) /\
     &0 < cc /\ cc < &1
     ==> mfd_scalar atlas (g(--(drop(sndcart z)))) (chart_inv c (fstcart z)) <=
         (&1 + &2 / cc) * p2bw_cfun c (p2b_klx (top,atlas) g p) z / drop(sndcart z) /\
         (!v. drop(D(pastecart v (vec 0))) pow 2 <=
              ((&1 + &2 / cc) * p2bw_cfun c (p2b_klx (top,atlas) g p) z / drop(sndcart z) -
               mfd_scalar atlas (g(--(drop(sndcart z)))) (chart_inv c (fstcart z))) *
              (v dot (metric_local atlas c (g(--(drop(sndcart z)))) (fstcart z) ** v))) /\
         mfd_scalar atlas (g(--(drop(sndcart z)))) (chart_inv c (fstcart z)) -
         (&1 + &1 / cc) * p2bw_cfun c (p2b_klx (top,atlas) g p) z / drop(sndcart z)
         <= drop(D(pastecart (vec 0) (lift(&1))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL8") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  ABBREV_TAC `tau = drop(sndcart(z:real^(3,1)finite_sum))` THEN
  ABBREV_TAC `x = fstcart(z:real^(3,1)finite_sum)` THEN
  SUBGOAL_THEN `z = pastecart (x:real^3) (lift tau)` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "tau"] THEN REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  ABBREV_TAC `q = chart_inv (c:(B->bool)#(B->real^3)) x` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:B) IN FST(c:(B->bool)#(B->real^3)) /\ SND c q = x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(q:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `q:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c' = chart_at (atlas:((B->bool)#(B->real^3))->bool) (q:B)` THEN
  ABBREV_TAC `a = --(&2 * tau / (&1 - cc))` THEN
  SUBGOAL_THEN `a < &0 /\ tau < --a /\ tau <= (&1 - cc) * (&0 - a)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    SUBGOAL_THEN `&0 < &1 - cc` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - cc) * (tau / (&1 - cc)) = tau` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < tau / (&1 - cc)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < cc * (tau / (&1 - cc))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_NEG_NEG; REAL_SUB_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `V = p2a_flow_view (top:B topology,atlas) (real_interval[a,&0])
                    (g:real->B->real^3^3)` THEN
  SUBGOAL_THEN
   `((\z. lift(p2b_klx (top,atlas) (g:real->B->real^3^3) p (drop(fstcart z))
                 (chart_inv (c':(B->bool)#(B->real^3)) (sndcart z)))) has_derivative
     (\k. (D:real^(3,1)finite_sum->real^1)
            (pastecart (chart_jac c' (c:(B->bool)#(B->real^3)) q (sndcart k)) (fstcart k))))
    (at (pastecart (lift tau) (SND c' q)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`; `c':(B->bool)#(B->real^3)`; `q:B`;
                   `p2b_klx (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                            (g:real->B->real^3^3) p`;
                   `tau:real`; `D:real^(3,1)finite_sum->real^1`] P2BX_DERIV_CHART_SWAP) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `((\z. lift(p2bw_cfun (c:(B->bool)#(B->real^3))
                              (p2b_klx (top,atlas) (g:real->B->real^3^3) p) z)) has_derivative
                  D) (at (pastecart (x:real^3) (lift tau)))` THEN
    ASM_REWRITE_TAC[p2bw_cfun];
    ALL_TAC] THEN
  ABBREV_TAC `d1 = \k. (D:real^(3,1)finite_sum->real^1)
                         (pastecart (chart_jac (c':(B->bool)#(B->real^3)) c q (sndcart k))
                                    (fstcart k))` THEN
  SUBGOAL_THEN
   `((\z. lift(p2a_lx (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                         (real->B->real^3^3)) (&0) (p:B) (drop(fstcart z))
                 (chart_inv (c':(B->bool)#(B->real^3)) (sndcart z)))) has_derivative
     (d1:real^(1,3)finite_sum->real^1)) (at (pastecart (lift tau) (SND c' (q:B))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. lift(p2b_klx (top,atlas) (g:real->B->real^3^3) p (drop(fstcart z))
                           (chart_inv (c':(B->bool)#(B->real^3)) (sndcart z)))` THEN
    EXISTS_TAC `min tau (--a - tau)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z':real^(1,3)finite_sum` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN EXPAND_TAC "V" THEN MATCH_MP_TAC P2BX_KLX_VIEW THEN
    SUBGOAL_THEN `abs(drop(fstcart(z':real^(1,3)finite_sum)) - tau) <
                  min tau (--a - tau)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `dist(z':real^(1,3)finite_sum,
                       pastecart (lift tau) (SND (c':(B->bool)#(B->real^3)) q))` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN] THEN REWRITE_TAC[dist] THEN
      MP_TAC(ISPEC `z' - pastecart (lift tau) (SND (c':(B->bool)#(B->real^3)) q)`
                   NORM_FSTCART) THEN
      REWRITE_TAC[FSTCART_SUB; FSTCART_PASTECART; NORM_1; DROP_SUB; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "FL8" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                  `a:real`; `&0`; `g:real->B->real^3^3`; `p:B`; `cc:real`] o
                  REWRITE_RULE[P2A_FLOW_PROP_9_9_STATEMENT]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[DIMINDEX_3; LE_REFL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `mfd_sectional:((B->bool)#(B->real^3)->bool)->(B->real^3^3)->B->real^3->real^3->real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`tau:real`; `q:B`; `d1:real^(1,3)finite_sum->real^1`]) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN
  SUBGOAL_THEN
   `p2a_lx (p2a_flow_view (top:B topology,atlas) (real_interval[a,&0]) (g:real->B->real^3^3))
           (&0) p tau q = p2b_klx (top,atlas) g p tau q`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX_KLX_VIEW THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SP") (LABEL_TAC "TM")) THEN
  SUBGOAL_THEN
   `p2bw_cfun (c:(B->bool)#(B->real^3)) (p2b_klx (top,atlas) (g:real->B->real^3^3) p)
              (pastecart x (lift tau)) = p2b_klx (top,atlas) g p tau q`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2bw_cfun; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!l. &0 <= l /\ l + r <= b ==> r <= b`) THEN
    EXISTS_TAC `lgrad2 (metric_local atlas (c':(B->bool)#(B->real^3))
                          ((g:real->B->real^3^3) (--tau)))
                       (\y. p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g)
                                   (&0) p tau (chart_inv c' y))
                       (SND c' q)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LGRAD2_POS THEN
    EXISTS_TAC `IMAGE (SND (c':(B->bool)#(B->real^3))) (FST c')` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--tau))` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    USE_THEN "TM" MP_TAC THEN EXPAND_TAC "d1" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`; `c':(B->bool)#(B->real^3)`; `q:B`]
           P2BX_TRANS_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_jac (c':(B->bool)#(B->real^3)) c q (vec 0) = vec 0` SUBST1_TAC THENL
     [MP_TAC(ISPEC `chart_jac (c':(B->bool)#(B->real^3)) c q` LINEAR_0) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[]]] THEN
  X_GEN_TAC `v:real^3` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`; `c':(B->bool)#(B->real^3)`; `q:B`]
         P2BX_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `J = chart_jac (c':(B->bool)#(B->real^3)) c q` THEN
  ABBREV_TAC `u = matrix_inv(matrix(J:real^3->real^3)) ** (v:real^3)` THEN
  SUBGOAL_THEN `(J:real^3->real^3) u = v /\ matrix J ** u = v` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM MATRIX_WORKS] THEN EXPAND_TAC "u" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `fp = \y. p2a_lx (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                 (real->B->real^3^3)) (&0) (p:B) tau
                         (chart_inv (c':(B->bool)#(B->real^3)) y)` THEN
  SUBGOAL_THEN
   `((\y. lift((fp:real^3->real) y)) has_derivative
     (\w. (D:real^(3,1)finite_sum->real^1) (pastecart ((J:real^3->real^3) w) (vec 0))))
    (at (SND (c':(B->bool)#(B->real^3)) q))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\y. lift((fp:real^3->real) y)) =
      (\z. lift(p2a_lx (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                          (real->B->real^3^3)) (&0) (p:B) (drop(fstcart z))
                       (chart_inv (c':(B->bool)#(B->real^3)) (sndcart z)))) o
      (\y:real^3. pastecart (lift tau) y)`
    SUBST1_TAC THENL
     [EXPAND_TAC "fp" THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\w. (D:real^(3,1)finite_sum->real^1) (pastecart ((J:real^3->real^3) w) (vec 0))) =
      (d1:real^(1,3)finite_sum->real^1) o (\w:real^3. pastecart (vec 0) w)`
    SUBST1_TAC THENL
     [EXPAND_TAC "d1" THEN ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART;
                                           SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND (c':(B->bool)#(B->real^3))) (FST c'))
                 (metric_local atlas c' ((g:real->B->real^3^3) (--tau))) /\
    metric_field (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))
                 (metric_local atlas c (g (--tau)))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--tau))` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c':(B->bool)#(B->real^3))) (FST c')`;
                 `metric_local atlas (c':(B->bool)#(B->real^3)) ((g:real->B->real^3^3) (--tau))`;
                 `fp:real^3->real`; `SND (c':(B->bool)#(B->real^3)) q`; `u:real^3`]
                P2BX_LGRAD2_CS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\w. (D:real^(3,1)finite_sum->real^1)
                      (pastecart ((J:real^3->real^3) w) (vec 0))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `u dot (metric_local atlas (c':(B->bool)#(B->real^3)) ((g:real->B->real^3^3) (--tau))
            (SND c' q) ** u) =
    v dot (metric_local atlas c (g (--tau)) x ** v)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST(c':(B->bool)#(B->real^3))`; `SND(c':(B->bool)#(B->real^3))`;
                   `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                   `(g:real->B->real^3^3) (--tau)`; `q:B`] METRIC_LOCAL_JAC) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v dot (metric_local atlas (c:(B->bool)#(B->real^3))
                               ((g:real->B->real^3^3) (--tau)) x ** v)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `v:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    UNDISCH_TAC `metric_field (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))
                   (metric_local atlas c ((g:real->B->real^3^3) (--tau)))` THEN
    REWRITE_TAC[metric_field] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3` o CONJUNCT2 o
                                              CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lgrad2 (metric_local atlas (c':(B->bool)#(B->real^3))
                        ((g:real->B->real^3^3) (--tau))) fp (SND c' q) *
              (v dot (metric_local atlas (c:(B->bool)#(B->real^3)) (g (--tau)) x ** v))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "SP" MP_TAC THEN EXPAND_TAC "fp" THEN EXPAND_TAC "V" THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The limit c -> 1 in the constants of FL8, W3 read on p2bw_cdom c T with   *)
(* the Part 2B reduced length, and the almost-everywhere bounds in a chart.  *)
(* ========================================================================= *)

let P2BX_CC_LIMIT = prove
 (`!A B K. &0 <= B /\ &0 <= K /\ (!cc. &0 < cc /\ cc < &1 ==> A <= (&1 + K / cc) * B)
           ==> A <= (&1 + K) * B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `e = A - (&1 + K) * B` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = min (&1 / &2) (e / (&4 * (K + &1) * (B + &1)))` THEN
  SUBGOAL_THEN `&0 < d /\ d <= &1 / &2 /\ d * (&4 * (K + &1) * (B + &1)) <= e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &4 * (K + &1) * (B + &1)` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "d" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN
    CONJ_TAC THENL [CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_DIV]]; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / (&4 * (K + &1) * (B + &1)) * (&4 * (K + &1) * (B + &1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 - d`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `K / (&1 - d) <= K + &2 * K * d` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &1 - d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= K * d * (&1 - &2 * d)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * K * d * B <= e / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d * (&4 * (K + &1) * (B + &1)) / &2` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&2 * K * d * B <= d * (&4 * (K + &1) * (B + &1)) / &2 <=>
                    &0 <= d * (&2 * (K + B + &1))` SUBST1_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + K / (&1 - d)) * B <= (&1 + K) * B + &2 * K * d * B` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + K + &2 * K * d) * B` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Frechet derivatives at x only see the function near x. *)

let P2BX_FRECHET_LOCAL = prove
 (`!(f:real^M->real^N) g s x.
     open s /\ x IN s /\ (!y. y IN s ==> f y = g y)
     ==> frechet_derivative f (at x) = frechet_derivative g (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^M->real^N` THEN
  UNDISCH_TAC `open(s:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `g:real^M->real^N`] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^M) IN s` (fun th -> ASM_SIMP_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

(* W3 read with the Part 2B reduced length on p2bw_cdom c T (view of         *)
(* [-2T,0]): local Lipschitz property and the identity of Cor 6.51 a.e.      *)

let P2BX_W3_CHART = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p c Tm.
     P2B_REQ_P2A_WEAK_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ c IN atlas /\ &0 < Tm
     ==> wan_loclip (p2bw_cdom c Tm) (p2bw_cfun c (p2b_klx (top,atlas) g p)) /\
         negligible
          {z | z IN p2bw_cdom c Tm /\
               ~(wan_tder (p2bw_cfun c (p2b_klx (top,atlas) g p)) z *
                 p2bw_crho atlas c (&0) g z =
                 (p2bw_cscal atlas c (&0) g z * p2bw_crho atlas c (&0) g z -
                  p2bw_bil (p2bw_cA atlas c (&0) g) (p2bw_cfun c (p2b_klx (top,atlas) g p))
                           (p2bw_cfun c (p2b_klx (top,atlas) g p)) z) / &2 -
                 p2bw_cfun c (p2b_klx (top,atlas) g p) z / (&2 * drop(sndcart z)) *
                 p2bw_crho atlas c (&0) g z)}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W3") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `p2a_cbflow (top,atlas) (--(&2 * Tm)) (&0) (g:real->B->real^3^3)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[P2AF_CBFLOW_3] THEN STRIP_TAC THEN
  USE_THEN "W3" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                 `--(&2 * Tm)`; `&0`; `g:real->B->real^3^3`; `p:B`;
                                 `c:(B->bool)#(B->real^3)`] o
                 REWRITE_RULE[P2B_REQ_P2A_WEAK_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM P2A_FLOW_VIEW_3] THEN
  ABBREV_TAC `LW = p2bw_cfun (c:(B->bool)#(B->real^3))
                     (p2a_lx (p2a_flow_view (top,atlas) (real_interval[--(&2 * Tm),&0])
                                (g:real->B->real^3^3)) (&0) p)` THEN
  ABBREV_TAC `LK = p2bw_cfun (c:(B->bool)#(B->real^3))
                     (p2b_klx (top,atlas) (g:real->B->real^3^3) p)` THEN
  SUBGOAL_THEN `!z. z IN p2bw_cdom (c:(B->bool)#(B->real^3)) Tm ==> (LK:real^(3,1)finite_sum->real) z = LW z`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["LK"; "LW"] THEN REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; p2bw_cfun] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_KLX_VIEW THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2bw_cdom (c:(B->bool)#(B->real^3)) Tm SUBSET p2bw_cdom c (&0 - --(&2 * Tm))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; p2bw_cdom; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(p2bw_cdom (c:(B->bool)#(B->real^3)) Tm)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_CDOM_OPEN THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `wan_loclip (p2bw_cdom (c:(B->bool)#(B->real^3)) (&0 - --(&2 * Tm)))
                            (LW:real^(3,1)finite_sum->real)` THEN
    REWRITE_TAC[wan_loclip] THEN DISCH_TAC THEN X_GEN_TAC `k:real^(3,1)finite_sum->bool` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:real^(3,1)finite_sum->bool`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `L:real` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(LK:real^(3,1)finite_sum->real) x = LW x /\ LK y = LW y`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC
   `p2bw_tid (p2bw_cdom (c:(B->bool)#(B->real^3)) (&0 - --(&2 * Tm)))
             (p2bw_cA atlas c (&0) (g:real->B->real^3^3)) (p2bw_crho atlas c (&0) g)
             (p2bw_cscal atlas c (&0) g) (LW:real^(3,1)finite_sum->real)` THEN
  REWRITE_TAC[p2bw_tid] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\w. lift((LK:real^(3,1)finite_sum->real) w)) (at z) =
    frechet_derivative (\w. lift((LW:real^(3,1)finite_sum->real) w)) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_FRECHET_LOCAL THEN
    EXISTS_TAC `p2bw_cdom (c:(B->bool)#(B->real^3)) Tm` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `~(wan_tder (LK:real^(3,1)finite_sum->real) z * p2bw_crho atlas c (&0) (g:real->B->real^3^3) z =
      (p2bw_cscal atlas c (&0) g z * p2bw_crho atlas c (&0) g z -
       p2bw_bil (p2bw_cA atlas (c:(B->bool)#(B->real^3)) (&0) g) LK LK z) / &2 -
      LK z / (&2 * drop (sndcart z)) * p2bw_crho atlas c (&0) g z)` THEN
  ASM_SIMP_TAC[wan_tder; wan_xder; p2bw_bil]);;

(* The bounds of MT Cor 9.10 at the points of a chart where the chart       *)
(* reading of l is differentiable (FL8 with c -> 1): R <= 3 l / tau,         *)
(* |dl(v)|^2 <= (3 l / tau - R) |v|^2_g and dl/dtau >= -2 l / tau.          *)

let P2BX_CHART_DIFF_BOUNDS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p c z D.
     P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\ P2A_FLOW_MIN_EXISTS_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ c IN atlas /\
     fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z) /\
     ((\z. lift(p2bw_cfun c (p2b_klx (top,atlas) g p) z)) has_derivative D) (at z)
     ==> mfd_scalar atlas (g(--(drop(sndcart z)))) (chart_inv c (fstcart z)) <=
         &3 * p2bw_cfun c (p2b_klx (top,atlas) g p) z / drop(sndcart z) /\
         (!v. drop(D(pastecart v (vec 0))) pow 2 <=
              (&3 * p2bw_cfun c (p2b_klx (top,atlas) g p) z / drop(sndcart z) -
               mfd_scalar atlas (g(--(drop(sndcart z)))) (chart_inv c (fstcart z))) *
              (v dot (metric_local atlas c (g(--(drop(sndcart z)))) (fstcart z) ** v))) /\
         --(&2 * p2bw_cfun c (p2b_klx (top,atlas) g p) z / drop(sndcart z))
         <= drop(D(pastecart (vec 0) (lift(&1))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL8") (CONJUNCTS_THEN2 (LABEL_TAC "FL2")
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  ABBREV_TAC `tau = drop(sndcart(z:real^(3,1)finite_sum))` THEN
  ABBREV_TAC `L = p2bw_cfun (c:(B->bool)#(B->real^3))
                    (p2b_klx (top,atlas) (g:real->B->real^3^3) p) z` THEN
  ABBREV_TAC `R = mfd_scalar atlas ((g:real->B->real^3^3) (--tau))
                    (chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)))` THEN
  SUBGOAL_THEN `&0 <= L / tau` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXPAND_TAC "L" THEN
    REWRITE_TAC[p2bw_cfun] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BX_KLX_NONNEG THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)) IN FST c`
    MP_TAC THENL [ASM_SIMP_TAC[]; ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC P2BX_MFD_SCALAR_NONNEG THEN
    EXISTS_TAC `top:B topology` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)) IN
                  topspace top` ASSUME_TAC THENL
     [SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)) IN
                    FST c` MP_TAC THENL [ASM_SIMP_TAC[]; ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!cc. &0 < cc /\ cc < &1
         ==> R <= (&1 + &2 / cc) * L / tau /\
             (!v. drop((D:real^(3,1)finite_sum->real^1) (pastecart v (vec 0))) pow 2 <=
                  ((&1 + &2 / cc) * L / tau - R) *
                  (v dot (metric_local atlas (c:(B->bool)#(B->real^3))
                           ((g:real->B->real^3^3) (--tau)) (fstcart(z:real^(3,1)finite_sum)) ** v))) /\
             R - (&1 + &1 / cc) * L / tau <= drop(D(pastecart (vec 0) (lift(&1))))`
  (LABEL_TAC "CC") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                   `c:(B->bool)#(B->real^3)`; `z:real^(3,1)finite_sum`;
                   `D:real^(3,1)finite_sum->real^1`; `cc:real`] P2BX_FL8_CHART) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(a * b) / c = a * b / c`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`R:real`; `L / tau`; `&2`] P2BX_CC_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POS] THEN REPEAT STRIP_TAC THEN
      USE_THEN "CC" (MP_TAC o SPEC `cc:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REAL_ARITH_TAC];
    X_GEN_TAC `v:real^3` THEN
    SUBGOAL_THEN `&0 <= v dot (metric_local atlas (c:(B->bool)#(B->real^3))
                             ((g:real->B->real^3^3) (--tau)) (fstcart(z:real^(3,1)finite_sum)) ** v)`
    ASSUME_TAC THENL
     [ASM_CASES_TAC `v:real^3 = vec 0` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--tau))` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `c:(B->bool)#(B->real^3)`) THEN
      ASM_REWRITE_TAC[metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `fstcart(z:real^(3,1)finite_sum)` o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`drop((D:real^(3,1)finite_sum->real^1) (pastecart v (vec 0))) pow 2 +
                    R * (v dot (metric_local atlas (c:(B->bool)#(B->real^3))
                             ((g:real->B->real^3^3) (--tau)) (fstcart(z:real^(3,1)finite_sum)) ** v))`;
                   `L / tau * (v dot (metric_local atlas (c:(B->bool)#(B->real^3))
                             ((g:real->B->real^3^3) (--tau)) (fstcart(z:real^(3,1)finite_sum)) ** v))`;
                   `&2`] P2BX_CC_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN REPEAT STRIP_TAC THEN
      USE_THEN "CC" (MP_TAC o SPEC `cc:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT1 o CONJUNCT2) THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    MP_TAC(ISPECL [`--drop((D:real^(3,1)finite_sum->real^1) (pastecart (vec 0) (lift(&1))))`;
                   `L / tau`; `&1`] P2BX_CC_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POS] THEN REPEAT STRIP_TAC THEN
      USE_THEN "CC" (MP_TAC o SPEC `cc:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* At a point of differentiability where the identity of W3 holds:          *)
(* dl/dtau = (R - |grad l|^2)/2 - l/(2 tau) <= R/2 - l/(2 tau) <= l / tau.  *)

let P2BX_CHART_TID_UPPER = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p c z D.
     P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\ P2A_FLOW_MIN_EXISTS_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ c IN atlas /\
     fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z) /\
     ((\z. lift(p2bw_cfun c (p2b_klx (top,atlas) g p) z)) has_derivative D) (at z) /\
     wan_tder (p2bw_cfun c (p2b_klx (top,atlas) g p)) z * p2bw_crho atlas c (&0) g z =
     (p2bw_cscal atlas c (&0) g z * p2bw_crho atlas c (&0) g z -
      p2bw_bil (p2bw_cA atlas c (&0) g) (p2bw_cfun c (p2b_klx (top,atlas) g p))
               (p2bw_cfun c (p2b_klx (top,atlas) g p)) z) / &2 -
     p2bw_cfun c (p2b_klx (top,atlas) g p) z / (&2 * drop(sndcart z)) *
     p2bw_crho atlas c (&0) g z
     ==> drop(D(pastecart (vec 0) (lift(&1)))) <=
         p2bw_cfun c (p2b_klx (top,atlas) g p) z / drop(sndcart z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `c:(B->bool)#(B->real^3)`; `z:real^(3,1)finite_sum`;
                 `D:real^(3,1)finite_sum->real^1`] P2BX_CHART_DIFF_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  ABBREV_TAC `G = p2bw_cmet atlas (c:(B->bool)#(B->real^3)) (&0) (g:real->B->real^3^3) z` THEN
  SUBGOAL_THEN `transp(G:real^3^3) = G /\ !v. ~(v = vec 0) ==> &0 < v dot (G ** v)`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[p2bw_cmet; REAL_SUB_LZERO] THEN
    SUBGOAL_THEN `riemannian_metric atlas
                    ((g:real->B->real^3^3) (--(drop(sndcart(z:real^(3,1)finite_sum)))))`
    MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN(MP_TAC o SPEC `c:(B->bool)#(B->real^3)`) THEN
    ASM_REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `fstcart(z:real^(3,1)finite_sum)` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BW_COEFF_POINT) THEN
  SUBGOAL_THEN `&0 < p2bw_crho atlas (c:(B->bool)#(B->real^3)) (&0) (g:real->B->real^3^3) z`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2bw_crho] THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= p2bw_bil (p2bw_cA atlas (c:(B->bool)#(B->real^3)) (&0) (g:real->B->real^3^3))
                   (p2bw_cfun c (p2b_klx (top,atlas) g p))
                   (p2bw_cfun c (p2b_klx (top,atlas) g p)) z`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bw_bil] THEN
    REWRITE_TAC[REAL_ARITH `a * x * y:real = a * x * y`] THEN
    MP_TAC(ISPECL [`p2bw_cA atlas (c:(B->bool)#(B->real^3)) (&0) (g:real->B->real^3^3) z`;
                   `\i. wan_xder i (p2bw_cfun (c:(B->bool)#(B->real^3))
                                     (p2b_klx (top,atlas) (g:real->B->real^3^3) p)) z`]
                  LRG_QUADFORM_SUM) THEN
    BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[p2bw_cA; p2bw_crho] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_tder (p2bw_cfun (c:(B->bool)#(B->real^3))
                  (p2b_klx (top,atlas) (g:real->B->real^3^3) p)) z =
                drop((D:real^(3,1)finite_sum->real^1) (pastecart (vec 0) (lift(&1))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[wan_tder] THEN FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2bw_cscal atlas (c:(B->bool)#(B->real^3)) (&0) (g:real->B->real^3^3) z =
                mfd_scalar atlas (g(--(drop(sndcart z)))) (chart_inv c (fstcart z))`
  ASSUME_TAC THENL [REWRITE_TAC[p2bw_cscal; REAL_SUB_LZERO]; ALL_TAC] THEN
  ABBREV_TAC `rh = p2bw_crho atlas (c:(B->bool)#(B->real^3)) (&0) (g:real->B->real^3^3) z` THEN
  ABBREV_TAC `bl = p2bw_bil (p2bw_cA atlas (c:(B->bool)#(B->real^3)) (&0) (g:real->B->real^3^3))
                   (p2bw_cfun c (p2b_klx (top,atlas) g p))
                   (p2bw_cfun c (p2b_klx (top,atlas) g p)) z` THEN
  ABBREV_TAC `RR = mfd_scalar atlas ((g:real->B->real^3^3) (--(drop(sndcart z))))
                     (chart_inv (c:(B->bool)#(B->real^3)) (fstcart z))` THEN
  ABBREV_TAC `LL = p2bw_cfun (c:(B->bool)#(B->real^3))
                     (p2b_klx (top,atlas) (g:real->B->real^3^3) p) z` THEN
  ABBREV_TAC `dt = drop((D:real^(3,1)finite_sum->real^1) (pastecart (vec 0) (lift(&1))))` THEN
  ABBREV_TAC `tau = drop(sndcart(z:real^(3,1)finite_sum))` THEN
  SUBGOAL_THEN `dt * rh = (RR * rh - bl) / &2 - LL / (&2 * tau) * rh` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dt <= RR / &2 - LL / (&2 * tau)` MP_TAC THENL
   [SUBGOAL_THEN `dt * rh <= (RR / &2 - LL / (&2 * tau)) * rh` MP_TAC THENL
     [UNDISCH_TAC `&0 <= bl` THEN
      SUBGOAL_THEN `dt * rh = (RR * rh - bl) / &2 - LL / (&2 * tau) * rh` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_RMUL_EQ]];
    ALL_TAC] THEN
  UNDISCH_TAC `RR <= &3 * LL / tau` THEN UNDISCH_TAC `&0 < tau` THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  SPEC_TAC(`inv tau`,`it:real`) THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Monotonicity in backward time (MT Cor 9.10, second display, integrated):  *)
(* t^2 l is nondecreasing and l / t is nonincreasing along every chart line, *)
(* by P2BX_LINE_BOUND on -(tau^2 L) and L / tau.                             *)
(* ========================================================================= *)

let P2BX_TAU_SQ_DERIV = prove
 (`!z:real^(N,1)finite_sum.
     ((\y. lift(drop(sndcart y) pow 2)) has_derivative
      (\h. lift(&2 * drop(sndcart z) * drop(sndcart h)))) (at z)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\y:real^(N,1)finite_sum. lift(drop(sndcart y) pow 2)) =
                (\y. lift(drop(sndcart y) * drop(sndcart y)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `(\h:real^(N,1)finite_sum. lift(&2 * drop(sndcart(z:real^(N,1)finite_sum)) *
                                                drop(sndcart h))) =
                (\h. lift(drop(sndcart z) * drop(sndcart h) + drop(sndcart h) * drop(sndcart z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LRG_HAS_DERIVATIVE_LIFT_MUL THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SNDCART]);;

let P2BX_TAU_INV_DERIV = prove
 (`!z:real^(N,1)finite_sum.
     &0 < drop(sndcart z)
     ==> ((\y. lift(inv(drop(sndcart y)))) has_derivative
          (\h. lift(--(drop(sndcart h)) / drop(sndcart z) pow 2))) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^(N,1)finite_sum. lift(inv(drop(sndcart y)))) =
                (lift o inv o drop) o (\y. sndcart y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\h:real^(N,1)finite_sum. lift(--(drop(sndcart h)) /
                                                drop(sndcart(z:real^(N,1)finite_sum)) pow 2)) =
                (\x. --inv(drop(sndcart z) pow 2) % x) o (\h. sndcart h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[ETA_AX; LINEAR_SNDCART];
    MP_TAC(SPEC `drop(sndcart(z:real^(N,1)finite_sum))` HAS_REAL_DERIVATIVE_INV_BASIC) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; HAS_REAL_FRECHET_DERIVATIVE_AT; LIFT_DROP]]);;

let P2BX_LOCLIP_GLOBAL = prove
 (`!(s:real^M->bool) f B.
     (!z w. z IN s /\ w IN s ==> abs(f z - f w) <= B * norm(z - w))
     ==> wan_loclip s f`,
  REWRITE_TAC[wan_loclip] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `B:real` THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let P2BX_ABS_DROP_SNDCART = prove
 (`!z w:real^(N,1)finite_sum.
     abs(drop(sndcart z) - drop(sndcart w)) <= norm(z - w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DROP_SUB; GSYM SNDCART_SUB; GSYM NORM_1] THEN
  REWRITE_TAC[NORM_SNDCART]);;

(* Linearity in the time direction, Lipschitz bounds for tau^2 and 1/tau. *)

let P2BX_DIR_TIME = prove
 (`!(D:real^(N,1)finite_sum->real^1) h.
     linear D
     ==> drop(D(pastecart (vec 0) (lift h))) = h * drop(D(pastecart (vec 0) (lift(&1))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (vec 0:real^N) (lift h) = h % pastecart (vec 0) (lift(&1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO; GSYM LIFT_CMUL; REAL_MUL_RID];
    ASM_SIMP_TAC[LINEAR_CMUL; DROP_CMUL]]);;

let P2BX_LOCLIP_TAU_SQ = prove
 (`!(s:real^(N,1)finite_sum->bool) M.
     (!z. z IN s ==> &0 < drop(sndcart z) /\ drop(sndcart z) < M)
     ==> wan_loclip s (\z. --(drop(sndcart z) pow 2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_LOCLIP_GLOBAL THEN
  EXISTS_TAC `&2 * M` THEN MAP_EVERY X_GEN_TAC [`z:real^(N,1)finite_sum`; `w:real^(N,1)finite_sum`] THEN
  STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`z:real^(N,1)finite_sum`; `w:real^(N,1)finite_sum`] P2BX_ABS_DROP_SNDCART) THEN
  SUBGOAL_THEN `&0 < drop(sndcart(z:real^(N,1)finite_sum)) /\ drop(sndcart z) < M /\
                &0 < drop(sndcart(w:real^(N,1)finite_sum)) /\ drop(sndcart w) < M`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`drop(sndcart(z:real^(N,1)finite_sum))`,`a:real`) THEN
  SPEC_TAC(`drop(sndcart(w:real^(N,1)finite_sum))`,`b:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(--(a pow 2) - --(b pow 2)) = (a + b) * abs(a - b)` SUBST1_TAC THENL
   [SUBGOAL_THEN `--(a pow 2) - --(b pow 2) = --((a + b) * (a - b))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a + b /\ a + b <= &2 * M` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * M) * abs(a - b)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P2BX_LOCLIP_TAU_INV = prove
 (`!(s:real^(N,1)finite_sum->bool) m.
     &0 < m /\ (!z. z IN s ==> m < drop(sndcart z))
     ==> wan_loclip s (\z. inv(drop(sndcart z)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_LOCLIP_GLOBAL THEN
  EXISTS_TAC `inv(m pow 2)` THEN
  MAP_EVERY X_GEN_TAC [`z:real^(N,1)finite_sum`; `w:real^(N,1)finite_sum`] THEN STRIP_TAC THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`z:real^(N,1)finite_sum`; `w:real^(N,1)finite_sum`] P2BX_ABS_DROP_SNDCART) THEN
  SUBGOAL_THEN `m < drop(sndcart(z:real^(N,1)finite_sum)) /\ m < drop(sndcart(w:real^(N,1)finite_sum))`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`drop(sndcart(z:real^(N,1)finite_sum))`,`a:real`) THEN
  SPEC_TAC(`drop(sndcart(w:real^(N,1)finite_sum))`,`b:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < a /\ &0 < b` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv a - inv b = (b - a) / (a * b)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  SUBGOAL_THEN `abs(a * b) = a * b` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a * b /\ m pow 2 <= a * b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL] THEN REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(m pow 2) * norm(z - w:real^(N,1)finite_sum) * m pow 2` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < m pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < x ==> inv x * y * x = y`] THEN
    ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]]);;

(* Monotonicity along a chart line {x} x [t1,t2]. *)

let P2BX_TIME_MONO_CHART = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p c x t1 t2.
     P2B_REQ_P2A_WEAK_STATEMENT w /\ P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\
     P2A_FLOW_MIN_EXISTS_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ c IN atlas /\
     x IN IMAGE (SND c) (FST c) /\ &0 < t1 /\ t1 <= t2
     ==> t1 pow 2 * p2bw_cfun c (p2b_klx (top,atlas) g p) (pastecart x (lift t1)) <=
         t2 pow 2 * p2bw_cfun c (p2b_klx (top,atlas) g p) (pastecart x (lift t2)) /\
         t1 * p2bw_cfun c (p2b_klx (top,atlas) g p) (pastecart x (lift t2)) <=
         t2 * p2bw_cfun c (p2b_klx (top,atlas) g p) (pastecart x (lift t1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W3") (CONJUNCTS_THEN2 (LABEL_TAC "FL8")
    (CONJUNCTS_THEN2 (LABEL_TAC "FL2") STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  ABBREV_TAC `L = p2bw_cfun (c:(B->bool)#(B->real^3))
                    (p2b_klx (top,atlas) (g:real->B->real^3^3) p)` THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `c:(B->bool)#(B->real^3)`; `t2 + &2`] P2BX_W3_CHART) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LIP") (LABEL_TAC "TID")) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `open(IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))`) THEN
  REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `kk = cball(x:real^3,r) PCROSS interval[lift(t1 / &2),lift(t2 + &1)]` THEN
  ABBREV_TAC `s = ball(x:real^3,r) PCROSS interval(lift(t1 / &2),lift(t2 + &1))` THEN
  SUBGOAL_THEN `compact(kk:real^(3,1)finite_sum->bool) /\ open(s:real^(3,1)finite_sum->bool) /\
                s SUBSET kk /\ kk SUBSET p2bw_cdom (c:(B->bool)#(B->real^3)) (t2 + &2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["kk"; "s"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_CBALL; COMPACT_INTERVAL];
      MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_BALL; OPEN_INTERVAL];
      MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[BALL_SUBSET_CBALL; INTERVAL_OPEN_SUBSET_CLOSED];
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; p2bw_cdom; IN_ELIM_THM;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
      REPEAT STRIP_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^(3,1)finite_sum. z IN s ==> t1 / &2 < drop(sndcart z) /\
                                                    drop(sndcart z) < t2 + &1`
  (LABEL_TAC "TB") THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                                    SNDCART_PASTECART; LIFT_DROP] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `n = {z | z IN kk /\ ~((\y. lift((L:real^(3,1)finite_sum->real) y)) differentiable at z)} UNION
        {z | z IN p2bw_cdom (c:(B->bool)#(B->real^3)) (t2 + &2) /\
             ~(wan_tder L z * p2bw_crho atlas c (&0) (g:real->B->real^3^3) z =
               (p2bw_cscal atlas c (&0) g z * p2bw_crho atlas c (&0) g z -
                p2bw_bil (p2bw_cA atlas c (&0) g) L L z) / &2 -
               L z / (&2 * drop(sndcart z)) * p2bw_crho atlas c (&0) g z)}` THEN
  SUBGOAL_THEN `negligible(n:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN MATCH_MP_TAC NEGLIGIBLE_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BW_LOCLIP_AE_ON THEN
    EXISTS_TAC `p2bw_cdom (c:(B->bool)#(B->real^3)) (t2 + &2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BX_CDOM_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN s /\ ~(z IN n)
        ==> ?D. ((\y. lift((L:real^(3,1)finite_sum->real) y)) has_derivative D) (at z) /\
                --(&2 * L z / drop(sndcart z)) <= drop(D(pastecart (vec 0) (lift(&1)))) /\
                drop(D(pastecart (vec 0) (lift(&1)))) <= L z / drop(sndcart z)`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^(3,1)finite_sum) IN kk /\ z IN p2bw_cdom (c:(B->bool)#(B->real^3)) (t2 + &2)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(\y. lift((L:real^(3,1)finite_sum->real) y)) differentiable at z` MP_TAC THENL
     [UNDISCH_TAC `~((z:real^(3,1)finite_sum) IN n)` THEN EXPAND_TAC "n" THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[differentiable] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `D:real^(3,1)finite_sum->real^1` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^(3,1)finite_sum) IN p2bw_cdom (c:(B->bool)#(B->real^3)) (t2 + &2)` THEN
    REWRITE_TAC[p2bw_cdom; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                     `c:(B->bool)#(B->real^3)`; `z:real^(3,1)finite_sum`;
                     `D:real^(3,1)finite_sum->real^1`] P2BX_CHART_DIFF_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                     `c:(B->bool)#(B->real^3)`; `z:real^(3,1)finite_sum`;
                     `D:real^(3,1)finite_sum->real^1`] P2BX_CHART_TID_UPPER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `~((z:real^(3,1)finite_sum) IN n)` THEN EXPAND_TAC "n" THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
      ASM_REWRITE_TAC[p2bw_cdom; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_loclip (s:real^(3,1)finite_sum->bool) L` ASSUME_TAC THENL
   [UNDISCH_TAC `wan_loclip (p2bw_cdom (c:(B->bool)#(B->real^3)) (t2 + &2))
                            (L:real^(3,1)finite_sum->real)` THEN
    REWRITE_TAC[wan_loclip] THEN DISCH_TAC THEN X_GEN_TAC `k:real^(3,1)finite_sum->bool` THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `kk:real^(3,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `s:real^(3,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. &0 <= u /\ u <= &1
                    ==> pastecart (x:real^3) (lift t1) + u % pastecart (vec 0) (lift(t2 - t1))
                        IN (s:real^(3,1)finite_sum->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD; PASTECART_IN_PCROSS; VECTOR_MUL_RZERO;
                VECTOR_ADD_RID; CENTRE_IN_BALL; IN_INTERVAL_1; GSYM LIFT_CMUL; GSYM LIFT_ADD;
                LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= u * (t2 - t1) /\ u * (t2 - t1) <= t2 - t1` MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `u * d <= &1 * d ==> u * d <= d`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (x:real^3) (lift t1) + pastecart (vec 0) (lift(t2 - t1)) =
                pastecart x (lift t2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_RID; GSYM LIFT_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^(3,1)finite_sum->bool`;
                   `\z:real^(3,1)finite_sum. --(drop(sndcart z) pow 2) * L z`;
                   `n:real^(3,1)finite_sum->bool`; `&0`;
                   `pastecart (vec 0:real^3) (lift(t2 - t1))`;
                   `pastecart (x:real^3) (lift t1)`] P2BX_LINE_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC P2BW_LOCLIP_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC P2BX_LOCLIP_TAU_SQ THEN EXISTS_TAC `t2 + &1` THEN
        X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
        USE_THEN "TB" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; UNDISCH_TAC `&0 < t1` THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
      USE_THEN "PT" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `D:real^(3,1)finite_sum->real^1` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `t1 / &2 < drop(sndcart(z:real^(3,1)finite_sum))` ASSUME_TAC THENL
       [USE_THEN "TB" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `((\z. lift(--(drop(sndcart z) pow 2) * (L:real^(3,1)finite_sum->real) z)) has_derivative
         (\h. lift(--(drop(sndcart z) pow 2) * drop((D:real^(3,1)finite_sum->real^1) h) +
                   --(&2 * drop(sndcart z) * drop(sndcart h)) * L z))) (at z)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC LRG_HAS_DERIVATIVE_LIFT_MUL THEN
        REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[LIFT_NEG] THEN MATCH_MP_TAC HAS_DERIVATIVE_NEG THEN
        REWRITE_TAC[P2BX_TAU_SQ_DERIV];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[differentiable] THEN
        FIRST_ASSUM(fun th -> EXISTS_TAC (rand(rator(concl th))) THEN ACCEPT_TAC th);
        ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[LIFT_DROP; SNDCART_PASTECART] THEN
      SUBGOAL_THEN `linear(D:real^(3,1)finite_sum->real^1)` ASSUME_TAC THENL
       [UNDISCH_TAC `((\y. lift((L:real^(3,1)finite_sum->real) y)) has_derivative D) (at z)` THEN
        SIMP_TAC[has_derivative];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`D:real^(3,1)finite_sum->real^1`; `t2 - t1:real`] P2BX_DIR_TIME) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ABBREV_TAC `tz = drop(sndcart(z:real^(3,1)finite_sum))` THEN
      ABBREV_TAC `d0 = drop((D:real^(3,1)finite_sum->real^1) (pastecart (vec 0) (lift(&1))))` THEN
      SUBGOAL_THEN `&0 < tz` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `--(&2 * (L:real^(3,1)finite_sum->real) z) <= tz * d0` ASSUME_TAC THENL
       [SUBGOAL_THEN `tz * --(&2 * (L:real^(3,1)finite_sum->real) z / tz) <= tz * d0`
        MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
        SUBGOAL_THEN `tz * --(&2 * (L:real^(3,1)finite_sum->real) z / tz) = --(&2 * L z)`
        SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < tz` THEN CONV_TAC REAL_FIELD; REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (t2 - t1) * tz * (tz * d0 + &2 * (L:real^(3,1)finite_sum->real) z)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ASM_REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP] THEN REAL_ARITH_TAC];
    MP_TAC(ISPECL [`s:real^(3,1)finite_sum->bool`;
                   `\z:real^(3,1)finite_sum. (L:real^(3,1)finite_sum->real) z * inv(drop(sndcart z))`;
                   `n:real^(3,1)finite_sum->bool`; `&0`;
                   `pastecart (vec 0:real^3) (lift(t2 - t1))`;
                   `pastecart (x:real^3) (lift t1)`] P2BX_LINE_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC P2BW_LOCLIP_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC P2BX_LOCLIP_TAU_INV THEN EXISTS_TAC `t1 / &2` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
        USE_THEN "TB" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
      USE_THEN "PT" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `D:real^(3,1)finite_sum->real^1` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `t1 / &2 < drop(sndcart(z:real^(3,1)finite_sum))` ASSUME_TAC THENL
       [USE_THEN "TB" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < drop(sndcart(z:real^(3,1)finite_sum))` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `((\z. lift((L:real^(3,1)finite_sum->real) z * inv(drop(sndcart z)))) has_derivative
         (\h. lift(L z * (--(drop(sndcart h)) / drop(sndcart z) pow 2) +
                   drop((D:real^(3,1)finite_sum->real^1) h) * inv(drop(sndcart z))))) (at z)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC LRG_HAS_DERIVATIVE_LIFT_MUL THEN
        REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC P2BX_TAU_INV_DERIV THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[differentiable] THEN
        FIRST_ASSUM(fun th -> EXISTS_TAC (rand(rator(concl th))) THEN ACCEPT_TAC th);
        ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[LIFT_DROP; SNDCART_PASTECART] THEN
      SUBGOAL_THEN `linear(D:real^(3,1)finite_sum->real^1)` ASSUME_TAC THENL
       [UNDISCH_TAC `((\y. lift((L:real^(3,1)finite_sum->real) y)) has_derivative D) (at z)` THEN
        SIMP_TAC[has_derivative];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`D:real^(3,1)finite_sum->real^1`; `t2 - t1:real`] P2BX_DIR_TIME) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ABBREV_TAC `tz = drop(sndcart(z:real^(3,1)finite_sum))` THEN
      ABBREV_TAC `d0 = drop((D:real^(3,1)finite_sum->real^1) (pastecart (vec 0) (lift(&1))))` THEN
      SUBGOAL_THEN `d0 * tz <= (L:real^(3,1)finite_sum->real) z` ASSUME_TAC THENL
       [UNDISCH_TAC `d0 <= (L:real^(3,1)finite_sum->real) z / tz` THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
        ALL_TAC] THEN
      SUBGOAL_THEN `(L:real^(3,1)finite_sum->real) z * --(t2 - t1) / tz pow 2 +
                    ((t2 - t1) * d0) * inv tz =
                    (t2 - t1) * (d0 * tz - L z) / tz pow 2`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < tz` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (t2 - t1) * ((L:real^(3,1)finite_sum->real) z - d0 * tz) / tz pow 2`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
      ASM_REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < t1 /\ &0 < t2` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `t1 * (L:real^(3,1)finite_sum->real) (pastecart x (lift t2)) -
        t2 * L (pastecart x (lift t1)) =
        (t1 * t2) * (L (pastecart x (lift t2)) * inv t2 - L (pastecart x (lift t1)) * inv t1)`
      MP_TAC THENL
       [UNDISCH_TAC `&0 < t1` THEN UNDISCH_TAC `&0 < t2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN
       `&0 <= (t1 * t2) * --((L:real^(3,1)finite_sum->real) (pastecart x (lift t2)) * inv t2 -
                             L (pastecart x (lift t1)) * inv t1)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The spatial bound of MT Cor 9.10 in a chart: sqrt(l + d) is locally       *)
(* (sqrt(3/(4 t)) + e)-Lipschitz for the frozen chart norm of g(-t)          *)
(* (P2BX_LINE_BOUND in the direction (y - x, 0)).                            *)
(* ========================================================================= *)

let P2BX_SQRT_LIP = prove
 (`!a b d. &0 < d /\ d <= a /\ d <= b
           ==> abs(sqrt a - sqrt b) <= abs(a - b) / (&2 * sqrt d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt d /\ sqrt d <= sqrt a /\ sqrt d <= sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt a - sqrt b = (a - b) / (sqrt a + sqrt b)` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt a + sqrt b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN
    SUBGOAL_THEN `sqrt a pow 2 = a /\ sqrt b pow 2 = b` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  SUBGOAL_THEN `abs(sqrt a + sqrt b) = sqrt a + sqrt b` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;

(* Quadratic forms of nearby matrices. *)

let P2BX_QUAD_NEAR = prove
 (`!(G0:real^N^N) G c0 e.
     &0 < c0 /\ &0 <= e /\ (!w. c0 * norm w pow 2 <= w dot (G0 ** w)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> abs(G$i$j - G0$i$j) <= c0 * e / &(dimindex(:N)) pow 2)
     ==> !w. w dot (G ** w) <= (&1 + e) * (w dot (G0 ** w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `w dot ((G:real^N^N) ** w) - w dot (G0 ** w) <= c0 * e * norm(w:real^N) pow 2`
  MP_TAC THENL
   [REWRITE_TAC[GSYM DOT_RSUB; GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
    ABBREV_TAC `A = (G:real^N^N) - G0` THEN
    SUBGOAL_THEN `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                        ==> abs((A:real^N^N)$i$j) <= c0 * e / &(dimindex(:N)) pow 2`
    ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN SIMP_TAC[MATRIX_SUB_COMPONENT] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[dot; matrix_vector_mul] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                  (\j. (c0 * e / &(dimindex(:N)) pow 2) * norm(w:real^N) pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
      ASM_SIMP_TAC[LAMBDA_BETA] THEN
      REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs x <= b ==> x <= b`) THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_POW_2] THEN
      SUBGOAL_THEN `abs((w:real^N)$i) <= norm w /\ abs(w$j) <= norm w` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[COMPONENT_LE_NORM]; ALL_TAC] THEN
      SUBGOAL_THEN `abs((A:real^N^N)$i$j) <= c0 * e / &(dimindex(:N)) pow 2` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `abs((w:real^N)$i) * abs((A:real^N^N)$i$j) * abs(w$j) <=
                    norm w * (c0 * e / &(dimindex(:N)) pow 2) * norm w` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
        SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        REAL_ARITH_TAC];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
      SUBGOAL_THEN `&0 < &(dimindex(:N))` MP_TAC THENL
       [SIMP_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> 0 < n`]; ALL_TAC] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < &(dimindex(:N))` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `w:real^N`) THEN
  SUBGOAL_THEN `&0 <= e * c0 * norm(w:real^N) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `e * c0 * norm(w:real^N) pow 2 <= e * (w dot (G0 ** w))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P2BX_ENTRY_LE_VECTORIZE = prove
 (`!(A:real^N^N) i j.
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> abs(A$i$j) <= norm((vectorize:real^N^N->real^(N,N)finite_prod) A)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV) [GSYM MATRIFY_VECTORIZE] THEN
  ASM_SIMP_TAC[MATRIFY_COMPONENT; COMPONENT_LE_NORM]);;

(* Arithmetic for the choice of the radii. *)

let P2BX_RATE_ARITH = prove
 (`!t0 dt e r tau.
     &0 < t0 /\ &0 < dt /\ &0 <= e /\ e <= dt * t0 / &3 /\ &0 <= r /\ r <= t0 / &2 /\
     r <= dt * t0 * t0 / &12 /\ t0 - r <= tau
     ==> &3 * (&1 + e) / (&4 * tau) <= &3 / (&4 * t0) + dt`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t0 / &2 <= tau /\ &0 < tau` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * tau * t0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * (&1 + e) / (&4 * tau) = (&3 * (&1 + e) * t0) / (&4 * tau * t0) /\
                &3 / (&4 * t0) + dt = (&3 * tau + &4 * dt * tau * t0) / (&4 * tau * t0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&0 < tau` THEN UNDISCH_TAC `&0 < t0` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  SUBGOAL_THEN `&0 <= (&2 * dt * t0) * (&2 * tau - t0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `e * t0 <= (dt * t0 / &3) * t0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= dt * t0 * t0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* sqrt(f + dl) is locally Lipschitz when f is and f >= 0. *)

let P2BX_LOCLIP_SQRT = prove
 (`!(s:real^M->bool) f dl.
     &0 < dl /\ (!z. z IN s ==> &0 <= f z) /\ wan_loclip s f
     ==> wan_loclip s (\z. sqrt(f z + dl))`,
  REWRITE_TAC[wan_loclip] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  EXISTS_TAC `abs L / (&2 * sqrt dl)` THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `&0 < &2 * sqrt dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(((f:real^M->real) x + dl) - (f y + dl)) / (&2 * sqrt dl)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_SQRT_LIP THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= (f:real^M->real) x /\ &0 <= f y` MP_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a + d) - (b + d) = a - b:real`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `(abs L / (&2 * sqrt dl) * norm(x - y:real^M)) * (&2 * sqrt dl) =
                abs L * norm(x - y)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &2 * sqrt dl` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * norm(x - y:real^M)` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  REAL_ARITH_TAC);;

(* Derivative of sqrt(f + dl). *)

let P2BX_SQRT_DERIV = prove
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

(* The pointwise bound for the derivative of sqrt(l + dl). *)

let P2BX_SQRT_BOUND_ARITH = prove
 (`!a L dl tau e1 Q0 K.
     &0 <= L /\ &0 < dl /\ &0 < tau /\ &0 <= Q0 /\ &0 < K /\ &0 <= e1 /\
     a pow 2 <= (&3 * L / tau) * ((&1 + e1) * Q0) /\
     &3 * (&1 + e1) / (&4 * tau) <= K pow 2
     ==> inv(&2 * sqrt(L + dl)) * a <= K * sqrt Q0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < L + dl` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `K * sqrt Q0 = sqrt(K pow 2 * Q0)` SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_MUL; REAL_LE_POW_2] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; SQRT_MUL; REAL_LE_POW_2];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  SUBGOAL_THEN `(inv(&2 * sqrt(L + dl)) * a) pow 2 = a pow 2 / (&4 * (L + dl))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV; REAL_POW_2] THEN
    SUBGOAL_THEN `sqrt(L + dl) * sqrt(L + dl) = L + dl` MP_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < L + dl` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * (L + dl)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&3 * L / tau) * ((&1 + e1) * Q0)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&3 * L / tau) * ((&1 + e1) * Q0) =
                (&3 * (&1 + e1) / (&4 * tau)) * (Q0 * (&4 * L))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < tau` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(K pow 2 * Q0) * (&4 * (L + dl)) = K pow 2 * (Q0 * (&4 * (L + dl)))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

(* The local spatial bound: for K^2 > 3/(4 t0), sqrt(l(t0,.) + dl) is        *)
(* K-Lipschitz for the frozen chart norm of g(-t0) at x0, on a small ball.   *)

let P2BX_SQRT_CHART_LOCAL = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p c x0 t0 dl K.
     P2B_REQ_P2A_WEAK_STATEMENT w /\ P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\
     P2A_FLOW_MIN_EXISTS_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ c IN atlas /\
     x0 IN IMAGE (SND c) (FST c) /\ &0 < t0 /\ &0 < dl /\ &0 < K /\
     &3 / (&4 * t0) < K pow 2
     ==> ?r. &0 < r /\ ball(x0,r) SUBSET IMAGE (SND c) (FST c) /\
             !x y. x IN ball(x0,r) /\ y IN ball(x0,r)
                   ==> sqrt(p2b_klx (top,atlas) g p t0 (chart_inv c y) + dl) -
                       sqrt(p2b_klx (top,atlas) g p t0 (chart_inv c x) + dl)
                       <= K * sqrt((y - x) dot
                                   (metric_local atlas c (g(--t0)) x0 ** (y - x)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W3") (CONJUNCTS_THEN2 (LABEL_TAC "FL8")
    (CONJUNCTS_THEN2 (LABEL_TAC "FL2") STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  ABBREV_TAC `L = p2bw_cfun (c:(B->bool)#(B->real^3))
                    (p2b_klx (top,atlas) (g:real->B->real^3^3) p)` THEN
  ABBREV_TAC `G = p2bw_cmet atlas (c:(B->bool)#(B->real^3)) (&0) (g:real->B->real^3^3)` THEN
  ABBREV_TAC `G0 = metric_local atlas (c:(B->bool)#(B->real^3)) ((g:real->B->real^3^3) (--t0)) x0` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the chart data on cdom c (2 t0) *)
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `c:(B->bool)#(B->real^3)`; `&2 * t0`] P2BX_W3_CHART) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LIP") (K ALL_TAC)) THEN
  SUBGOAL_THEN `open(p2bw_cdom (c:(B->bool)#(B->real^3)) (&2 * t0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2BX_CDOM_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (vectorize:real^3^3->real^(3,3)finite_prod) ((G:real^(3,1)finite_sum->real^3^3) z))
                continuous_on p2bw_cdom (c:(B->bool)#(B->real^3)) (&2 * t0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:B)`; `(:3)`] P2B_FLOW_CHART) THEN
    REWRITE_TAC[P2B_FLOW_CHART_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                               `--(&2 * t0)`; `&0`; `g:real->B->real^3^3`;
                               `c:(B->bool)#(B->real^3)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `p2a_cbflow (top,atlas) (--(&2 * t0)) (&0) (g:real->B->real^3^3)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[p2a_cbflow; ricci_flow_from];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&0 - --(&2 * t0) = &2 * t0`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o CONJUNCT1) THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (x0:real^3) (lift t0) IN p2bw_cdom (c:(B->bool)#(B->real^3)) (&2 * t0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^(3,1)finite_sum->real^3^3) (pastecart x0 (lift t0)) = G0` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G"; "G0"] THEN
    REWRITE_TAC[p2bw_cmet; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; REAL_SUB_LZERO];
    ALL_TAC] THEN
  (* lower bound of the frozen metric *)
  SUBGOAL_THEN `?c0. &0 < c0 /\ !v:real^3. c0 * norm v pow 2 <= v dot (G0 ** v)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (--t0)`; `FST(c:(B->bool)#(B->real^3))`;
                   `SND(c:(B->bool)#(B->real^3))`; `{x0:real^3}`] GRGD_METRIC_BOUNDS) THEN
    REWRITE_TAC[PAIR; COMPACT_SING; SING_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_SING] THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `c0:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x0:real^3`; `v:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the rates *)
  ABBREV_TAC `dt = K pow 2 - &3 / (&4 * t0)` THEN
  SUBGOAL_THEN `&0 < dt` ASSUME_TAC THENL [EXPAND_TAC "dt" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `e1 = dt * t0 / &3` THEN
  SUBGOAL_THEN `&0 < e1` ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `rt = min (t0 / &2) (dt * t0 * t0 / &12)` THEN
  SUBGOAL_THEN `&0 < rt /\ rt <= t0 / &2 /\ rt <= dt * t0 * t0 / &12` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rt" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* metric comparison near (x0,t0) *)
  SUBGOAL_THEN
   `?r1. &0 < r1 /\
         !z. dist(z,pastecart (x0:real^3) (lift t0)) < r1
             ==> !v:real^3. v dot ((G:real^(3,1)finite_sum->real^3^3) z ** v) <=
                            (&1 + e1) * (v dot (G0 ** v))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                        ((G:real^(3,1)finite_sum->real^3^3) z))
                 continuous_on p2bw_cdom (c:(B->bool)#(B->real^3)) (&2 * t0)` THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (x0:real^3) (lift t0)`) THEN
    ASM_REWRITE_TAC[continuous_at] THEN
    DISCH_THEN(MP_TAC o SPEC `c0 * e1 / &9`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r1:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2BX_QUAD_NEAR THEN EXISTS_TAC `c0:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; DIMINDEX_3] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((vectorize:real^3^3->real^(3,3)finite_prod)
                     ((G:real^(3,1)finite_sum->real^3^3) z) - vectorize G0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM VECTORIZE_SUB] THEN
      SIMP_TAC[GSYM MATRIX_SUB_COMPONENT; ASSUME `1 <= i`; ASSUME `i <= 3`;
               ASSUME `1 <= j`; ASSUME `j <= 3`] THEN
      MATCH_MP_TAC P2BX_ENTRY_LE_VECTORIZE THEN ASM_REWRITE_TAC[DIMINDEX_3];
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN ASM_REWRITE_TAC[dist] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the radius *)
  MP_TAC(ASSUME `open(IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))`) THEN
  REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `x0:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rU:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min (min rU (r1 / &2)) rt` THEN
  SUBGOAL_THEN `&0 < r /\ r <= rU /\ r <= r1 / &2 /\ r <= rt` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s = ball(x0:real^3,r) PCROSS interval(lift(t0 - r),lift(t0 + r))` THEN
  ABBREV_TAC `kk = cball(x0:real^3,r) PCROSS interval[lift(t0 - r),lift(t0 + r)]` THEN
  SUBGOAL_THEN `open(s:real^(3,1)finite_sum->bool) /\ compact(kk:real^(3,1)finite_sum->bool) /\
                s SUBSET kk /\ kk SUBSET p2bw_cdom (c:(B->bool)#(B->real^3)) (&2 * t0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "kk"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_BALL; OPEN_INTERVAL];
      MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_CBALL; COMPACT_INTERVAL];
      MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[BALL_SUBSET_CBALL; INTERVAL_OPEN_SUBSET_CLOSED];
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; p2bw_cdom; IN_ELIM_THM;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`y:real^3`; `t:real^1`] THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `cball(x0:real^3,rU) SUBSET IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        UNDISCH_TAC `(y:real^3) IN cball(x0,r)` THEN REWRITE_TAC[IN_CBALL] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN s ==> dist(z,pastecart (x0:real^3) (lift t0)) < r1 /\
                   t0 - rt <= drop(sndcart z) /\ &0 < drop(sndcart z)`
  (LABEL_TAC "SB") THENL
   [EXPAND_TAC "s" THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_BALL; IN_INTERVAL_1; LIFT_DROP;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`y:real^3`; `t:real^1`] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[dist; PASTECART_SUB] THEN
    MP_TAC(ISPECL [`y - x0:real^3`; `t - lift t0`] NORM_PASTECART_LE) THEN
    REWRITE_TAC[NORM_1; DROP_SUB; LIFT_DROP] THEN
    UNDISCH_TAC `dist(x0:real^3,y) < r` THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^3,rU)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^3,r)` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
  (* the line bound *)
  MP_TAC(ISPECL [`s:real^(3,1)finite_sum->bool`;
                 `\z:real^(3,1)finite_sum. sqrt((L:real^(3,1)finite_sum->real) z + dl)`;
                 `{z:real^(3,1)finite_sum | z IN kk /\
                    ~((\w. lift((L:real^(3,1)finite_sum->real) w)) differentiable at z)}`;
                 `K * sqrt((y - x:real^3) dot (G0 ** (y - x)))`;
                 `pastecart (y - x:real^3) (vec 0:real^1)`;
                 `pastecart (x:real^3) (lift t0)`] P2BX_LINE_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_LOCLIP_SQRT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN EXPAND_TAC "L" THEN
        REWRITE_TAC[p2bw_cfun] THEN MATCH_MP_TAC P2BX_KLX_NONNEG THEN
        MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`] THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(z:real^(3,1)finite_sum) IN p2bw_cdom (c:(B->bool)#(B->real^3)) (&2 * t0)`
        MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[p2bw_cdom; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)) IN FST c`
        MP_TAC THENL [ASM_SIMP_TAC[]; ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
        UNDISCH_TAC `wan_loclip (p2bw_cdom (c:(B->bool)#(B->real^3)) (&2 * t0))
                                (L:real^(3,1)finite_sum->real)` THEN
        REWRITE_TAC[wan_loclip] THEN DISCH_TAC THEN
        X_GEN_TAC `k:real^(3,1)finite_sum->bool` THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `kk:real^(3,1)finite_sum->bool` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `s:real^(3,1)finite_sum->bool` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC P2BW_LOCLIP_AE_ON THEN
      EXISTS_TAC `p2bw_cdom (c:(B->bool)#(B->real^3)) (&2 * t0)` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN EXPAND_TAC "s" THEN
      REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD; PASTECART_IN_PCROSS; VECTOR_MUL_RZERO;
                  VECTOR_ADD_RID; IN_INTERVAL_1; LIFT_DROP] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `x + u % (y - x) = (&1 - u) % x + u % (y:real^3)` SUBST1_TAC THENL
       [VECTOR_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`x0:real^3`; `r:real`] CONVEX_BALL) THEN
      REWRITE_TAC[CONVEX_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(\w. lift((L:real^(3,1)finite_sum->real) w)) differentiable at z`
      MP_TAC THENL
       [UNDISCH_TAC `~((z:real^(3,1)finite_sum) IN
                       {z | z IN kk /\ ~((\w. lift((L:real^(3,1)finite_sum->real) w))
                                          differentiable at z)})` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[differentiable] THEN
      DISCH_THEN(X_CHOOSE_TAC `D:real^(3,1)finite_sum->real^1`) THEN
      USE_THEN "SB" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `(z:real^(3,1)finite_sum) IN p2bw_cdom (c:(B->bool)#(B->real^3)) (&2 * t0)`
      MP_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[p2bw_cdom; IN_ELIM_THM] THEN STRIP_TAC] THEN
      SUBGOAL_THEN `&0 <= (L:real^(3,1)finite_sum->real) z` ASSUME_TAC THENL
       [EXPAND_TAC "L" THEN REWRITE_TAC[p2bw_cfun] THEN MATCH_MP_TAC P2BX_KLX_NONNEG THEN
        MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`] THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)) IN FST c`
        MP_TAC THENL [ASM_SIMP_TAC[]; ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`L:real^(3,1)finite_sum->real`; `D:real^(3,1)finite_sum->real^1`;
                     `z:real^(3,1)finite_sum`; `dl:real`] P2BX_SQRT_DERIV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[differentiable] THEN
        FIRST_ASSUM(fun th -> EXISTS_TAC (rand(rator(concl th))) THEN ACCEPT_TAC th);
        ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[DROP_CMUL] THEN
      MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                     `c:(B->bool)#(B->real^3)`; `z:real^(3,1)finite_sum`;
                     `D:real^(3,1)finite_sum->real^1`] P2BX_CHART_DIFF_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `y - x:real^3` o CONJUNCT1)) THEN
      SUBGOAL_THEN `&0 <= mfd_scalar atlas ((g:real->B->real^3^3) (--(drop(sndcart z))))
                            (chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC P2BX_MFD_SCALAR_NONNEG THEN EXISTS_TAC `top:B topology` THEN
        SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)) IN
                      topspace top` ASSUME_TAC THENL
         [SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)) IN
                        FST c` MP_TAC THENL [ASM_SIMP_TAC[]; ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(y - x:real^3) dot (metric_local atlas (c:(B->bool)#(B->real^3))
                             ((g:real->B->real^3^3) (--(drop(sndcart z)))) (fstcart z) ** (y - x))
        <= (&1 + e1) * ((y - x) dot (G0 ** (y - x))) /\
        &0 <= (y - x:real^3) dot (metric_local atlas (c:(B->bool)#(B->real^3))
                             ((g:real->B->real^3^3) (--(drop(sndcart z)))) (fstcart z) ** (y - x))`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [SUBGOAL_THEN `metric_local atlas (c:(B->bool)#(B->real^3))
                          ((g:real->B->real^3^3) (--(drop(sndcart z)))) (fstcart z) =
                        (G:real^(3,1)finite_sum->real^3^3) z` SUBST1_TAC THENL
           [EXPAND_TAC "G" THEN REWRITE_TAC[p2bw_cmet; REAL_SUB_LZERO]; ALL_TAC] THEN
          FIRST_ASSUM(MP_TAC o SPEC `z:real^(3,1)finite_sum` o check
             (fun th -> can (find_term ((=) `e1:real`)) (concl th) && is_forall(concl th) &&
                        can (find_term ((=) `r1:real`)) (concl th))) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])];
          ASM_CASES_TAC `y - x:real^3 = vec 0` THEN
          ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN
          SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--(drop(sndcart(z:real^(3,1)finite_sum)))))`
          MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[riemannian_metric] THEN
          DISCH_THEN(MP_TAC o SPEC `c:(B->bool)#(B->real^3)`) THEN
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[metric_field] THEN
          DISCH_THEN(MP_TAC o SPEC `fstcart(z:real^(3,1)finite_sum)` o CONJUNCT2 o CONJUNCT2) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      DISCH_TAC THEN MATCH_MP_TAC P2BX_SQRT_BOUND_ARITH THEN
      EXISTS_TAC `drop(sndcart(z:real^(3,1)finite_sum))` THEN EXISTS_TAC `e1:real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c0 * norm(y - x:real^3) pow 2` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
          FIRST_ASSUM(MATCH_ACCEPT_TAC o SPEC `y - x:real^3` o check
            (fun th -> can (find_term ((=) `c0:real`)) (concl th) && is_forall(concl th)))];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(&3 * (L:real^(3,1)finite_sum->real) z / drop(sndcart z) -
                     mfd_scalar atlas ((g:real->B->real^3^3) (--(drop(sndcart z))))
                       (chart_inv (c:(B->bool)#(B->real^3)) (fstcart z))) *
                    ((y - x:real^3) dot (metric_local atlas c (g (--(drop(sndcart z))))
                                          (fstcart z) ** (y - x)))` THEN
        CONJ_TAC THENL
         [FIRST_ASSUM(ACCEPT_TAC o check (fun th ->
            can (find_term ((=) `D:real^(3,1)finite_sum->real^1`)) (concl th) &&
            can (find_term ((=) `pow`)) (concl th) &&
            not (can (find_term ((=) `e1:real`)) (concl th))));
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(&3 * (L:real^(3,1)finite_sum->real) z / drop(sndcart z)) *
                    ((y - x:real^3) dot (metric_local atlas (c:(B->bool)#(B->real^3))
                       ((g:real->B->real^3^3) (--(drop(sndcart z)))) (fstcart z) ** (y - x)))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
           [UNDISCH_TAC `&0 <= mfd_scalar atlas ((g:real->B->real^3^3) (--(drop(sndcart z))))
                            (chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)))` THEN
            REAL_ARITH_TAC;
            ASM_REWRITE_TAC[]];
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / (&4 * t0) + dt` THEN CONJ_TAC THENL
         [MATCH_MP_TAC P2BX_RATE_ARITH THEN EXISTS_TAC `rt:real` THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
          EXPAND_TAC "dt" THEN REAL_ARITH_TAC]]];
    REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_RID;
                VECTOR_ARITH `x + (y - x):real^N = y`] THEN
    EXPAND_TAC "L" THEN
    REWRITE_TAC[p2bw_cfun; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]);;

(* ========================================================================= *)
(* From local chart bounds to the manifold distance.  A function that is     *)
(* locally (K + e)-Lipschitz for the frozen chart norms, for every e > 0,    *)
(* satisfies h(gamma 1) - h(gamma 0) <= K length(gamma) along C^1 curves,    *)
(* hence h q - h q0 <= K d(q0,q).                                            *)
(* ========================================================================= *)

(* Locally nonincreasing on [0,1] implies f 1 <= f 0. *)

let P2BX_LOCAL_MONO = prove
 (`!f:real->real.
     (!s0. &0 <= s0 /\ s0 <= &1
           ==> ?d. &0 < d /\
                   !s s'. &0 <= s /\ s <= s' /\ s' <= &1 /\ abs(s - s0) < d /\
                          abs(s' - s0) < d
                          ==> f s' <= f s)
     ==> f(&1) <= f(&0)`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  MP_TAC(ISPEC `{s | &0 <= s /\ s <= &1 /\ (f:real->real) s <= f(&0)}` SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `&0` THEN
      REAL_ARITH_TAC;
      EXISTS_TAC `&1` THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `m = sup {s | &0 <= s /\ s <= &1 /\ (f:real->real) s <= f(&0)}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "UB") (LABEL_TAC "LUB")) THEN
  SUBGOAL_THEN `&0 <= m /\ m <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "UB" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      USE_THEN "LUB" MATCH_MP_TAC THEN SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "H" (MP_TAC o SPEC `m:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LOC"))) THEN
  SUBGOAL_THEN `?s1. &0 <= s1 /\ s1 <= &1 /\ (f:real->real) s1 <= f(&0) /\ m - d < s1 /\ s1 <= m`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?s1. &0 <= s1 /\ s1 <= &1 /\ (f:real->real) s1 <= f(&0) /\ m - d < s1`
    THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s1:real` THEN ASM_REWRITE_TAC[] THEN USE_THEN "UB" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      USE_THEN "LUB" (MP_TAC o SPEC `m - d:real`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[REAL_NOT_LT]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s'. s1 <= s' /\ s' <= &1 /\ s' < m + d ==> (f:real->real) s' <= f(&0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:real->real) s1` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "LOC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `m = &1` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "UB" (MP_TAC o SPEC `min (&1) (m + d / &2)`) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* The increment of a C^1 curve in a chart, measured by a linear map M      *)
(* dominated by B times the metric norm along the curve, is at most B times *)
(* the length of the curve piece.                                            *)

let P2BX_CHART_INCR_LE_LENGTH = prove
 (`!top atlas (g:A->real^N^N) gamma c s s' (M:real^N^N) B.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ c IN atlas /\
     &0 <= s /\ s <= s' /\ s' <= &1 /\
     (!u. s <= u /\ u <= s' ==> gamma u IN FST c) /\
     (!u w. s <= u /\ u <= s'
            ==> norm(M ** w) <=
                B * sqrt(w dot (metric_local atlas c g (SND c (gamma u)) ** w)))
     ==> norm(M ** (SND c (gamma s') - SND c (gamma s))) <=
         B * mfd_length atlas g gamma s s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `ff = \t:real^1. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) (drop t))` THEN
  ABBREV_TAC `vv = \t:real^1. vector_derivative (ff:real^1->real^N)
                                (at t within interval[lift(&0),lift(&1)])` THEN
  SUBGOAL_THEN
   `((vv:real^1->real^N) has_integral (ff(lift s') - ff(lift s))) (interval[lift s,lift s'])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `interval[lift(&0),lift(&1)]` THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["vv"; "ff"] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `gamma:real->A`; `&0`; `&1`; `c:(A->bool)#(A->real^N)`; `drop t`]
             GRGD_C1_CHART_HAS_VD) THEN
      ASM_REWRITE_TAC[LIFT_DROP; IN_REAL_INTERVAL] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        SIMP_TAC[]];
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_speed atlas (g:A->real^N^N) gamma (&0) (&1) real_integrable_on
                real_interval[s,s']` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
    CONJ_TAC THENL [MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN
                    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^N^N) gamma s s' =
                real_integral (real_interval[s,s']) (mfd_speed atlas g gamma (&0) (&1))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC GRGD_LENGTH_SUBINTERVAL THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; IMAGE_LIFT_REAL_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL]) THEN
  SUBGOAL_THEN
   `(M:real^N^N) ** ((ff:real^1->real^N) (lift s') - ff(lift s)) =
    integral (interval[lift s,lift s']) (\t. M ** (vv:real^1->real^N) t)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MP_TAC(ISPECL [`vv:real^1->real^N`; `(ff:real^1->real^N) (lift s') - ff(lift s)`;
                   `interval[lift s,lift s']`; `\x:real^N. (M:real^N^N) ** x`]
                  HAS_INTEGRAL_LINEAR) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) s') - SND c (gamma s) =
                (ff:real^1->real^N) (lift s') - ff(lift s)` SUBST1_TAC THENL
   [EXPAND_TAC "ff" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `B * drop(integral (interval[lift s,lift s'])
                (lift o mfd_speed atlas (g:A->real^N^N) gamma (&0) (&1) o drop)) =
    drop(integral (interval[lift s,lift s'])
           (\t. B % (lift o mfd_speed atlas g gamma (&0) (&1) o drop) t))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`lift o mfd_speed atlas (g:A->real^N^N) gamma (&0) (&1) o drop`; `B:real`;
                   `interval[lift s,lift s']`] INTEGRAL_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[integrable_on] THEN
    EXISTS_TAC `(M:real^N^N) ** ((ff:real^1->real^N) (lift s') - ff(lift s))` THEN
    MP_TAC(ISPECL [`vv:real^1->real^N`; `(ff:real^1->real^N) (lift s') - ff(lift s)`;
                   `interval[lift s,lift s']`; `\x:real^N. (M:real^N^N) ** x`]
                  HAS_INTEGRAL_LINEAR) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; o_DEF];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM; DROP_CMUL; LIFT_DROP] THEN
    SUBGOAL_THEN `mfd_speed atlas (g:A->real^N^N) gamma (&0) (&1) (drop t) =
                  sqrt((vv:real^1->real^N) t dot
                       (metric_local atlas (c:(A->bool)#(A->real^N)) g (SND c (gamma(drop t))) **
                        vv t))`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["vv"; "ff"] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`; `drop t`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                    MFD_SPEED_CHART) THEN
      ASM_REWRITE_TAC[PAIR; IN_REAL_INTERVAL; LIFT_DROP; REAL_LT_01] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        SIMP_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* The frozen norm of a metric field at a point, as the norm of M w. *)

let P2BX_FROZEN_NORM = prove
 (`!(M:real^N^N) G0 w.
     G0 = transp M ** M ==> sqrt(w dot (G0 ** w)) = norm(M ** w)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL; GSYM NORM_POW_2] THEN
  MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[NORM_POS_LE]);;

(* The local step of the curve estimate at s0. *)

let P2BX_LIP_LOCAL_STEP = prove
 (`!top atlas (g:A->real^N^N) (h:A->real) K gamma e s0.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 <= K /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ &0 < e /\ &0 <= s0 /\ s0 <= &1 /\
     (!c x0 K'. c IN atlas /\ x0 IN IMAGE (SND c) (FST c) /\ K < K'
                ==> ?r. &0 < r /\ ball(x0,r) SUBSET IMAGE (SND c) (FST c) /\
                        !x y. x IN ball(x0,r) /\ y IN ball(x0,r)
                              ==> h(chart_inv c y) - h(chart_inv c x) <=
                                  K' * sqrt((y - x) dot (metric_local atlas c g x0 ** (y - x))))
     ==> ?d. &0 < d /\
             !s s'. &0 <= s /\ s <= s' /\ s' <= &1 /\ abs(s - s0) < d /\ abs(s' - s0) < d
                    ==> h(gamma s') - h(gamma s) <=
                        ((K + e) * (&1 + e)) * mfd_length atlas g gamma s s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LOC")))))))) THEN
  SUBGOAL_THEN `(gamma:real->A) s0 IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `&0`; `&1`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) s0`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) s0)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x0 = SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) s0)` THEN
  SUBGOAL_THEN `(x0:real^N) IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                             (metric_local atlas c (g:A->real^N^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  USE_THEN "LOC" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `x0:real^N`; `K + e:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rh:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RH")))) THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `x0:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "FN" o MATCH_MP P2BX_FROZEN_NORM))) THEN
  MP_TAC(ASSUME `open(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`) THEN
  REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `x0:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rU:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `cball(x0:real^N,rU)`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[PAIR; COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GB"))))) THEN
  ABBREV_TAC `ee = (&1 + e) pow 2 - &1` THEN
  SUBGOAL_THEN `&0 < ee` ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN REWRITE_TAC[REAL_ARITH `(&1 + e) pow 2 - &1 = e * (e + &2)`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ee` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < ee` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* continuity of the chart metric at x0 *)
  SUBGOAL_THEN
   `?r2. &0 < r2 /\
         !p. dist(p,x0) < r2
             ==> !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                       ==> abs(metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) x0$i$j -
                               metric_local atlas c g p$i$j) <=
                           c1 * ee / &(dimindex(:N)) pow 2`
  (X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R2"))) THENL
   [SUBGOAL_THEN `(\p. (vectorize:real^N^N->real^(N,N)finite_prod)
                         (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) p))
                  continuous at x0` MP_TAC THENL
     [SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o
                     metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                    continuous_on IMAGE (SND c) (FST c)` ASSUME_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN ASM_MESON_TAC[metric_field];
        ALL_TAC] THEN
      SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o
                     metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                    continuous at x0` MP_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]; REWRITE_TAC[o_DEF]];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN
    DISCH_THEN(MP_TAC o SPEC `c1 * ee / &(dimindex(:N)) pow 2`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
      SIMP_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> 0 < n`];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r2:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((vectorize:real^N^N->real^(N,N)finite_prod)
                      (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) p) -
                     vectorize (metric_local atlas c g x0))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM VECTORIZE_SUB] THEN
      ASM_SIMP_TAC[GSYM MATRIX_SUB_COMPONENT; P2BX_ENTRY_LE_VECTORIZE];
      FIRST_X_ASSUM(MP_TAC o SPEC `p:real^N`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[dist] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `rr = min rh (min rU r2)` THEN
  SUBGOAL_THEN `&0 < rr` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  (* the frozen norm is dominated near x0 *)
  SUBGOAL_THEN
   `!p w. p IN ball(x0:real^N,rr)
          ==> norm((M:real^N^N) ** w) <=
              (&1 + e) * sqrt(w dot (metric_local atlas (c:(A->bool)#(A->real^N))
                                       (g:A->real^N^N) p ** w))`
  (LABEL_TAC "NB") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^N) IN cball(x0,rU) /\ dist(p,x0) < r2` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^N) IN ball(x0,rr)` THEN EXPAND_TAC "rr" THEN
      REWRITE_TAC[IN_BALL; IN_CBALL; REAL_LT_MIN] THEN
      MP_TAC(ISPECL [`p:real^N`; `x0:real^N`] DIST_SYM) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!v. c1 * norm(v:real^N) pow 2 <=
                      v dot (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) p ** v)`
    ASSUME_TAC THENL
     [X_GEN_TAC `v:real^N` THEN USE_THEN "GB" (MP_TAC o SPECL [`p:real^N`; `v:real^N`]) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `w dot (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) x0 ** w) <=
                  (&1 + ee) * (w dot (metric_local atlas c g p ** w))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) p`;
                     `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) x0`;
                     `c1:real`; `ee:real`] P2BX_QUAD_NEAR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "R2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= w dot (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) p ** w)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c1 * norm(w:real^N) pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN UNDISCH_TAC `&0 < c1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= w dot (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) x0 ** w)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c1 * norm(w:real^N) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        UNDISCH_TAC `&0 < c1` THEN REAL_ARITH_TAC;
        USE_THEN "GB" (MP_TAC o SPECL [`x0:real^N`; `w:real^N`]) THEN
        REWRITE_TAC[CENTRE_IN_CBALL] THEN ANTS_TAC THENL
         [UNDISCH_TAC `&0 < rU` THEN REAL_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    USE_THEN "FN" (fun th -> REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt((&1 + ee) * (w dot (metric_local atlas (c:(A->bool)#(A->real^N))
                                           (g:A->real^N^N) p ** w)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&1 + ee = (&1 + e) pow 2` SUBST1_TAC THENL
     [EXPAND_TAC "ee" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC POW_2_SQRT THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the curve window around s0 *)
  SUBGOAL_THEN `open_in top {z | z IN FST (c:(A->bool)#(A->real^N)) /\
                                 SND c z IN ball(x0:real^N,rr)}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `ball(x0:real^N,rr)`] GRGD_CHART_PREIMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR; OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `gamma:real->A`;
                 `&0`; `&1`;
                 `{z | z IN FST (c:(A->bool)#(A->real^N)) /\ SND c z IN ball(x0:real^N,rr)}`;
                 `s0:real`] GRGD_CURVE_TIMES_BALL) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM; CENTRE_IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "WIN"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `s':real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u. s <= u /\ u <= s'
                    ==> (gamma:real->A) u IN FST (c:(A->bool)#(A->real^N)) /\
                        SND c (gamma u) IN ball(x0:real^N,rr)` (LABEL_TAC "INW") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    USE_THEN "WIN" (MP_TAC o SPEC `lift u`) THEN
    REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1; DIST_LIFT] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `abs(s - s0) < d` THEN UNDISCH_TAC `abs(s' - s0) < d` THEN
    UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `s' <= &1` THEN
    UNDISCH_TAC `s <= u` THEN UNDISCH_TAC `u <= s'` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "INW" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  USE_THEN "INW" (MP_TAC o SPEC `s':real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) s) IN ball(x0:real^N,rh) /\
                SND c (gamma s') IN ball(x0,rh)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) s) IN ball(x0:real^N,rr)` THEN
    UNDISCH_TAC `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) s') IN ball(x0:real^N,rr)` THEN
    EXPAND_TAC "rr" THEN REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `h((gamma:real->A) s') - h(gamma s) <=
    (K + e) * norm((M:real^N^N) ** (SND (c:(A->bool)#(A->real^N)) (gamma s') - SND c (gamma s)))`
  MP_TAC THENL
   [USE_THEN "RH" (MP_TAC o SPECL [`SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) s)`;
                                   `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) s')`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "FN" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c ((gamma:real->A) s)) = gamma s /\
                  chart_inv c (SND c (gamma s')) = gamma s'` (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c:real. b <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [UNDISCH_TAC `&0 <= K` THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
                  ALL_TAC] THEN
  MATCH_MP_TAC P2BX_CHART_INCR_LE_LENGTH THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN USE_THEN "INW" (MP_TAC o SPEC `u:real`) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real`; `w:real^N`] THEN STRIP_TAC THEN
    USE_THEN "NB" MATCH_MP_TAC THEN USE_THEN "INW" (MP_TAC o SPEC `u:real`) THEN
    ASM_SIMP_TAC[]]);;

(* Letting e tend to 0 in D <= (K + e)(1 + e) L. *)

let P2BX_LIMIT_ARITH = prove
 (`!D K L. &0 <= K /\ &0 <= L /\ (!e. &0 < e ==> D <= ((K + e) * (&1 + e)) * L)
           ==> D <= K * L`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (K + &2) * L + &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!x. &0 <= x ==> &0 < x + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = (D - K * L) / (&2 * ((K + &2) * L + &1))` THEN
  SUBGOAL_THEN `&0 < q /\ q * ((K + &2) * L + &1) = (D - K * L) / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < (K + &2) * L + &1` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC `e = min (&1) q` THEN
  SUBGOAL_THEN `&0 < e /\ e <= &1 /\ e <= q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= e * L * (&1 - e) /\ &0 <= e /\
                e * ((K + &2) * L + &1) <= q * ((K + &2) * L + &1)` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `K * L < D` THEN REAL_ARITH_TAC);;

(* Along a C^1 curve, a locally (K + e)-Lipschitz function (frozen chart    *)
(* norms, every e > 0) increases by at most K times the length.             *)

let P2BX_DIST_LIP_CURVE = prove
 (`!top atlas (g:A->real^N^N) (h:A->real) K gamma.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 <= K /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     (!c x0 K'. c IN atlas /\ x0 IN IMAGE (SND c) (FST c) /\ K < K'
                ==> ?r. &0 < r /\ ball(x0,r) SUBSET IMAGE (SND c) (FST c) /\
                        !x y. x IN ball(x0,r) /\ y IN ball(x0,r)
                              ==> h(chart_inv c y) - h(chart_inv c x) <=
                                  K' * sqrt((y - x) dot (metric_local atlas c g x0 ** (y - x))))
     ==> h(gamma(&1)) - h(gamma(&0)) <= K * mfd_length atlas g gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BX_LIMIT_ARITH THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\s. (h:A->real)((gamma:real->A) s) -
                    ((K + e) * (&1 + e)) * mfd_length atlas (g:A->real^N^N) gamma (&0) s`
         P2BX_LOCAL_MONO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `s0:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `h:A->real`; `K:real`; `gamma:real->A`; `e:real`;
                   `s0:real`] P2BX_LIP_LOCAL_STEP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`s:real`; `s':real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) s' =
                  mfd_length atlas g gamma (&0) s + mfd_length atlas g gamma s s'`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `&0`; `s':real`; `&1`]
             MFD_LENGTH_COMBINE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `&0`; `s:real`; `s':real`]
             MFD_LENGTH_COMBINE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `s':real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) (&0) = &0`
  SUBST1_TAC THENL [REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL]; REAL_ARITH_TAC]);;

(* The manifold distance version. *)

let P2BX_DIST_LIP = prove
 (`!top atlas (g:A->real^N^N) (h:A->real) K q0 q.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 <= K /\
     mfd_joinable (top,atlas) q0 q /\
     (!c x0 K'. c IN atlas /\ x0 IN IMAGE (SND c) (FST c) /\ K < K'
                ==> ?r. &0 < r /\ ball(x0,r) SUBSET IMAGE (SND c) (FST c) /\
                        !x y. x IN ball(x0,r) /\ y IN ball(x0,r)
                              ==> h(chart_inv c y) - h(chart_inv c x) <=
                                  K' * sqrt((y - x) dot (metric_local atlas c g x0 ** (y - x))))
     ==> h q - h q0 <= K * mfd_dist (top,atlas) g q0 q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gamma0:real->A` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [mfd_joinable]) THEN
  SUBGOAL_THEN
   `!gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = q0 /\ gamma(&1) = q
            ==> (h:A->real) q - h q0 <= K * mfd_length atlas (g:A->real^N^N) gamma (&0) (&1)`
  (LABEL_TAC "CU") THENL
   [X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `h:A->real`; `K:real`; `gamma:real->A`]
           P2BX_DIST_LIP_CURVE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `K = &0` THENL
   [USE_THEN "CU" (MP_TAC o SPEC `gamma0:real->A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^N^N) (gamma0:real->A) (&0) (&1)` THEN
    EXISTS_TAC `gamma0:real->A` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    USE_THEN "CU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Subadditivity of the square root. *)

let P2BX_SQRT_ADD_LE = prove
 (`!a b. &0 <= a /\ &0 <= b ==> sqrt(a + b) <= sqrt a + sqrt b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
  ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_ADD] THEN
  REWRITE_TAC[REAL_ARITH `(x + y) pow 2 = x pow 2 + y pow 2 + &2 * x * y`] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c. &0 <= c ==> a + b <= a + b + &2 * c`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE]);;

(* MT Cor 9.10, the spatial bound: sqrt l is sqrt(3/(4t))-Lipschitz for the *)
(* distance of g(-t).                                                       *)

let P2BX_C910_SPATIAL = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p t q0 q.
     P2B_REQ_P2A_WEAK_STATEMENT w /\ P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\
     P2A_FLOW_MIN_EXISTS_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\
     &0 < t /\ q0 IN topspace top /\ q IN topspace top
     ==> sqrt(p2b_klx (top,atlas) g p t q) <=
         sqrt(p2b_klx (top,atlas) g p t q0) +
         sqrt(&3 / (&4 * t)) * mfd_dist (top,atlas) (g(--t)) q0 q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W3") (CONJUNCTS_THEN2 (LABEL_TAC "FL8")
    (CONJUNCTS_THEN2 (LABEL_TAC "FL2") STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `&0 <= sqrt(&3 / (&4 * t)) /\ sqrt(&3 / (&4 * t)) pow 2 = &3 / (&4 * t)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &3 / (&4 * t)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `K = sqrt(&3 / (&4 * t))` THEN
  SUBGOAL_THEN `&0 <= p2b_klx (top,atlas) (g:real->B->real^3^3) p t q /\
                &0 <= p2b_klx (top,atlas) g p t q0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2BX_KLX_NONNEG THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (q0:B) q` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (--t))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!dl. &0 < dl
         ==> sqrt(p2b_klx (top,atlas) (g:real->B->real^3^3) p t q + dl) -
             sqrt(p2b_klx (top,atlas) g p t q0 + dl) <=
             K * mfd_dist (top,atlas) (g(--t)) q0 q`
  (LABEL_TAC "DL") THENL
   [X_GEN_TAC `dl:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (--t)`;
                   `\y:B. sqrt(p2b_klx (top,atlas) (g:real->B->real^3^3) p t y + dl)`;
                   `K:real`; `q0:B`; `q:B`] P2BX_DIST_LIP) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`c:(B->bool)#(B->real^3)`; `x0:real^3`; `K':real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BX_SQRT_CHART_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `&0 <= K` THEN UNDISCH_TAC `K < K'` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_THEN `K pow 2 = &3 / (&4 * t)` (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `lq = p2b_klx (top,atlas) (g:real->B->real^3^3) p t q` THEN
  ABBREV_TAC `lq0 = p2b_klx (top,atlas) (g:real->B->real^3^3) p t q0` THEN
  ABBREV_TAC `dd = mfd_dist (top,atlas) ((g:real->B->real^3^3) (--t)) q0 q` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `ee = (sqrt lq - (sqrt lq0 + K * dd)) / &2` THEN
  SUBGOAL_THEN `&0 < ee /\ sqrt lq0 + K * dd + &2 * ee = sqrt lq` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN UNDISCH_TAC `sqrt lq0 + K * dd < sqrt lq` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "DL" (MP_TAC o SPEC `ee pow 2`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt lq <= sqrt(lq + ee pow 2)` MP_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[REAL_LE_ADDR; REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lq0 + ee pow 2) <= sqrt lq0 + ee` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt lq0 + sqrt(ee pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_SQRT_ADD_LE THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < ee` THEN UNDISCH_TAC `sqrt lq0 + K * dd + &2 * ee = sqrt lq` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The pointwise bounds of MT Cor 9.10 and the route theorem.  R <= 3 l / t  *)
(* everywhere (almost everywhere from FL8 in a chart, then continuity of R   *)
(* and l), the monotonicity of t^2 l and l / t at points, and the assembly   *)
(* of P2B_COR_9_10_STATEMENT.                                                *)
(* ========================================================================= *)

(* R <= 3 l / t at every chart point. *)

let P2BX_SCALAR_CHART = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p c x t.
     P2B_REQ_P2A_WEAK_STATEMENT w /\ P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\
     P2A_FLOW_MIN_EXISTS_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ c IN atlas /\
     x IN IMAGE (SND c) (FST c) /\ &0 < t
     ==> mfd_scalar atlas (g(--t)) (chart_inv c x) <=
         &3 * p2bw_cfun c (p2b_klx (top,atlas) g p) (pastecart x (lift t)) / t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W3") (CONJUNCTS_THEN2 (LABEL_TAC "FL8")
    (CONJUNCTS_THEN2 (LABEL_TAC "FL2") STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  ABBREV_TAC `L = p2bw_cfun (c:(B->bool)#(B->real^3))
                    (p2b_klx (top,atlas) (g:real->B->real^3^3) p)` THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `c:(B->bool)#(B->real^3)`; `t + &2`] P2BX_W3_CHART) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `open(IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))`) THEN
  REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `kk = cball(x:real^3,r) PCROSS interval[lift(t / &2),lift(t + &1)]` THEN
  ABBREV_TAC `s = ball(x:real^3,r) PCROSS interval(lift(t / &2),lift(t + &1))` THEN
  SUBGOAL_THEN `compact(kk:real^(3,1)finite_sum->bool) /\ open(s:real^(3,1)finite_sum->bool) /\
                s SUBSET kk /\ kk SUBSET p2bw_cdom (c:(B->bool)#(B->real^3)) (t + &2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["kk"; "s"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_CBALL; COMPACT_INTERVAL];
      MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_BALL; OPEN_INTERVAL];
      MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[BALL_SUBSET_CBALL; INTERVAL_OPEN_SUBSET_CLOSED];
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; p2bw_cdom; IN_ELIM_THM;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
      REPEAT STRIP_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^(3,1)finite_sum. z IN s ==> &0 < drop(sndcart z)`
  (LABEL_TAC "TB") THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                                    SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `n = {z | z IN kk /\ ~((\y. lift((L:real^(3,1)finite_sum->real) y)) differentiable at z)}` THEN
  SUBGOAL_THEN `negligible(n:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN MATCH_MP_TAC P2BW_LOCLIP_AE_ON THEN
    EXISTS_TAC `p2bw_cdom (c:(B->bool)#(B->real^3)) (t + &2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BX_CDOM_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_loclip (s:real^(3,1)finite_sum->bool) L` ASSUME_TAC THENL
   [UNDISCH_TAC `wan_loclip (p2bw_cdom (c:(B->bool)#(B->real^3)) (t + &2))
                            (L:real^(3,1)finite_sum->real)` THEN
    REWRITE_TAC[wan_loclip] THEN DISCH_TAC THEN X_GEN_TAC `k:real^(3,1)finite_sum->bool` THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `kk:real^(3,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `s:real^(3,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (--(t + &2)) (&0) (g:real->B->real^3^3)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `p2a_cbflow (top,atlas) (--(t + &2)) (&0) (g:real->B->real^3^3)` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; SIMP_TAC[p2a_cbflow; ricci_flow_from]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^(3,1)finite_sum->bool`;
                 `\z. p2bw_cscal atlas (c:(B->bool)#(B->real^3)) (&0) (g:real->B->real^3^3) z`;
                 `\z:real^(3,1)finite_sum. &3 * (L:real^(3,1)finite_sum->real) z / drop(sndcart z)`;
                 `n:real^(3,1)finite_sum->bool`] P2BX_AE_LE_CONT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `p2bw_cdom (c:(B->bool)#(B->real^3)) (t + &2)` THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `--(t + &2)`;
                       `&0`; `g:real->B->real^3^3`; `c:(B->bool)#(B->real^3)`]
          (REWRITE_RULE[P2B_FLOW_CHART_STATEMENT]
            (ISPECL [`w:B->bool`; `(:3)`] P2B_FLOW_CHART))) THEN
        ASM_REWRITE_TAC[REAL_ARITH `&0 - --(t + &2) = t + &2`] THEN
        DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS o CONJUNCT1 o CONJUNCT2) THEN
        REWRITE_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `kk:real^(3,1)finite_sum->bool` THEN
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(\z:real^(3,1)finite_sum. lift(&3 * (L:real^(3,1)finite_sum->real) z /
                                                    drop(sndcart z))) =
                    (\z. inv(drop(sndcart z)) % lift(&3 * L z))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL] THEN GEN_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC P2BW_CONT_TAU_INV THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^(3,1)finite_sum) IN kk /\
                    z IN p2bw_cdom (c:(B->bool)#(B->real^3)) (t + &2)`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(\y. lift((L:real^(3,1)finite_sum->real) y)) differentiable at z` MP_TAC THENL
       [UNDISCH_TAC `~((z:real^(3,1)finite_sum) IN n)` THEN EXPAND_TAC "n" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[differentiable] THEN
      DISCH_THEN(X_CHOOSE_TAC `D:real^(3,1)finite_sum->real^1`) THEN
      UNDISCH_TAC `(z:real^(3,1)finite_sum) IN p2bw_cdom (c:(B->bool)#(B->real^3)) (t + &2)` THEN
      REWRITE_TAC[p2bw_cdom; IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                     `c:(B->bool)#(B->real^3)`; `z:real^(3,1)finite_sum`;
                     `D:real^(3,1)finite_sum->real^1`] P2BX_CHART_DIFF_BOUNDS) THEN
      ASM_REWRITE_TAC[p2bw_cscal; REAL_SUB_LZERO] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (x:real^3) (lift t)`) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "s" THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; CENTRE_IN_BALL; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2bw_cscal; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; REAL_SUB_LZERO]);;

(* The pointwise bounds at manifold points (chart at q). *)

let P2BX_C910_POINT = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p.
     P2B_REQ_P2A_WEAK_STATEMENT w /\ P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\
     P2A_FLOW_MIN_EXISTS_STATEMENT w (:3) /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top
     ==> (!t q. &0 < t /\ q IN topspace top
                ==> mfd_scalar atlas (g(--t)) q <= &3 * p2b_klx (top,atlas) g p t q / t) /\
         (!q t1 t2. q IN topspace top /\ &0 < t1 /\ t1 <= t2
                    ==> t1 pow 2 * p2b_klx (top,atlas) g p t1 q <=
                        t2 pow 2 * p2b_klx (top,atlas) g p t2 q /\
                        t1 * p2b_klx (top,atlas) g p t2 q <=
                        t2 * p2b_klx (top,atlas) g p t1 q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN
   `!q. q IN topspace top
        ==> chart_at atlas q IN atlas /\
            SND (chart_at (atlas:((B->bool)#(B->real^3))->bool) (q:B)) q IN
            IMAGE (SND (chart_at atlas q)) (FST (chart_at atlas q)) /\
            chart_inv (chart_at atlas q) (SND (chart_at atlas q) q) = q`
  (LABEL_TAC "CQ") THENL
   [X_GEN_TAC `q:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `q:B`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `chart_at (atlas:((B->bool)#(B->real^3))->bool) (q:B)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `q:B`] THEN STRIP_TAC THEN
    USE_THEN "CQ" (MP_TAC o SPEC `q:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                   `chart_at (atlas:((B->bool)#(B->real^3))->bool) (q:B)`;
                   `SND (chart_at (atlas:((B->bool)#(B->real^3))->bool) (q:B)) q`; `t:real`]
                  P2BX_SCALAR_CHART) THEN
    ASM_REWRITE_TAC[p2bw_cfun; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    MAP_EVERY X_GEN_TAC [`q:B`; `t1:real`; `t2:real`] THEN STRIP_TAC THEN
    USE_THEN "CQ" (MP_TAC o SPEC `q:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                   `chart_at (atlas:((B->bool)#(B->real^3))->bool) (q:B)`;
                   `SND (chart_at (atlas:((B->bool)#(B->real^3))->bool) (q:B)) q`;
                   `t1:real`; `t2:real`] P2BX_TIME_MONO_CHART) THEN
    ASM_REWRITE_TAC[p2bw_cfun; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]);;

(* The route theorem of MT Cor 9.10. *)

let P2B_COR_9_10_ROUTE = prove
 (`!w:B->bool. P2B_COR_9_10_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_COR_9_10_ROUTE_STATEMENT; P2B_COR_9_10_STATEMENT] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `p:B`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`]
                P2BX_C910_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SC") (LABEL_TAC "MO")) THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `q:B`] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_KLX_NONNEG THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`] THEN ASM_REWRITE_TAC[];
      USE_THEN "SC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `q0:B`; `q:B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BX_C910_SPATIAL THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`q:B`; `t1:real`; `t2:real`] THEN STRIP_TAC THEN
    USE_THEN "MO" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

