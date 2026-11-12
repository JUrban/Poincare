(* ========================================================================= *)
(* pc_p2b_parfield: the limit parallel field of SPLIT_ROUND,                 *)
(* P2BPL_LIMIT_FIELD |- !u w. P2BPL_LIMIT_FIELD_STATEMENT u w (statement in  *)
(* pc_p2b_parfieldreq): unit parallel fields on the slices of a slice limit  *)
(* give, along a subsequence, a unit parallel field on the limit with C^0    *)
(* convergence in the g0 norm, uniformly on compact sets.  Proof: pull the   *)
(* fields back to the limit, bound them and their derivatives on chart balls *)
(* through the Christoffel symbols, extract a diagonal subsequence           *)
(* (Arzela-Ascoli) and pass to the limit in the parallel equation            *)
(* (HAS_DERIVATIVE_SEQUENCE).                                                *)
(* ========================================================================= *)

needs "src/pc_p2b_parfieldreq.ml";;
needs "src/pc_p2b_parlim.ml";;
needs "src/pc_p2b_parons.ml";;
needs "src/pc_p2c_cgsub.ml";;
needs "src/pc_rfa_split.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Naturality of the parallel equation under a diffeomorphism of open sets   *)
(* of real^N: the pulled-back field (D h)^-1 (V o h) is smooth and parallel  *)
(* for the pullback metric.                                                  *)
(* ========================================================================= *)

let P2BPF_PAR_EUCLID = prove
 (`!U U' (h:real^N->real^N) h' (G:real^N->real^N^N) (V:real^N->real^N) (Wf:real^N->real^N).
     metric_field U G /\ diffeomorphism_on U' U h h' /\ smooth_map_on U V /\
     (!y z. y IN U ==> frechet_derivative V (at y) z + christoffel G y z (V y) = vec 0) /\
     (!u. u IN U' ==> Wf u = frechet_derivative h' (at (h u)) (V (h u)))
     ==> smooth_map_on U' Wf /\
         !u z. u IN U'
               ==> frechet_derivative Wf (at u) z +
                   christoffel (mpullback h G) u z (Wf u) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN
   `!x. x IN U'
        ==> (h:real^N->real^N) x IN U /\ linear(frechet_derivative h (at x)) /\
            frechet_derivative h (at x) ((Wf:real^N->real^N) x) = (V:real^N->real^N) (h x) /\
            (!w. frechet_derivative (h':real^N->real^N) (at (h x))
                   (frechet_derivative h (at x) w) = w) /\
            (!w. frechet_derivative h (at x) (frechet_derivative h' (at (h x)) w) = w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `x:real^N`] LRG_DIFFEO_DERIV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> linear(frechet_derivative (h':real^N->real^N) (at y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_DIFFEO_LINEAR_AT THEN
    MAP_EVERY EXISTS_TAC [`U':real^N->bool`; `U:real^N->bool`; `h:real^N->real^N`] THEN
    ASM_SIMP_TAC[DIFFEOMORPHISM_ON_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U' (Wf:real^N->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\u. matrix(frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) u))) **
                    (V:real^N->real^N) (h u)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[MATRIX_WORKS];
      MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `(vectorize:real^N^N->real^(N,N)finite_prod) o
          (\u. matrix(frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) u)))) =
          ((vectorize:real^N^N->real^(N,N)finite_prod) o
           (\z. matrix(frechet_derivative h' (at z)))) o h`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_SIMP_TAC[LRG_SMOOTH_JACOBIAN; SUBSET_REFL];
        SUBGOAL_THEN `(\u. (V:real^N->real^N) ((h:real^N->real^N) u)) = V o h` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[SUBSET_REFL]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`u:real^N`; `z:real^N`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `u:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `Wf:real^N->real^N`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "linear")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `((\x. frechet_derivative (h:real^N->real^N) (at x) ((Wf:real^N->real^N) x)) has_derivative
     (\v. frechet_derivative h (at u) (frechet_derivative Wf (at u) v) +
          frechet_derivative (\x. frechet_derivative h (at x) (Wf u)) (at u) v)) (at u)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. frechet_derivative (h:real^N->real^N) (at x)`; `Wf:real^N->real^N`;
                   `frechet_derivative (Wf:real^N->real^N) (at u)`; `U':real^N->bool`; `u:real^N`]
           LRG_HAS_DERIVATIVE_LINFAM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC LRG_DIFFEO_LINEAR_AT THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`; `u:real^N`; `basis i:real^N`]
             LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`U':real^N->bool`; `Wf:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. (V:real^N->real^N) ((h:real^N->real^N) x)) has_derivative
     (\v. frechet_derivative V (at (h u)) (frechet_derivative h (at u) v))) (at u)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. (V:real^N->real^N) ((h:real^N->real^N) x)) = V o h` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. frechet_derivative (V:real^N->real^N) (at ((h:real^N->real^N) u))
             (frechet_derivative h (at u) v)) =
      frechet_derivative V (at (h u)) o frechet_derivative h (at u)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (h:real^N->real^N) (at u) (frechet_derivative (Wf:real^N->real^N) (at u) z) +
    dd2 h u z (Wf u) =
    frechet_derivative (V:real^N->real^N) (at (h u)) (frechet_derivative h (at u) z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[dd2] THEN
    MP_TAC(ISPECL
     [`\x. frechet_derivative (h:real^N->real^N) (at x) ((Wf:real^N->real^N) x)`;
      `\x. (V:real^N->real^N) ((h:real^N->real^N) x)`;
      `\v. frechet_derivative (h:real^N->real^N) (at u) (frechet_derivative (Wf:real^N->real^N) (at u) v) +
           frechet_derivative (\x. frechet_derivative h (at x) (Wf u)) (at u) v`;
      `\v. frechet_derivative (V:real^N->real^N) (at ((h:real^N->real^N) u))
             (frechet_derivative h (at u) v)`;
      `U':real^N->bool`; `u:real^N`] LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Wf:real^N->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "linear")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C AP_THM `z:real^N`) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (h:real^N->real^N) (at u)
      (frechet_derivative (Wf:real^N->real^N) (at u) z +
       christoffel (mpullback h (G:real^N->real^N^N)) u z (Wf u)) = vec 0`
  MP_TAC THENL
   [MP_TAC(ISPECL [`frechet_derivative (h:real^N->real^N) (at u)`;
                   `frechet_derivative (Wf:real^N->real^N) (at u) z`;
                   `christoffel (mpullback (h:real^N->real^N) (G:real^N->real^N^N)) u z
                      ((Wf:real^N->real^N) u)`] LINEAR_ADD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`; `h':real^N->real^N`;
                   `G:real^N->real^N^N`; `u:real^N`; `z:real^N`; `(Wf:real^N->real^N) u`]
           LCHRISTOFFEL_PULLBACK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`(h:real^N->real^N) u`; `frechet_derivative (h:real^N->real^N) (at u) z`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "christoffel")) (concl th) &&
        can (find_term ((=) `V:real^N->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC
     `frechet_derivative (h:real^N->real^N) (at u) (frechet_derivative (Wf:real^N->real^N) (at u) z) +
      dd2 h u z (Wf u) =
      frechet_derivative (V:real^N->real^N) (at (h u)) (frechet_derivative h (at u) z)` THEN
    VECTOR_ARITH_TAC;
    DISCH_THEN(MP_TAC o AP_TERM `frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) u))`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(ISPEC `frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) u))` LINEAR_0) THEN
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Naturality of parallel fields under a diffeomorphism of manifolds: the    *)
(* pulled-back field is parallel for the pullback metric                     *)
(* (P2BPF_PAR_PULLBACK).                                                     *)
(* ========================================================================= *)

(* Manifold form, locally: near a point of a chart c of the source, the     *)
(* representative of the pulled-back field is smooth and parallel for the   *)
(* pullback metric.                                                         *)

let P2BPF_PAR_PULLBACK_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    W W' (f:A->B) f' (g':B->real^N^N) (X':B->real^N) (Z:A->real^N) c x0.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_diffeo top atlas W top' atlas' W' f f' /\
     p2b_parallel_on atlas' g' W' X' /\
     (!y. y IN W ==> mfd_differential atlas atlas' f y (Z y) = X'(f y)) /\
     c IN atlas /\ x0 IN FST c /\ x0 IN W
     ==> ?D0. open D0 /\ SND c x0 IN D0 /\ D0 SUBSET IMAGE (SND c) (FST c INTER W) /\
              smooth_map_on D0 (mfd_vrep atlas Z c) /\
              !u z. u IN D0
                    ==> frechet_derivative (mfd_vrep atlas Z c) (at u) z +
                        christoffel (metric_local atlas c (mfd_pullback_metric atlas atlas' f g'))
                          u z (mfd_vrep atlas Z c u) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_parallel_on] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_parallel_on")) (concl th))) THEN
  SUBGOAL_THEN `(f:A->B) x0 IN topspace top'` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET; FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?c1. c1 IN atlas' /\ (f:A->B) x0 IN FST (c1:(B->bool)#(B->real^N))`
  (X_CHOOSE_THEN `c1:(B->bool)#(B->real^N)` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[CHART_AT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c:(A->bool)#(A->real^N)`]
         MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `c1:(B->bool)#(B->real^N)`]
         MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `W':B->bool`;
                 `f:A->B`; `f':B->A`; `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c1:(B->bool)#(B->real^N))`; `SND(c1:(B->bool)#(B->real^N))`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "diffeomorphism_on")) (concl th))) THEN
  (* the chart representative of the pulled-back field *)
  SUBGOAL_THEN
   `!u. u IN IMAGE (SND (c:(A->bool)#(A->real^N))) {x | x IN FST c INTER (W:A->bool) /\ (f:A->B) x IN FST (c1:(B->bool)#(B->real^N))}
        ==> frechet_derivative (SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c:(A->bool)#(A->real^N))) (at u) (mfd_vrep (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) (c:(A->bool)#(A->real^N)) u) = mfd_vrep (atlas':((B->bool)#(B->real^N))->bool) (X':B->real^N) (c1:(B->bool)#(B->real^N)) ((SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c:(A->bool)#(A->real^N))) u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N` THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `f:A->B`;
                   `c:(A->bool)#(A->real^N)`; `c1:(B->bool)#(B->real^N)`; `x:A`] GEOI_DIFF_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
           CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[mfd_vrep; o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN IMAGE (SND (c:(A->bool)#(A->real^N))) {x | x IN FST c INTER (W:A->bool) /\ (f:A->B) x IN FST (c1:(B->bool)#(B->real^N))}
        ==> mfd_vrep (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) (c:(A->bool)#(A->real^N)) u = frechet_derivative (SND (c:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) (at ((SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c:(A->bool)#(A->real^N))) u)) (mfd_vrep (atlas':((B->bool)#(B->real^N))->bool) (X':B->real^N) (c1:(B->bool)#(B->real^N)) ((SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c:(A->bool)#(A->real^N))) u))`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`IMAGE (SND (c1:(B->bool)#(B->real^N))) {y | y IN FST c1 INTER (W':B->bool) /\ (f':B->A) y IN FST (c:(A->bool)#(A->real^N))}`; `IMAGE (SND (c:(A->bool)#(A->real^N))) {x | x IN FST c INTER (W:A->bool) /\ (f:A->B) x IN FST (c1:(B->bool)#(B->real^N))}`; `(SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c:(A->bool)#(A->real^N)))`; `(SND (c:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N)))`; `u:real^N`] LRG_DIFFEO_DERIV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `X':B->real^N`)) (concl th) &&
      can (find_term ((=) `Z:A->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (SND (c1:(B->bool)#(B->real^N))) {y | y IN FST c1 INTER (W':B->bool) /\ (f':B->A) y IN FST (c:(A->bool)#(A->real^N))} SUBSET IMAGE (SND (c1:(B->bool)#(B->real^N))) (FST c1 INTER (W':B->bool)) /\
                IMAGE (SND (c1:(B->bool)#(B->real^N))) {y | y IN FST c1 INTER (W':B->bool) /\ (f':B->A) y IN FST (c:(A->bool)#(A->real^N))} SUBSET IMAGE (SND (c1:(B->bool)#(B->real^N))) (FST c1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c1:(B->bool)#(B->real^N))) {y | y IN FST c1 INTER (W':B->bool) /\ (f':B->A) y IN FST (c:(A->bool)#(A->real^N))}`; `IMAGE (SND (c:(A->bool)#(A->real^N))) {x | x IN FST c INTER (W:A->bool) /\ (f:A->B) x IN FST (c1:(B->bool)#(B->real^N))}`; `(SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c:(A->bool)#(A->real^N)))`; `(SND (c:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N)))`; `metric_local (atlas':((B->bool)#(B->real^N))->bool) (c1:(B->bool)#(B->real^N)) (g':B->real^N^N)`; `mfd_vrep (atlas':((B->bool)#(B->real^N))->bool) (X':B->real^N) (c1:(B->bool)#(B->real^N))`; `mfd_vrep (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) (c:(A->bool)#(A->real^N))`] P2BPF_PAR_EUCLID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c1:(B->bool)#(B->real^N))) (FST c1)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `riemannian_metric (atlas':((B->bool)#(B->real^N))->bool) (g':B->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c1:(B->bool)#(B->real^N))) (FST c1 INTER (W':B->bool))` THEN
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    STRIP_TAC] THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) {x | x IN FST c INTER (W:A->bool) /\ (f:A->B) x IN FST (c1:(B->bool)#(B->real^N))}` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `x0:A` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `z:real^N`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (mfd_pullback_metric (atlas:((A->bool)#(A->real^N))->bool) (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) (g':B->real^N^N))) u z (mfd_vrep (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) (c:(A->bool)#(A->real^N)) u) =
    christoffel (mpullback (SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c:(A->bool)#(A->real^N))) (metric_local (atlas':((B->bool)#(B->real^N))->bool) (c1:(B->bool)#(B->real^N)) (g':B->real^N^N))) u z (mfd_vrep (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) (c:(A->bool)#(A->real^N)) u)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) {x | x IN FST c INTER (W:A->bool) /\ (f:A->B) x IN FST (c1:(B->bool)#(B->real^N))}` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `W':B->bool`;
                   `f:A->B`; `f':B->A`; `g':B->real^N^N`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c1:(B->bool)#(B->real^N))`; `SND(c1:(B->bool)#(B->real^N))`; `x:A`]
                  P2A_PULLBACK_METRIC_LOCAL_W) THEN
    ASM_REWRITE_TAC[PAIR];
    ASM_SIMP_TAC[]]);;


let P2BPF_PAR_PULLBACK = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    W W' (f:A->B) f' (g':B->real^N^N) (X':B->real^N) (Z:A->real^N).
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_diffeo top atlas W top' atlas' W' f f' /\
     p2b_parallel_on atlas' g' W' X' /\
     (!y. y IN W ==> mfd_differential atlas atlas' f y (Z y) = X'(f y))
     ==> p2b_parallel_on atlas (mfd_pullback_metric atlas atlas' f g') W Z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (W:A->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  REWRITE_TAC[p2b_parallel_on] THEN CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c:(A->bool)#(A->real^N)) INTER (W:A->bool)`] CHART_IMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFDM_CHART];
      X_GEN_TAC `u0:real^N` THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `x0:A` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                     `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `W':B->bool`;
                     `f:A->B`; `f':B->A`; `g':B->real^N^N`; `X':B->real^N`; `Z:A->real^N`;
                     `c:(A->bool)#(A->real^N)`; `x0:A`] P2BPF_PAR_PULLBACK_LOCAL) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `D0:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `D0:real^N->bool` THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `u0:real^N`; `z:real^N`] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x0:A` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `W':B->bool`;
                   `f:A->B`; `f':B->A`; `g':B->real^N^N`; `X':B->real^N`; `Z:A->real^N`;
                   `c:(A->bool)#(A->real^N)`; `x0:A`] P2BPF_PAR_PULLBACK_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `D0:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The quadratic form of a metric in a chart and in the preferred            *)
(* coordinates, and a uniform bound of the Christoffel symbols on a compact  *)
(* set (the lemmas on p2b_parallel_on are in pc_p2b_parons).                 *)
(* ========================================================================= *)

let P2BPF_JAC_QUAD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (h:A->real^N^N) c x w.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c
     ==> chart_jac (chart_at atlas x) c x w dot
         (metric_local atlas c h (SND c x) ** chart_jac (chart_at atlas x) c x w) =
         w dot (h x ** w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
         CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`; `x:A`]
         CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[metric_local; P2BPL_QUAD_PULLBACK; MATRIX_WORKS]);;

(* P2BPF_PARALLEL_ON_EQ, P2BPF_PARALLEL_ON_LOCAL and P2BPF_PARALLEL_CMUL are *)
(* in pc_p2b_parons.                                                         *)

let P2BPF_CHRIST_BOUND = prove
 (`!U (G:real^N->real^N^N) D.
     metric_field U G /\ compact D /\ D SUBSET U
     ==> ?C. &0 <= C /\
             !u a b. u IN D ==> norm(christoffel G u a b) <= C * norm a * norm b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. ?M. &0 <= M /\
              !u. u IN D ==> norm(christoffel (G:real^N->real^N^N) u (basis i) (basis j)) <= M`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `IMAGE (\u. christoffel (G:real^N->real^N^N) u (basis i) (basis j)) D`
           COMPACT_IMP_BOUNDED) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[REAL_LT_IMP_LE]];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `M:num->num->real` ASSUME_TAC)] THEN
  EXISTS_TAC `sum ((1..dimindex(:N)) CROSS (1..dimindex(:N))) (\(i,j). (M:num->num->real) i j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `bilinear (christoffel (G:real^N->real^N^N) u)` ASSUME_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `U:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINOP_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[BILINEAR_VSUM; FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BILINEAR_LMUL; NORM_MUL] THEN
  ASM_SIMP_TAC[BILINEAR_RMUL; NORM_MUL; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; COMPONENT_LE_NORM]);;

(* ========================================================================= *)
(* The pulled-back field of one slice (unique preimage under the             *)
(* differential, all its multiples parallel for the pullback metric), and a  *)
(* countable cover of the limit by chart balls from the compact exhaustion.  *)
(* ========================================================================= *)

let P2BPF_PULLED_FIELD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    W W' (f:A->B) f' (g':B->real^N^N) (X':B->real^N).
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_diffeo top atlas W top' atlas' W' f f' /\
     p2b_parallel_on atlas' g' W' X'
     ==> ?zf. (!y. y IN W ==> mfd_differential atlas atlas' f y (zf y) = X'(f y)) /\
              (!y z. y IN W /\ mfd_differential atlas atlas' f y z = X'(f y) ==> z = zf y) /\
              !a. p2b_parallel_on atlas (mfd_pullback_metric atlas atlas' f g') W (\y. a % zf y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (W:A->bool) /\ open_in top' (W':B->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN W
        ==> linear(mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                     (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) y) /\
            (!w:real^N. ?z:real^N. mfd_differential atlas atlas' f y z = w) /\
            (!z1 z2. mfd_differential atlas atlas' f y z1 = mfd_differential atlas atlas' f y z2
                     ==> z1 = z2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `W':B->bool`;
                   `f:A->B`; `f':B->A`; `y:A`] P2BPL_DIFF_SURJ) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_SURJECTIVE_IMP_INJECTIVE THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  EXISTS_TAC `\y:A. @z:real^N. mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                                  (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) y z =
                                (X':B->real^N) (f y)` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!y:A. y IN W
          ==> mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) y
                (@z:real^N. mfd_differential atlas atlas' f y z = (X':B->real^N) (f y)) = X' (f y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "linear")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `a:real` THEN MATCH_MP_TAC P2BPF_PAR_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `W':B->bool`; `f':B->A`;
                        `\y. a % (X':B->real^N) y`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BPF_PARALLEL_CMUL THEN EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "linear")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[LINEAR_CMUL]]);;

let P2BPF_CHART_COVER = prove
 (`!top (atlas:((B->bool)#(B->real^N))->bool) (W:num->B->bool).
     smooth_manifold_atlas top atlas /\ ~(topspace top = {}) /\
     (!k. open_in top (W k) /\ compact_in top (top closure_of W k)) /\
     UNIONS {W k | k IN (:num)} = topspace top
     ==> ?(cs:num->(B->bool)#(B->real^N)) (ps:num->real^N) (rs:num->real).
           (!i. cs i IN atlas /\ &0 < rs i /\
                cball(ps i,&2 * rs i) SUBSET IMAGE (SND (cs i)) (FST (cs i))) /\
           (!x. x IN topspace top ==> ?i. x IN FST (cs i) /\ SND (cs i) x IN ball(ps i,rs i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> ?r. &0 < r /\
                cball(SND(chart_at (atlas:((B->bool)#(B->real^N))->bool) x) x,&2 * r) SUBSET
                IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))`
  MP_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `x:B`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `chart_at (atlas:((B->bool)#(B->real^N))->bool) (x:B)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `SND(chart_at (atlas:((B->bool)#(B->real^N))->bool) (x:B)) x` o
                GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_ARITH `&2 * e / &2 = e`] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_TAC `rad:B->real`)] THEN
  ABBREV_TAC
   `P = \x:B. {y | y IN FST(chart_at (atlas:((B->bool)#(B->real^N))->bool) x) /\
                   SND(chart_at atlas x) y IN ball(SND(chart_at atlas x) x,rad x)}` THEN
  SUBGOAL_THEN `!x:B. x IN topspace top ==> open_in top (P x) /\ x IN P x` ASSUME_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `x:B`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_CHART_PREIMAGE_OPEN THEN
      EXISTS_TAC `atlas:((B->bool)#(B->real^N))->bool` THEN ASM_REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ?Fk. FINITE Fk /\ Fk SUBSET topspace top /\
             top closure_of (W:num->B->bool) k SUBSET UNIONS (IMAGE (P:B->B->bool) Fk)`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPEC `k:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
    REWRITE_TAC[compact_in] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (P:B->B->bool) (topspace top)` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:B` THEN DISCH_TAC THEN EXISTS_TAC `x:B` THEN
      SUBGOAL_THEN `(x:B) IN topspace top` (fun th -> ASM_SIMP_TAC[th]) THEN
      ASM_MESON_TAC[CLOSURE_OF_SUBSET_TOPSPACE; SUBSET];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:(B->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`P:B->B->bool`; `topspace (top:B topology)`; `V:(B->bool)->bool`]
           FINITE_SUBSET_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `Fk:B->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `Fs:num->B->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `COUNTABLE(UNIONS {(Fs:num->B->bool) k | k IN (:num)}) /\
                ~(UNIONS {Fs k | k IN (:num)} = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_UNIONS THEN REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; FINITE_IMP_COUNTABLE];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `x0:B` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o check (fun th ->
      is_neg(concl th))) THEN
    SUBGOAL_THEN `?k. (x0:B) IN (W:num->B->bool) k` (X_CHOOSE_TAC `k:num`) THENL
     [UNDISCH_TAC `UNIONS {(W:num->B->bool) k | k IN (:num)} = topspace top` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x0:B) IN top closure_of (W:num->B->bool) k` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t x:B. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `(W:num->B->bool) k` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
      ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    SUBGOAL_THEN `?y:B. y IN (Fs:num->B->bool) k` (X_CHOOSE_TAC `y:B`) THENL
     [UNDISCH_TAC `top closure_of (W:num->B->bool) k SUBSET UNIONS (IMAGE (P:B->B->bool) (Fs k))` THEN
      UNDISCH_TAC `(x0:B) IN top closure_of (W:num->B->bool) k` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN MESON_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      MAP_EVERY EXISTS_TAC [`y:B`; `(Fs:num->B->bool) k`] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `UNIONS {(Fs:num->B->bool) k | k IN (:num)}` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `en:num->B`) THEN
  SUBGOAL_THEN `!i. (en:num->B) i IN topspace top` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN
    SUBGOAL_THEN `(en:num->B) i IN UNIONS {(Fs:num->B->bool) k | k IN (:num)}` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_UNIV];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\i. chart_at (atlas:((B->bool)#(B->real^N))->bool) ((en:num->B) i)`;
    `\i. SND(chart_at (atlas:((B->bool)#(B->real^N))->bool) ((en:num->B) i)) (en i)`;
    `\i. (rad:B->real) ((en:num->B) i)`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `(en:num->B) i`]
           CHART_AT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k. (x:B) IN (W:num->B->bool) k` (X_CHOOSE_TAC `k:num`) THENL
   [UNDISCH_TAC `UNIONS {(W:num->B->bool) k | k IN (:num)} = topspace top` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:B) IN top closure_of (W:num->B->bool) k` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t x:B. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `(W:num->B->bool) k` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:B. y IN (Fs:num->B->bool) k /\ x IN (P:B->B->bool) y` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:B) IN top closure_of (W:num->B->bool) k` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Fs:num->B->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "closure_of")) (concl th))) THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?i. (en:num->B) i = y` (X_CHOOSE_THEN `i:num` (SUBST_ALL_TAC o SYM)) THENL
   [SUBGOAL_THEN `(y:B) IN UNIONS {(Fs:num->B->bool) k | k IN (:num)}` MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `i:num` THEN
  UNDISCH_TAC `(x:B) IN (P:B->B->bool) ((en:num->B) i)` THEN EXPAND_TAC "P" THEN
  REWRITE_TAC[IN_ELIM_THM]);;

(* ========================================================================= *)
(* The uniform limit of solutions of                                         *)
(* D f = --Gamma_n(., f) with Gamma_n -> Gamma_0 uniformly solves            *)
(* D g = --Gamma_0(., g) (HAS_DERIVATIVE_SEQUENCE).                          *)
(* ========================================================================= *)

let P2BPF_DERIV_EST = prove
 (`!(Gn:real^N->real^N->real^N) G0 a b h e M C eta delta.
     bilinear G0 /\ norm(Gn h a - G0 h a) <= eta * norm h * norm a /\
     norm(G0 h (a - b)) <= C * norm h * norm(a - b) /\
     norm a <= M /\ norm(a - b) <= delta /\ &0 <= eta /\ &0 <= C /\ eta * M + C * delta <= e
     ==> norm(--(Gn h a) - --(G0 h b)) <= e * norm h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `--((Gn:real^N->real^N->real^N) h a) - --(G0 h b) =
                --((Gn h a - G0 h a) + G0 h (a - b))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[BILINEAR_RSUB] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NORM_NEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `eta * norm(h:real^N) * norm(a:real^N) + C * norm h * norm(a - b:real^N)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC NORM_TRIANGLE_LE THEN ASM_SIMP_TAC[REAL_LE_ADD2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eta * norm(h:real^N) /\ &0 <= C * norm h` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(eta * norm(h:real^N)) * norm(a:real^N) <= (eta * norm h) * M /\
                (C * norm h) * norm(a - b:real^N) <= (C * norm h) * delta /\
                norm h * (eta * M + C * delta) <= norm h * e`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    REAL_ARITH_TAC]);;

let P2BPF_EUCLID_LIMIT = prove
 (`!s (f:num->real^N->real^N) g (Gn:num->real^N->real^N->real^N->real^N) G0 M C.
     open s /\ convex s /\ ~(s = {}) /\ &0 <= M /\ &0 <= C /\
     (!n u. u IN s ==> ((f n) has_derivative (\h. --(Gn n u h (f n u)))) (at u)) /\
     (!n u. u IN s ==> norm(f n u) <= M) /\
     (!u. u IN s ==> bilinear (G0 u)) /\
     (!u a b. u IN s ==> norm(G0 u a b) <= C * norm a * norm b) /\
     (!e. &0 < e ==> ?N. !n u a b. N <= n /\ u IN s
                                  ==> norm(Gn n u a b - G0 u a b) <= e * norm a * norm b) /\
     (!e. &0 < e ==> ?N. !n u. N <= n /\ u IN s ==> norm(f n u - g u) < e)
     ==> !u. u IN s ==> (g has_derivative (\h. --(G0 u h (g u)))) (at u)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "der") (CONJUNCTS_THEN2 (LABEL_TAC "bd")
   (CONJUNCTS_THEN2 (LABEL_TAC "bil") (CONJUNCTS_THEN2 (LABEL_TAC "gb")
   (CONJUNCTS_THEN2 (LABEL_TAC "gc") (LABEL_TAC "fc"))))))))))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:num->real^N->real^N`;
                 `\n u h. --((Gn:num->real^N->real^N->real^N->real^N) n u h
                              ((f:num->real^N->real^N) n u))`;
                 `\u h. --((G0:real^N->real^N->real^N->real^N) u h ((g:real^N->real^N) u))`]
         HAS_DERIVATIVE_SEQUENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      USE_THEN "der" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "gc" (MP_TAC o SPEC `e / &2 / (M + &1)`) THEN
      ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
      USE_THEN "fc" (MP_TAC o SPEC `e / &2 / (C + &1)`) THEN
      ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "n2")) THEN
      EXISTS_TAC `MAX N1 N2` THEN MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`; `h:real^N`] THEN
      REWRITE_TAC[GE; ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN STRIP_TAC THEN
      MATCH_MP_TAC P2BPF_DERIV_EST THEN
      MAP_EVERY EXISTS_TAC [`M:real`; `C:real`; `e / &2 / (M + &1)`; `e / &2 / (C + &1)`] THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "bil" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "n1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "gb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "bd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "n2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `e / &2 / (M + &1) * M <= e / &2 /\ C * e / &2 / (C + &1) <= e / &2`
        MP_TAC THENL
         [CONJ_TAC THENL
           [SUBGOAL_THEN `e / &2 / (M + &1) * M = (e / &2 * M) / (M + &1)` SUBST1_TAC THENL
             [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= M ==> &0 < M + &1`] THEN
            ASM_REAL_ARITH_TAC;
            SUBGOAL_THEN `C * e / &2 / (C + &1) = (e / &2 * C) / (C + &1)` SUBST1_TAC THENL
             [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= C ==> &0 < C + &1`] THEN
            ASM_REAL_ARITH_TAC];
          REAL_ARITH_TAC]];
      FIRST_X_ASSUM(X_CHOOSE_TAC `x0:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      MAP_EVERY EXISTS_TAC [`x0:real^N`; `(g:real^N->real^N) x0`] THEN
      ASM_REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "fc" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gg:real^N->real^N` (LABEL_TAC "gg")) THEN
  SUBGOAL_THEN `!x. x IN s ==> (gg:real^N->real^N) x = g x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. (f:num->real^N->real^N) n x` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [USE_THEN "gg" (MP_TAC o SPEC `x:real^N`) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "fc" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC [`gg:real^N->real^N`; `s:real^N->bool`] THEN ASM_SIMP_TAC[] THEN
  USE_THEN "gg" (MP_TAC o SPEC `u:real^N`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_OPEN THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Chart representatives of fields.  Derivative of the representative of a   *)
(* parallel field, the quadratic form in a chart, and unit length of the     *)
(* rescaled pulled-back field.                                               *)
(* ========================================================================= *)

let P2BPF_REP_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) g W (X:A->real^N) c u.
     smooth_manifold_atlas top atlas /\ open_in top W /\ p2b_parallel_on atlas g W X /\
     c IN atlas /\ u IN IMAGE (SND c) (FST c INTER W)
     ==> (mfd_vrep atlas X c has_derivative
          (\h. --(christoffel (metric_local atlas c g) u h (mfd_vrep atlas X c u)))) (at u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_parallel_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N)) INTER (W:A->bool)`] CHART_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)`;
                 `mfd_vrep atlas (X:A->real^N) c`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MP_TAC o SPEC `u:real^N`)] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `u:real^N`; `z:real^N`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "christoffel")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let P2BPF_REP_UNIT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (h:A->real^N^N) (Z:A->real^N) c u.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ u IN IMAGE (SND c) (FST c)
     ==> mfd_vrep atlas Z c u dot (metric_local atlas c h u ** mfd_vrep atlas Z c u) =
         Z (chart_inv c u) dot (h (chart_inv c u) ** Z (chart_inv c u))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[mfd_vrep] THEN
  MATCH_MP_TAC P2BPF_JAC_QUAD THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

let P2BPF_UNIT_PULL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    W W' (f:A->B) f' (g':B->real^N^N) (X':B->real^N) Q y z.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas W top' atlas' W' f f' /\ y IN W /\ &0 < Q /\
     mfd_differential atlas atlas' f y z = X'(f y) /\ X'(f y) dot (g'(f y) ** X'(f y)) = &1
     ==> (inv(sqrt Q) % z) dot
         ((Q %% mfd_pullback_metric atlas atlas' f g' y) ** (inv(sqrt Q) % z)) = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `(y:A) IN topspace top /\ (f:A->B) y IN topspace top'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_MESON_TAC[mfd_diffeo; OPEN_IN_SUBSET; SUBSET; FUN_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `W':B->bool`;
                 `f:A->B`; `f':B->A`; `y:A`] P2BPL_DIFF_SURJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `g':B->real^N^N`; `y:A`] P2BPL_PB_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[P2BPL_QUAD_SCALE; P2BPL_QUAD_PULLBACK; MATRIX_WORKS; REAL_MUL_RID] THEN
  MP_TAC(SPEC `Q:real` SQRT_POW_2) THEN MP_TAC(SPEC `Q:real` SQRT_POS_LT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* Per-chart estimates.  A uniform bound of the representatives (unit length *)
(* in a C^0-close metric), a Lipschitz bound (mean value theorem with the    *)
(* Christoffel bound), and the derivative of the representatives, eventually *)
(* in n, on a chart ball.                                                    *)
(* ========================================================================= *)

let P2BPF_TRI_EST = prove
 (`!(a:real^N) b x y M C.
     norm(a - b) <= &1 * x * y /\ norm b <= C * x * y /\ &0 <= x /\ &0 <= y /\ y <= M /\ &0 <= C
     ==> norm(--a) <= ((C + &1) * M) * x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_NEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C + &1) * x * y` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`a:real^N`; `b:real^N`] NORM_TRIANGLE_SUB) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `((C + &1) * M) * x = ((C + &1) * x) * M`] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let P2BPF_REP_BOUND = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g0:A->real^N^N) h (Z:A->real^N) c W u lam m.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     metric_field (IMAGE (SND c) (FST c INTER W)) (metric_local atlas c g0) /\
     metric_field (IMAGE (SND c) (FST c INTER W)) (metric_local atlas c h) /\
     u IN IMAGE (SND c) (FST c INTER W) /\ &0 < lam /\
     (!v. lam * norm v pow 2 <= v dot (metric_local atlas c g0 u ** v)) /\
     lck_dist2 m (metric_local atlas c g0) (metric_local atlas c h) u <= (&1 / &2) pow 2 /\
     Z (chart_inv c u) dot (h (chart_inv c u) ** Z (chart_inv c u)) = &1
     ==> norm(mfd_vrep atlas Z c u) <= sqrt(&2 / lam)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `h:A->real^N^N`;
                 `Z:A->real^N`; `c:(A->bool)#(A->real^N)`; `u:real^N`] P2BPF_REP_UNIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `u IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN SET_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N)`; `u:real^N`;
                 `mfd_vrep atlas (Z:A->real^N) c u`] LCK_DIST_C0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(lck_dist2 m (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N))
                  (metric_local atlas c (h:A->real^N^N)) u) <= &1 / &2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((&1 / &2) pow 2)` THEN
    ASM_SIMP_TAC[SQRT_MONO_LE; POW_2_SQRT; REAL_LE_REFL; REAL_ARITH `&0 <= &1 / &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_vrep atlas (Z:A->real^N) c u dot
                       (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N) u **
                        mfd_vrep atlas Z c u)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam * norm(mfd_vrep atlas (Z:A->real^N) (c:(A->bool)#(A->real^N)) u) pow 2` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_vrep atlas (Z:A->real^N) c u dot
                (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N) u **
                 mfd_vrep atlas Z c u) <= &2`
  ASSUME_TAC THENL
   [UNDISCH_TAC `abs(&1 - mfd_vrep atlas (Z:A->real^N) c u dot
                         (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N) u **
                          mfd_vrep atlas Z c u)) <=
                 sqrt(lck_dist2 m (metric_local atlas c g0) (metric_local atlas c (h:A->real^N^N)) u) *
                 (mfd_vrep atlas Z c u dot (metric_local atlas c g0 u ** mfd_vrep atlas Z c u))` THEN
    MP_TAC(ISPECL [`sqrt(lck_dist2 m (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N))
                      (metric_local atlas c (h:A->real^N^N)) u)`; `&1 / &2`;
                   `mfd_vrep atlas (Z:A->real^N) c u dot
                    (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N) u **
                     mfd_vrep atlas Z c u)`] REAL_LE_RMUL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_vrep atlas (Z:A->real^N) c u dot
              (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N) u **
               mfd_vrep atlas Z c u)` THEN
  ASM_REWRITE_TAC[]);;

let P2BPF_CHART_EST = prove
 (`!V x t Q (top:B topology) atlas g0 xl W phi (Zf:num->B->real^3) c p r.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!n. smooth_manifold_atlas (rfs_vtop (V n:(real->A topology)#
                                        (real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (t n))
                                (rfs_vatlas (V n) (t n)) /\
          riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) /\
          p2b_parallel_on atlas (mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                   (rfs_vmetric (V n) (t n))) (W n) (Zf n) /\
          (!y. y IN W n
               ==> Zf n y dot ((Q n %% mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                      (rfs_vmetric (V n) (t n)) y) ** Zf n y) = &1)) /\
     c IN atlas /\ &0 < r /\ cball(p,&2 * r) SUBSET IMAGE (SND c) (FST c)
     ==> ?N M L. &0 <= M /\ &0 <= L /\
           (!n. N <= n ==> IMAGE (chart_inv c) (cball(p,&2 * r)) SUBSET W n) /\
           (!n u. N <= n /\ u IN cball(p,&2 * r) ==> norm(mfd_vrep atlas (Zf n) c u) <= M) /\
           (!n u v. N <= n /\ u IN cball(p,r) /\ v IN cball(p,r)
                    ==> norm(mfd_vrep atlas (Zf n) c u - mfd_vrep atlas (Zf n) c v)
                        <= L * norm(u - v)) /\
           (!n u. N <= n /\ u IN ball(p,&2 * r)
                  ==> (mfd_vrep atlas (Zf n) c has_derivative
                       (\h. --(christoffel (metric_local atlas c
                                 (mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                    (rfs_vmetric (V n) (t n)))) u h (mfd_vrep atlas (Zf n) c u))))
                      (at u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `FST (c:(B->bool)#(B->real^3))`; `SND (c:(B->bool)#(B->real^3))`;
                 `cball(p:real^3,&2 * r)`] GRGD_METRIC_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PAIR; COMPACT_CBALL]; REWRITE_TAC[PAIR]] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))
                             (metric_local atlas c (g0:B->real^3^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g0:B->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)`;
                 `metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3)`;
                 `cball(p:real^3,&2 * r)`] P2BPF_CHRIST_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                 `cball(p:real^3,&2 * r)`; `0`; `(&1 / &2) pow 2`] P2BPL_SLICE_CLOSE_C0) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_CBALL; REAL_POW_LT; REAL_ARITH `&0 < &1 / &2`]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                 `cball(p:real^3,&2 * r)`; `&1`] P2BPL_CHRIST_C0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL; REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "n2")) THEN
  SUBGOAL_THEN `&0 < sqrt(&2 / lam)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. N1 <= n /\ N2 <= n
        ==> IMAGE (chart_inv (c:(B->bool)#(B->real^3))) (cball(p,&2 * r)) SUBSET W n /\
            (!u. u IN ball(p,&2 * r)
                 ==> (mfd_vrep atlas ((Zf:num->B->real^3) n) c has_derivative
                      (\h. --(christoffel (metric_local atlas c
                                (mfd_pullback_metric atlas
                                   (rfs_vatlas ((V:num->(real->A topology)#
                                                 (real->((A->bool)#(A->real^3))->bool)#
                                                 (real->A->real^3^3)) n) (t n))
                                   ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)))) u h
                              (mfd_vrep atlas (Zf n) c u)))) (at u)) /\
            (!u. u IN cball(p,&2 * r) ==> norm(mfd_vrep atlas (Zf n) c u) <= sqrt(&2 / lam)) /\
            (!u a b. u IN cball(p,&2 * r)
                     ==> norm(christoffel (metric_local atlas c
                                (mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                   (rfs_vmetric (V n) (t n)))) u a b -
                              christoffel (metric_local atlas c (g0:B->real^3^3)) u a b)
                         <= &1 * norm a * norm b)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    USE_THEN "n1" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl")) THEN
    USE_THEN "n2" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ch")) THEN
    FIRST_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `n:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_parallel_on")) (concl th))) THEN
    SUBGOAL_THEN
     `!u. u IN cball(p:real^3,&2 * r)
          ==> u IN IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) n)`
    ASSUME_TAC THENL
     [X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (c:(B->bool)#(B->real^3)) u` THEN
      SUBGOAL_THEN `u IN IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `metric_field (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) n))
                   (metric_local atlas c (g0:B->real^3^3)) /\
      metric_field (IMAGE (SND c) (FST c INTER W n))
                   (metric_local atlas c (\z. (Q:num->real) n %% mfd_pullback_metric atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)) z))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
        EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                         `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                         `FST(c:(B->bool)#(B->real^3)) INTER (W:num->B->bool) n`]
                 CHART_IMAGE_OPEN) THEN
          ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
          MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
        MATCH_MP_TAC P2BPL_PULLBACK_METRIC_FIELD THEN
        MAP_EVERY EXISTS_TAC
         [`top:B topology`;
          `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) n) (t n)`;
          `IMAGE ((phi:num->B->A) n) (W n)`; `psi:A->B`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC P2BPF_REP_DERIV THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `(W:num->B->bool) n`] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC P2BPF_REP_BOUND THEN
      MAP_EVERY EXISTS_TAC
       [`top:B topology`; `g0:B->real^3^3`; `\z. (Q:num->real) n %% mfd_pullback_metric atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)) z`;
        `(W:num->B->bool) n`; `0`] THEN
      ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
      USE_THEN "ch" ACCEPT_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`MAX N1 N2`; `sqrt(&2 / lam)`; `(C0 + &1) * sqrt(&2 / lam)`] THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN
  SUBGOAL_THEN `cball(p:real^3,r) SUBSET ball(p,&2 * r) /\ cball(p,r) SUBSET cball(p,&2 * r)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`n:num`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `N1:num`)) (concl th) &&
      can (find_term ((=) `N2:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`mfd_vrep atlas ((Zf:num->B->real^3) n) (c:(B->bool)#(B->real^3))`;
                   `\w h. --(christoffel (metric_local atlas (c:(B->bool)#(B->real^3)) (mfd_pullback_metric atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)))) w h
                              (mfd_vrep atlas ((Zf:num->B->real^3) n) c w))`;
                   `cball(p:real^3,r)`; `(C0 + &1) * sqrt(&2 / lam)`] DIFFERENTIABLE_BOUND) THEN
    REWRITE_TAC[CONVEX_CBALL] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `w IN ball(p:real^3,&2 * r) /\ w IN cball(p,&2 * r)` STRIP_ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[];
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `w IN ball(p:real^3,&2 * r) /\ w IN cball(p,&2 * r)` STRIP_ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPEC `\h. --(christoffel (metric_local atlas (c:(B->bool)#(B->real^3)) (mfd_pullback_metric atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)))) w h
                              (mfd_vrep atlas ((Zf:num->B->real^3) n) c w))` ONORM) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC LRG_HAS_DERIVATIVE_IMP_LINEAR THEN
          MAP_EVERY EXISTS_TAC [`mfd_vrep atlas ((Zf:num->B->real^3) n) (c:(B->bool)#(B->real^3))`;
                                `at (w:real^3)`] THEN
          ASM_SIMP_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN X_GEN_TAC `h:real^3` THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC P2BPF_TRI_EST THEN
        MAP_EVERY EXISTS_TAC
         [`christoffel (metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3)) w h
             (mfd_vrep atlas ((Zf:num->B->real^3) n) c w)`;
          `norm(mfd_vrep atlas ((Zf:num->B->real^3) n) (c:(B->bool)#(B->real^3)) w)`] THEN
        ASM_SIMP_TAC[NORM_POS_LE]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Unit length passes to the limit, and the inverse of the representative    *)
(* map.                                                                      *)
(* ========================================================================= *)

let P2BPF_UNIT_LIMIT = prove
 (`!(s:num->real^N->bool) (G0:real^N->real^N^N) G y (f:num->real^N) v.
     (!n. metric_field (s n) G0 /\ metric_field (s n) (G n) /\ y IN s n) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> lck_dist2 0 G0 (G n) y < e) /\
     (!n. f n dot (G n y ** f n) = &1) /\ (f --> v) sequentially
     ==> v dot (G0 y ** v) = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mf") (CONJUNCTS_THEN2 (LABEL_TAC "cl")
    (CONJUNCTS_THEN2 (LABEL_TAC "un") (LABEL_TAC "cv")))) THEN
  SUBGOAL_THEN `!n. &0 <= (f:num->real^N) n dot ((G0:real^N->real^N^N) y ** f n)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_NONNEG THEN
    EXISTS_TAC `(s:num->real^N->bool) n` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n eta. &0 < eta /\ lck_dist2 0 (G0:real^N->real^N^N) (G n) y < eta pow 2
            ==> abs(&1 - (f:num->real^N) n dot (G0 y ** f n)) <= eta * (f n dot (G0 y ** f n))`
  (LABEL_TAC "eta") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`0`; `(s:num->real^N->bool) n`; `G0:real^N->real^N^N`;
                   `(G:num->real^N->real^N^N) n`; `y:real^N`; `(f:num->real^N) n`] LCK_DIST_C0) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "un" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(lck_dist2 0 (G0:real^N->real^N^N) (G n) y) *
                ((f:num->real^N) n dot (G0 y ** f n))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  USE_THEN "cl" (MP_TAC o SPEC `&1 / &4`) THEN REWRITE_TAC[REAL_ARITH `&0 < &1 / &4`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  SUBGOAL_THEN `!n. N1 <= n ==> (f:num->real^N) n dot ((G0:real^N->real^N^N) y ** f n) <= &2`
  (LABEL_TAC "le2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "eta" (MP_TAC o SPECL [`n:num`; `&1 / &2`]) THEN
    ANTS_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\n. lift((f:num->real^N) n dot ((G0:real^N->real^N^N) y ** f n))`;
                 `lift(v dot ((G0:real^N->real^N^N) y ** v))`; `lift(&1)`] LIM_UNIQUE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIFT_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [MATCH_MP_TAC P2BPL_QUAD_LIM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "cl" (MP_TAC o SPEC `(e / &3) pow 2`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  EXISTS_TAC `MAX N1 N2` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN STRIP_TAC THEN
  USE_THEN "eta" (MP_TAC o SPECL [`n:num`; `e / &3`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; USE_THEN "N2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "le2" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`e / &3`; `(f:num->real^N) n dot ((G0:real^N->real^N^N) y ** f n)`; `&2`]
         REAL_LE_LMUL) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> &0 <= e / &3`] THEN ASM_REAL_ARITH_TAC);;

let P2BPF_VREP_INV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) c x.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c
     ==> chart_jac c (chart_at atlas x) x (mfd_vrep atlas Z c (SND c x)) = Z x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
         CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[mfd_vrep]);;

(* The two metric fields in a chart of the limit, on the part of the chart  *)
(* piece inside W n.                                                         *)

let P2BPF_FIELDS = prove
 (`!V x t Q (top:B topology) atlas g0 xl W phi c n.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!n. smooth_manifold_atlas (rfs_vtop (V n:(real->A topology)#
                                        (real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (t n))
                                (rfs_vatlas (V n) (t n)) /\
          riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))) /\
     c IN atlas
     ==> metric_field (IMAGE (SND c) (FST c INTER W n)) (metric_local atlas c g0) /\
         metric_field (IMAGE (SND c) (FST c INTER W n))
           (metric_local atlas c
              (\z. Q n %% mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                           (rfs_vmetric (V n) (t n)) z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `n:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g0:B->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                     `FST(c:(B->bool)#(B->real^3)) INTER (W:num->B->bool) n`] CHART_IMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFDM_CHART];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    MATCH_MP_TAC P2BPL_PULLBACK_METRIC_FIELD THEN
    MAP_EVERY EXISTS_TAC
     [`top:B topology`;
      `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) n) (t n)`;
      `IMAGE ((phi:num->B->A) n) (W n)`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[]]);;

(* One chart ball, after the diagonal extraction: the uniform limit of the   *)
(* representatives is a smooth unit parallel field there, and the pulled-    *)
(* back fields converge pointwise to its preferred-coordinate form.          *)

let P2BPF_PIECE = prove
 (`!V x t Q (top:B topology) atlas g0 xl W phi (Zf:num->B->real^3) c p r sub gl.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!n. smooth_manifold_atlas (rfs_vtop (V n:(real->A topology)#
                                        (real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (t n))
                                (rfs_vatlas (V n) (t n)) /\
          riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) /\
          p2b_parallel_on atlas (mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                   (rfs_vmetric (V n) (t n))) (W n) (Zf n) /\
          (!y. y IN W n
               ==> Zf n y dot ((Q n %% mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                      (rfs_vmetric (V n) (t n)) y) ** Zf n y) = &1)) /\
     c IN atlas /\ &0 < r /\ cball(p,&2 * r) SUBSET IMAGE (SND c) (FST c) /\
     p3_subseq sub /\ gl continuous_on cball(p,r) /\
     (!e. &0 < e ==> ?K. !n u. K <= n /\ u IN cball(p,r)
                               ==> norm(mfd_vrep atlas (Zf (sub n)) c u - gl u) < e)
     ==> open_in top {x | x IN FST c /\ SND c x IN ball(p,r)} /\
         p2b_parallel_on atlas g0 {x | x IN FST c /\ SND c x IN ball(p,r)}
           (\x. chart_jac c (chart_at atlas x) x (gl (SND c x))) /\
         (!x. x IN {x | x IN FST c /\ SND c x IN ball(p,r)}
              ==> chart_jac c (chart_at atlas x) x (gl (SND c x)) dot
                  (g0 x ** chart_jac c (chart_at atlas x) x (gl (SND c x))) = &1) /\
         (!x. x IN FST c /\ SND c x IN ball(p,r)
              ==> ((\n. Zf (sub n) x) --> chart_jac c (chart_at atlas x) x (gl (SND c x)))
                  sequentially)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_subseq sub` THEN REWRITE_TAC[p3_subseq] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MONOTONE_BIGGER) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(p:real^3,r) SUBSET cball(p,r) /\ cball(p,r) SUBSET cball(p,&2 * r) /\
                ball(p,r) SUBSET ball(p,&2 * r) /\ ball(p,r) SUBSET cball(p,&2 * r)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))
                             (metric_local atlas c (g0:B->real^3^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g0:B->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `Zf:num->B->real^3`;
                 `c:(B->bool)#(B->real^3)`; `p:real^3`; `r:real`] P2BPF_CHART_EST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (X_CHOOSE_THEN `M:real` (X_CHOOSE_THEN `L:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inc")
    (CONJUNCTS_THEN2 (LABEL_TAC "bd") (CONJUNCTS_THEN2 (LABEL_TAC "lip") (LABEL_TAC "der"))))))))) THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)`;
                 `metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3)`;
                 `cball(p:real^3,&2 * r)`] P2BPF_CHRIST_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gb"))) THEN
  (* the limit solves the parallel equation on the open ball *)
  SUBGOAL_THEN
   `!u. u IN ball(p:real^3,r)
        ==> ((gl:real^3->real^3) has_derivative
             (\h. --(christoffel (metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3))
                       u h (gl u)))) (at u)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(p:real^3,r)`;
                   `\n. mfd_vrep atlas ((Zf:num->B->real^3) ((sub:num->num) (n + N)))
                          (c:(B->bool)#(B->real^3))`;
                   `gl:real^3->real^3`;
                   `\n. christoffel (metric_local atlas (c:(B->bool)#(B->real^3)) (mfd_pullback_metric atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) (n + N))) (t (sub (n + N)))) ((phi:num->B->A) (sub (n + N))) (rfs_vmetric (V (sub (n + N))) (t (sub (n + N))))))`;
                   `christoffel (metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3))`;
                   `M:real`; `C0:real`] P2BPF_EUCLID_LIMIT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[OPEN_BALL; CONVEX_BALL; BALL_EQ_EMPTY] THEN ASM_REWRITE_TAC[REAL_NOT_LE] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`n:num`; `u:real^3`] THEN DISCH_TAC THEN
      USE_THEN "der" MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n + N:num` THEN ASM_REWRITE_TAC[LE_ADDR];
        ASM SET_TAC[]];
      MAP_EVERY X_GEN_TAC [`n:num`; `u:real^3`] THEN DISCH_TAC THEN
      USE_THEN "bd" MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n + N:num` THEN ASM_REWRITE_TAC[LE_ADDR];
        ASM SET_TAC[]];
      X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN
      EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`u:real^3`; `a:real^3`; `b:real^3`] THEN DISCH_TAC THEN
      USE_THEN "gb" MATCH_MP_TAC THEN ASM SET_TAC[];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)`;
                     `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                     `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                     `cball(p:real^3,&2 * r)`; `e:real`] P2BPL_CHRIST_C0) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n1:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `u:real^3`; `a:real^3`; `b:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(sub:num->num) (n + N)`) THEN ANTS_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n + N:num` THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM SET_TAC[]];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `gl:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `sub:num->num`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `u:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (ball(p:real^3,r))
                  (metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(p:real^3,r)) (gl:real^3->real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BPL_PARALLEL_BOOTSTRAP THEN
    EXISTS_TAC `metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `cball(p:real^3,r)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y z. y IN ball(p:real^3,r)
          ==> frechet_derivative (gl:real^3->real^3) (at y) z +
              christoffel (metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3)) y z (gl y) =
              vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `gl:real^3->real^3`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball(p:real^3,r)
        ==> (gl:real^3->real^3) y dot
            (metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3) y ** gl y) = &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!n. chart_inv (c:(B->bool)#(B->real^3)) y IN (W:num->B->bool) ((sub:num->num) (n + N))`
    ASSUME_TAC THENL
     [GEN_TAC THEN USE_THEN "inc" (MP_TAC o SPEC `(sub:num->num) (n + N)`) THEN ANTS_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n + N:num` THEN ASM_REWRITE_TAC[LE_ADDR];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) y IN FST c /\ SND c (chart_inv c y) = y`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\n. IMAGE (SND (c:(B->bool)#(B->real^3)))
                            (FST c INTER (W:num->B->bool) ((sub:num->num) (n + N)))`;
                   `metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3)`;
                   `\n. metric_local atlas (c:(B->bool)#(B->real^3))
                          (\z. (Q:num->real) ((sub:num->num) (n + N)) %% mfd_pullback_metric atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) (n + N))) (t (sub (n + N)))) ((phi:num->B->A) (sub (n + N))) (rfs_vmetric (V (sub (n + N))) (t (sub (n + N)))) z)`;
                   `y:real^3`;
                   `\n. mfd_vrep atlas ((Zf:num->B->real^3) ((sub:num->num) (n + N)))
                          (c:(B->bool)#(B->real^3)) y`;
                   `(gl:real^3->real^3) y`] P2BPF_UNIT_LIMIT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)`;
                     `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                     `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                     `(sub:num->num) (n + N)`] P2BPF_FIELDS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]] THEN
      DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (c:(B->bool)#(B->real^3)) y` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)`;
                     `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                     `W:num->B->bool`; `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                     `cball(p:real^3,&2 * r)`; `0`; `e:real`] P2BPL_SLICE_CLOSE_C0) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n1:num` THEN DISCH_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(sub:num->num) (n + N)`) THEN ANTS_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n + N:num` THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM SET_TAC[]];
      X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `\z. (Q:num->real) ((sub:num->num) (n + N)) %% mfd_pullback_metric atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) (n + N))) (t (sub (n + N)))) ((phi:num->B->A) (sub (n + N))) (rfs_vmetric (V (sub (n + N))) (t (sub (n + N)))) z`;
                     `(Zf:num->B->real^3) ((sub:num->num) (n + N))`;
                     `c:(B->bool)#(B->real^3)`; `y:real^3`] P2BPF_REP_UNIT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `(sub:num->num) (n + N)` o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_parallel_on")) (concl th))) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `gl:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `sub:num->num`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th)))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `c:(B->bool)#(B->real^3)`; `ball(p:real^3,r)`; `gl:real^3->real^3`]
         RFA_PARALLEL_ON_FROM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o REWRITE_RULE[]))) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. (Zf:num->B->real^3) ((sub:num->num) n) y =
        chart_jac (c:(B->bool)#(B->real^3)) (chart_at atlas y) y
          (mfd_vrep atlas (Zf (sub n)) c (SND c y))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BPF_VREP_INV THEN
    EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_LINEAR THEN CONJ_TAC THENL
   [REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `gl:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `sub:num->num`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                   `FST(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B))`;
                   `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B))`; `y:B`]
           CHART_JAC_LINEAR) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER]]);;

(* ========================================================================= *)
(* The uniform convergence in the g0 norm on one chart piece, and the main   *)
(* theorem P2BPL_LIMIT_FIELD.                                                *)
(* ========================================================================= *)

let P2BPF_UNIFORM_PIECE = prove
 (`!top (atlas:((B->bool)#(B->real^N))->bool) (g0:B->real^N^N) (Zs:num->B->real^N) (Y:B->real^N)
    gl c p r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\ c IN atlas /\ &0 < r /\
     cball(p,r) SUBSET IMAGE (SND c) (FST c) /\
     (!e. &0 < e ==> ?K. !n u. K <= n /\ u IN cball(p,r)
                               ==> norm(mfd_vrep atlas (Zs n) c u - gl u) < e) /\
     (!y. y IN FST c /\ SND c y IN ball(p,r)
          ==> Y y = chart_jac c (chart_at atlas y) y (gl (SND c y)))
     ==> !e. &0 < e
             ==> ?K. !n y. K <= n /\ y IN FST c /\ SND c y IN ball(p,r)
                           ==> (Zs n y - Y y) dot (g0 y ** (Zs n y - Y y)) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "uc") (LABEL_TAC "yd"))))))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^N))->bool`; `g0:B->real^N^N`;
                 `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                 `cball(p:real^N,r)`] GRGD_METRIC_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PAIR; COMPACT_CBALL]; REWRITE_TAC[PAIR]] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < Lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "uc" (MP_TAC o SPEC `sqrt(e / (Lam + &1))`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `y:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND (c:(B->bool)#(B->real^N)) y IN cball(p,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `SND (c:(B->bool)#(B->real^N)) y IN ball(p,r)` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `w = mfd_vrep atlas ((Zs:num->B->real^N) n) (c:(B->bool)#(B->real^N)) (SND c y) -
                  (gl:real^N->real^N) (SND c y)` THEN
  SUBGOAL_THEN `norm(w:real^N) < sqrt(e / (Lam + &1))` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `FST(c:(B->bool)#(B->real^N))`; `SND(c:(B->bool)#(B->real^N))`;
                 `FST(chart_at (atlas:((B->bool)#(B->real^N))->bool) (y:B))`;
                 `SND(chart_at (atlas:((B->bool)#(B->real^N))->bool) (y:B))`; `y:B`]
         CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(Zs:num->B->real^N) n y - (Y:B->real^N) y =
    chart_jac (c:(B->bool)#(B->real^N)) (chart_at atlas y) y w`
  SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN ASM_SIMP_TAC[LINEAR_SUB] THEN
    USE_THEN "yd" (fun th -> ASM_SIMP_TAC[th]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2BPF_VREP_INV THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g0:B->real^N^N`;
                 `c:(B->bool)#(B->real^N)`; `y:B`;
                 `chart_jac (c:(B->bool)#(B->real^N)) (chart_at atlas y) y w`] P2BPF_JAC_QUAD) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `FST(c:(B->bool)#(B->real^N))`; `SND(c:(B->bool)#(B->real^N))`;
                 `FST(chart_at (atlas:((B->bool)#(B->real^N))->bool) (y:B))`;
                 `SND(chart_at (atlas:((B->bool)#(B->real^N))->bool) (y:B))`; `y:B`]
         CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `Lam * norm(w:real^N) pow 2` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `Lam * e / (Lam + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    SUBGOAL_THEN `e / (Lam + &1) = sqrt(e / (Lam + &1)) pow 2` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE; ARITH_EQ];
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < L ==> &0 < L + &1`] THEN
    ASM_REAL_ARITH_TAC]);;

(* Headline: the limit field.                                                 *)

let P2BPL_LIMIT_FIELD = prove
 (`!(u:A->bool) (w:B->bool). P2BPL_LIMIT_FIELD_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BPL_LIMIT_FIELD_STATEMENT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  (* the pulled-back fields of the slices *)
  SUBGOAL_THEN
   `?zf:num->B->real^3.
      !n. (!y. y IN W n
               ==> mfd_differential atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) ((phi:num->B->A) n) y (zf n y) =
                   (X:num->A->real^3) n (phi n y)) /\
          (!y z. y IN W n /\
                 mfd_differential atlas (rfs_vatlas (V n) (t n)) (phi n) y z = X n (phi n y)
                 ==> z = zf n y) /\
          (!a. p2b_parallel_on atlas
                 (mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n) (rfs_vmetric (V n) (t n)))
                 (W n) (\y. a % zf n y))`
  (X_CHOOSE_THEN `zf:num->B->real^3` (LABEL_TAC "zf")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `n:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
    MATCH_MP_TAC P2BPF_PULLED_FIELD THEN
    MAP_EVERY EXISTS_TAC
     [`top:B topology`; `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`; `IMAGE ((phi:num->B->A) n) (W n)`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `?Zf:num->B->real^3. !n y. Zf n y = inv(sqrt((Q:num->real) n)) % zf n y`
  (X_CHOOSE_THEN `Zf:num->B->real^3` (LABEL_TAC "Zf")) THENL
   [EXISTS_TAC `\n y. inv(sqrt((Q:num->real) n)) % (zf:num->B->real^3) n y` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) (rfs_vatlas (V n) (t n)) /\
        riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) /\
        p2b_parallel_on atlas (mfd_pullback_metric atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) ((phi:num->B->A) n) (rfs_vmetric (V n) (t n))) (W n) ((Zf:num->B->real^3) n) /\
        (!y. y IN W n ==> Zf n y dot (((Q:num->real) n %% mfd_pullback_metric atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)) y) ** Zf n y) = &1)`
  (LABEL_TAC "zfh") THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `(Zf:num->B->real^3) n = (\y. inv(sqrt((Q:num->real) n)) % zf n y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `X:num->A->real^3`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_parallel_on")) (concl th) &&
      not (can (find_term ((=) `zf:num->B->real^3`)) (concl th)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "zf" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `n:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
    MATCH_MP_TAC P2BPF_UNIT_PULL THEN
    MAP_EVERY EXISTS_TAC
     [`top:B topology`; `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`; `(W:num->B->bool) n`;
      `IMAGE ((phi:num->B->A) n) (W n)`; `psi:A->B`; `(X:num->A->real^3) n`] THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a countable cover by chart balls *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `W:num->B->bool`]
         P2BPF_CHART_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cs:num->(B->bool)#(B->real^3)` (X_CHOOSE_THEN `ps:num->real^3`
    (X_CHOOSE_THEN `rs:num->real` (CONJUNCTS_THEN2 (LABEL_TAC "cs") (LABEL_TAC "cov"))))) THEN
  (* the estimates on each chart ball *)
  SUBGOAL_THEN
   `?N M L. !i. &0 <= (M:num->real) i /\ &0 <= (L:num->real) i /\
              (!n. (N:num->num) i <= n
                   ==> IMAGE (chart_inv ((cs:num->(B->bool)#(B->real^3)) i))
                         (cball((ps:num->real^3) i,&2 * (rs:num->real) i)) SUBSET W n) /\
              (!n u. N i <= n /\ u IN cball(ps i,&2 * rs i)
                     ==> norm(mfd_vrep atlas ((Zf:num->B->real^3) n) (cs i) u) <= M i) /\
              (!n u v. N i <= n /\ u IN cball(ps i,rs i) /\ v IN cball(ps i,rs i)
                       ==> norm(mfd_vrep atlas (Zf n) (cs i) u - mfd_vrep atlas (Zf n) (cs i) v)
                           <= L i * norm(u - v))`
  (X_CHOOSE_THEN `N:num->num` (X_CHOOSE_THEN `M:num->real` (X_CHOOSE_THEN `L:num->real`
    (LABEL_TAC "est")))) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                   `W:num->B->bool`; `phi:num->B->A`; `Zf:num->B->real^3`;
                   `(cs:num->(B->bool)#(B->real^3)) i`; `(ps:num->real^3) i`; `(rs:num->real) i`]
           P2BPF_CHART_EST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M0:real` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `L0:real` THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* diagonal Arzela-Ascoli *)
  MP_TAC(ISPECL [`\i n. mfd_vrep atlas ((Zf:num->B->real^3) n) ((cs:num->(B->bool)#(B->real^3)) i)`;
                 `\i. cball((ps:num->real^3) i,(rs:num->real) i)`; `M:num->real`; `N:num->num`]
         P2CS_AA_DIAG_GEN) THEN
  REWRITE_TAC[NUM_COUNTABLE; COMPACT_CBALL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `n:num`; `u:real^3`] THEN STRIP_TAC THEN
      USE_THEN "est" (MP_TAC o SPEC `i:num`) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `u IN cball((ps:num->real^3) i,(rs:num->real) i)` THEN
      USE_THEN "cs" (MP_TAC o SPEC `i:num`) THEN
      REWRITE_TAC[IN_CBALL] THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`i:num`; `u:real^3`; `e:real`] THEN STRIP_TAC THEN
      USE_THEN "est" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
      EXISTS_TAC `e / ((L:num->real) i + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `v:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(L:num->real) i * norm(u - v:real^3)` THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(L:num->real) i * e / (L i + &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= L ==> &0 < L + &1`] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `gl:num->real^3->real^3` (LABEL_TAC "gl")) THEN
  SUBGOAL_THEN `p3_subseq (sub:num->num)` ASSUME_TAC THENL [ASM_REWRITE_TAC[p3_subseq]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_subseq sub` THEN REWRITE_TAC[p3_subseq] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MONOTONE_BIGGER) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the limit on each chart ball *)
  SUBGOAL_THEN
   `!i. open_in top {x | x IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\ SND (cs i) x IN ball((ps:num->real^3) i,(rs:num->real) i)} /\
        p2b_parallel_on atlas (g0:B->real^3^3) {x | x IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\ SND (cs i) x IN ball((ps:num->real^3) i,(rs:num->real) i)} (\x. chart_jac ((cs:num->(B->bool)#(B->real^3)) i) (chart_at atlas x) x ((gl:num->real^3->real^3) i (SND (cs i) x))) /\
        (!x. x IN {x | x IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\ SND (cs i) x IN ball((ps:num->real^3) i,(rs:num->real) i)} ==> chart_jac ((cs:num->(B->bool)#(B->real^3)) i) (chart_at atlas x) x ((gl:num->real^3->real^3) i (SND (cs i) x)) dot (g0 x ** chart_jac ((cs:num->(B->bool)#(B->real^3)) i) (chart_at atlas x) x ((gl:num->real^3->real^3) i (SND (cs i) x))) = &1) /\
        (!x. x IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\ SND (cs i) x IN ball((ps:num->real^3) i,(rs:num->real) i)
             ==> ((\n. (Zf:num->B->real^3) ((sub:num->num) n) x) --> chart_jac ((cs:num->(B->bool)#(B->real^3)) i) (chart_at atlas x) x ((gl:num->real^3->real^3) i (SND (cs i) x))) sequentially)`
  (LABEL_TAC "pc") THENL
   [X_GEN_TAC `i:num` THEN MATCH_MP_TAC P2BPF_PIECE THEN
    MAP_EVERY EXISTS_TAC [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `x:num->A`; `t:num->real`; `Q:num->real`; `xl:B`;
                          `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `Y = \y:B. @w:real^3. ((\n. (Zf:num->B->real^3) ((sub:num->num) n) y) --> w) sequentially` THEN
  SUBGOAL_THEN
   `!i y. y IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\
          SND (cs i) y IN ball((ps:num->real^3) i,(rs:num->real) i)
          ==> (Y:B->real^3) y =
              chart_jac (cs i) (chart_at atlas y) y ((gl:num->real^3->real^3) i (SND (cs i) y))`
  (LABEL_TAC "yd") THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `y:B`] THEN STRIP_TAC THEN EXPAND_TAC "Y" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. (Zf:num->B->real^3) ((sub:num->num) n) y` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    USE_THEN "pc" (MP_TAC o SPEC `y:B` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `chart_jac ((cs:num->(B->bool)#(B->real^3)) i) (chart_at atlas y) y
                  ((gl:num->real^3->real^3) i (SND (cs i) y))` THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `Y:B->real^3`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BPF_PARALLEL_ON_LOCAL THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "cov" (MP_TAC o SPEC `y:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{x | x IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\ SND (cs i) x IN ball((ps:num->real^3) i,(rs:num->real) i)}` THEN
    USE_THEN "pc" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC P2BPF_PARALLEL_ON_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `\x. chart_jac ((cs:num->(B->bool)#(B->real^3)) i) (chart_at atlas x) x ((gl:num->real^3->real^3) i (SND (cs i) x))`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    USE_THEN "yd" (MP_TAC o SPECL [`i:num`; `x:B`]) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "cov" (MP_TAC o SPEC `y:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "yd" (MP_TAC o SPECL [`i:num`; `y:B`]) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "pc" (MP_TAC o SPEC `y:B` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:B->bool`; `e:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?Fi. FINITE Fi /\ K SUBSET UNIONS (IMAGE (\i. {x | x IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\ SND (cs i) x IN ball((ps:num->real^3) i,(rs:num->real) i)}) Fi)`
  (X_CHOOSE_THEN `Fi:num->bool` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `compact_in top (K:B->bool)` THEN REWRITE_TAC[compact_in] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `IMAGE (\i. {x | x IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\ SND (cs i) x IN ball((ps:num->real^3) i,(rs:num->real) i)}) (:num)`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN CONJ_TAC THENL
       [X_GEN_TAC `i:num` THEN USE_THEN "pc" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `i:num` th)]);
        REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
        X_GEN_TAC `y:B` THEN DISCH_TAC THEN
        USE_THEN "cov" (MP_TAC o SPEC `y:B`) THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]];
      DISCH_THEN(X_CHOOSE_THEN `V0:(B->bool)->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`\i. {x | x IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\ SND (cs i) x IN ball((ps:num->real^3) i,(rs:num->real) i)}`; `(:num)`; `V0:(B->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Fi:num->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. cball((ps:num->real^3) i,(rs:num->real) i) SUBSET IMAGE (SND ((cs:num->(B->bool)#(B->real^3)) i)) (FST (cs i))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN USE_THEN "cs" (MP_TAC o SPEC `i:num`) THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((ps:num->real^3) i,&2 * (rs:num->real) i)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ?Ki. !n y. Ki <= n /\ y IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\
                   SND (cs i) y IN ball((ps:num->real^3) i,(rs:num->real) i)
                   ==> ((Zf:num->B->real^3) ((sub:num->num) n) y - (Y:B->real^3) y) dot
                       ((g0:B->real^3^3) y ** (Zf (sub n) y - Y y)) < e`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                   `\n. (Zf:num->B->real^3) ((sub:num->num) n)`; `Y:B->real^3`;
                   `(gl:num->real^3->real^3) i`; `((cs:num->(B->bool)#(B->real^3)) i)`;
                   `(ps:num->real^3) i`; `(rs:num->real) i`] P2BPF_UNIFORM_PIECE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `Ku:num->num` (LABEL_TAC "ku"))] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`K:B->bool`; `0`; `&1`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_pullback")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  MP_TAC(ISPEC `IMAGE (Ku:num->num) Fi` num_FINITE) THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kmax:num` (LABEL_TAC "kmax")) THEN
  EXISTS_TAC `k0 + Kmax:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:B) IN (W:num->B->bool) ((sub:num->num) n)` ASSUME_TAC THENL
   [USE_THEN "k0" (MP_TAC o SPEC `(sub:num->num) n`) THEN ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `(zf:num->B->real^3) ((sub:num->num) n) y` THEN CONJ_TAC THENL
   [USE_THEN "zf" (MP_TAC o SPEC `(sub:num->num) n`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "Zf" (fun th -> REWRITE_TAC[GSYM th]) THEN
  SUBGOAL_THEN `?i. i IN Fi /\ (y:B) IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\
                    SND (cs i) y IN ball((ps:num->real^3) i,(rs:num->real) i)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:B->bool) SUBSET UNIONS (IMAGE (\i. {x | x IN FST ((cs:num->(B->bool)#(B->real^3)) i) /\ SND (cs i) x IN ball((ps:num->real^3) i,(rs:num->real) i)}) Fi)` THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Ku:num->num) i <= Kmax` ASSUME_TAC THENL
   [USE_THEN "kmax" MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ku" (MP_TAC o SPECL [`i:num`; `n:num`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]]);;

