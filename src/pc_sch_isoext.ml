(* ========================================================================= *)
(* pc_sch_isoext: isotopy extension for compact sets in real^N.             *)
(*                                                                           *)
(* A smooth family H t of injective immersions of an open set U with         *)
(* H 0 = identity is, on a compact K inside U, the time-one map of a        *)
(* compactly supported diffeomorphism of real^N supported near the trace    *)
(* of K (Hirsch, Differential Topology, Thm 8.1.3, for compact sets).        *)
(* Route: the track map (t,x) |-> (t,H t x) is a diffeomorphism onto an      *)
(* open set W; the time-dependent field V = (d/dt H) o (track map)^-1 on W   *)
(* is cut off near the compact trace of [0,1] x K (GRGE_EUCLID_CUTOFF);       *)
(* its flow (ODE_FLOW_ISOTOPY) carries x to H 1 x by uniqueness of           *)
(* solutions (ODE_MAXIMAL_UNIQUE). Main theorems: SCHI_ISOTOPY_EXTENSION and *)
(* SCHI_ISOTOPY_EXTENSION_01, used for the planar collars and for the        *)
(* collars and the gluing step in R^3 of the smooth Schoenflies theorem,     *)
(* among others.                                                             *)
(* ========================================================================= *)

needs "src/pc_ode_vf.ml";;
needs "src/pc_smt_sphere.ml";;
needs "src/pc_mfd_embmetric.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary lemmas. An injective smooth map with invertible derivative is a *)
(* diffeomorphism onto its image (the statement of P2CE_INJ_DIFFEO in        *)
(* pc_p2c_cgemb.ml, proved again here so that this file does not depend on   *)
(* that one); derivatives of the slices and time curves of a smooth family;  *)
(* the track map (t,x) |-> (t,H t x) of an isotopy of immersions.            *)
(* ------------------------------------------------------------------------- *)

let SCHI_INJ_DIFFEO = prove
 (`!(f:real^N->real^N) s.
     open s /\ smooth_map_on s f /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     (!x. x IN s ==> ~(det(matrix(frechet_derivative f (at x))) = &0))
     ==> ?g. diffeomorphism_on s (IMAGE f s) f g`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\y:real^N. @x. x IN s /\ (f:real^N->real^N) x = y` THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> (@x'. x' IN s /\ (f:real^N->real^N) x' = f x) = x`
  (LABEL_TAC "inv") THENL
   [REPEAT STRIP_TAC THEN SELECT_ELIM_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> ((f:real^N->real^N) has_derivative
                                         frechet_derivative f (at x)) (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (f:real^N->real^N) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_OPEN_MAP THEN
    EXISTS_TAC `\x:real^N. frechet_derivative (f:real^N->real^N) (at x)` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN USE_THEN "inv" (fun th -> ASM_SIMP_TAC[th]);
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(f:real^N->real^N) x` THEN
      USE_THEN "inv" (fun th -> ASM_SIMP_TAC[th]) THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN USE_THEN "inv" (fun th -> SIMP_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `s:real^N->bool`; `a:real^N`]
                SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `g0:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `g0:real^N->real^N` THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g0:real^N->real^N) y IN s /\ (f:real^N->real^N)(g0 y) = y`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `diffeomorphism_on t u (f:real^N->real^N) g0` THEN
      REWRITE_TAC[diffeomorphism_on] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "inv" (MP_TAC o C MP (ASSUME `(g0:real^N->real^N) y IN s`) o
                    SPEC `(g0:real^N->real^N) y`) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `diffeomorphism_on t u (f:real^N->real^N) g0` THEN
    SIMP_TAC[diffeomorphism_on]]);;

(* The joint map of a smooth family is differentiable on R x U. *)

let SCHI_JOINT_HAS_DERIVATIVE = prove
 (`!(H:real->real^N->real^N) U z.
        open U /\ smooth_family U H /\ z IN (:real^1) PCROSS U
        ==> ((\z. H (drop(fstcart z)) (sndcart z)) has_derivative
             frechet_derivative (\z. H (drop(fstcart z)) (sndcart z)) (at z)) (at z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_family] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^1) PCROSS (U:real^N->bool)`;
                 `\z:real^(1,N)finite_sum. (H:real->real^N->real^N) (drop(fstcart z)) (sndcart z)`]
    SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]);;

(* Slices: the derivative of H t at x is the joint derivative on (0,k). *)

let SCHI_SLICE_DERIV = prove
 (`!(H:real->real^N->real^N) U t x.
        open U /\ smooth_family U H /\ x IN U
        ==> (H t has_derivative
             (\k. frechet_derivative (\z. H (drop(fstcart z)) (sndcart z))
                                     (at (pastecart (lift t) x)) (pastecart (vec 0) k)))
            (at x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Hj = \z:real^(1,N)finite_sum.
                     (H:real->real^N->real^N) (drop(fstcart z)) (sndcart z)` THEN
  SUBGOAL_THEN `(H:real->real^N->real^N) t = Hj o (\y:real^N. pastecart (lift t) y)`
  SUBST1_TAC THENL
   [EXPAND_TAC "Hj" THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\k:real^N. frechet_derivative Hj (at (pastecart (lift t) x))
                              (pastecart (vec 0) k)) =
                frechet_derivative (Hj:real^(1,N)finite_sum->real^N)
                                   (at (pastecart (lift t) x)) o
                (\k:real^N. pastecart (vec 0:real^1) k)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`at (x:real^N)`; `\y:real^N. lift t`; `\y:real^N. y`;
                   `\h:real^N. vec 0:real^1`; `\h:real^N. h`] HAS_DERIVATIVE_PASTECART) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    EXPAND_TAC "Hj" THEN MATCH_MP_TAC SCHI_JOINT_HAS_DERIVATIVE THEN
    EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV]]);;

(* Time curves: d/ds H s x is the joint derivative on (1,0). *)

let SCHI_TIME_DERIV = prove
 (`!(H:real->real^N->real^N) U s x.
        open U /\ smooth_family U H /\ x IN U
        ==> ((\r. H (drop r) x) has_vector_derivative
             frechet_derivative (\z. H (drop(fstcart z)) (sndcart z))
                                (at (pastecart s x)) (pastecart (lift(&1)) (vec 0)))
            (at s)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Hj = \z:real^(1,N)finite_sum.
                     (H:real->real^N->real^N) (drop(fstcart z)) (sndcart z)` THEN
  SUBGOAL_THEN `(\r. (H:real->real^N->real^N) (drop r) x) =
                Hj o (\r:real^1. pastecart r x)` SUBST1_TAC THENL
   [EXPAND_TAC "Hj" THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Hj:real^(1,N)finite_sum->real^N) differentiable at (pastecart s x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `frechet_derivative (Hj:real^(1,N)finite_sum->real^N) (at (pastecart s x))` THEN
    EXPAND_TAC "Hj" THEN MATCH_MP_TAC SCHI_JOINT_HAS_DERIVATIVE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN `(\h:real^1. drop h % frechet_derivative (Hj:real^(1,N)finite_sum->real^N)
                                       (at (pastecart s x)) (pastecart (lift(&1)) (vec 0))) =
                frechet_derivative Hj (at (pastecart s x)) o
                (\h:real^1. pastecart h (vec 0:real^N))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO] THEN
    REWRITE_TAC[PASTECART_INJ] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP; REAL_MUL_RID];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`at (s:real^1)`; `\r:real^1. r`; `\r:real^1. x:real^N`;
                   `\h:real^1. h`; `\h:real^1. vec 0:real^N`] HAS_DERIVATIVE_PASTECART) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

(* ------------------------------------------------------------------------- *)
(* The track map (t,x) |-> (t,H t x) of a smooth family of                  *)
(* injective immersions is a diffeomorphism of R x U onto an open set.       *)
(* ------------------------------------------------------------------------- *)

let SCHI_FSTCART_SMOOTH = prove
 (`!s:real^(1,N)finite_sum->bool. open s ==> smooth_map_on s (fstcart:real^(1,N)finite_sum->real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^(1,N)finite_sum->bool`; `\z:real^(1,N)finite_sum. z`]
    SMOOTH_MAP_ON_FSTCART_OPEN) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let SCHI_TRACK_DERIV = prove
 (`!(H:real->real^N->real^N) U z.
        open U /\ smooth_family U H /\ z IN (:real^1) PCROSS U
        ==> ((\z. pastecart (fstcart z) (H (drop(fstcart z)) (sndcart z))) has_derivative
             (\h. pastecart (fstcart h)
                    (frechet_derivative (\z. H (drop(fstcart z)) (sndcart z)) (at z) h)))
            (at z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`at (z:real^(1,N)finite_sum)`; `fstcart:real^(1,N)finite_sum->real^1`;
                 `\z:real^(1,N)finite_sum. (H:real->real^N->real^N) (drop(fstcart z)) (sndcart z)`;
                 `fstcart:real^(1,N)finite_sum->real^1`;
                 `frechet_derivative (\z:real^(1,N)finite_sum.
                    (H:real->real^N->real^N) (drop(fstcart z)) (sndcart z)) (at z)`]
    HAS_DERIVATIVE_PASTECART) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_FSTCART];
    MATCH_MP_TAC SCHI_JOINT_HAS_DERIVATIVE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let SCHI_TRACK_INJ = prove
 (`!(H:real->real^N->real^N) U.
        (!t x y. x IN U /\ y IN U /\ H t x = H t y ==> x = y)
        ==> !z w. z IN (:real^1) PCROSS U /\ w IN (:real^1) PCROSS U /\
                  pastecart (fstcart z) (H (drop(fstcart z)) (sndcart z)) =
                  pastecart (fstcart w) (H (drop(fstcart w)) (sndcart w))
                  ==> z = w`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "inj") THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_PCROSS] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_INJ; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`s1:real^1`; `x1:real^N`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s2:real^1`; `x2:real^N`] THEN DISCH_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "inj" MATCH_MP_TAC THEN EXISTS_TAC `drop s2` THEN ASM_REWRITE_TAC[]);;

let SCHI_TRACK_DET = prove
 (`!(H:real->real^N->real^N) U z.
        open U /\ smooth_family U H /\
        (!t x h. x IN U /\ frechet_derivative (H t) (at x) h = vec 0 ==> h = vec 0) /\
        z IN (:real^1) PCROSS U
        ==> ~(det(matrix(frechet_derivative
                (\z. pastecart (fstcart z) (H (drop(fstcart z)) (sndcart z))) (at z))) = &0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "imm") MP_TAC))) THEN
  SPEC_TAC(`z:real^(1,N)finite_sum`,`z:real^(1,N)finite_sum`) THEN
  REWRITE_TAC[FORALL_IN_PCROSS; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `x:real^N`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:real->real^N->real^N`; `U:real^N->bool`; `pastecart (s:real^1) (x:real^N)`]
    SCHI_TRACK_DERIV) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  REWRITE_TAC[PASTECART_EQ_VEC; NOT_EXISTS_THM] THEN X_GEN_TAC `h:real^(1,N)finite_sum` THEN
  STRIP_TAC THEN
  ABBREV_TAC `k = sndcart(h:real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN `h = pastecart (vec 0:real^1) (k:real^N)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "k" THEN ASM_MESON_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:real->real^N->real^N`; `U:real^N->bool`; `drop s`; `x:real^N`]
    SCHI_SLICE_DERIV) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  UNDISCH_TAC `~(pastecart (vec 0:real^1) (k:real^N) = vec 0)` THEN
  REWRITE_TAC[PASTECART_EQ_VEC] THEN
  USE_THEN "imm" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`drop s`; `x:real^N`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
    is_eq(concl th) && is_abs(lhs(concl th)))) THEN
  ASM_REWRITE_TAC[]);;

let SCHI_TRACK_DIFFEO = prove
 (`!(H:real->real^N->real^N) U.
        open U /\ smooth_family U H /\
        (!t x y. x IN U /\ y IN U /\ H t x = H t y ==> x = y) /\
        (!t x h. x IN U /\ frechet_derivative (H t) (at x) h = vec 0 ==> h = vec 0)
        ==> ?G. diffeomorphism_on ((:real^1) PCROSS U)
                  (IMAGE (\z. pastecart (fstcart z) (H (drop(fstcart z)) (sndcart z)))
                         ((:real^1) PCROSS U))
                  (\z. pastecart (fstcart z) (H (drop(fstcart z)) (sndcart z))) G`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHI_INJ_DIFFEO THEN
  SUBGOAL_THEN `open((:real^1) PCROSS (U:real^N->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_SIMP_TAC[SCHI_FSTCART_SMOOTH] THEN
    UNDISCH_TAC `smooth_family (U:real^N->bool) (H:real->real^N->real^N)` THEN
    REWRITE_TAC[smooth_family];
    MATCH_MP_TAC SCHI_TRACK_INJ THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    MATCH_MP_TAC SCHI_TRACK_DET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The isotopy extension theorem for compact sets.                          *)
(* ------------------------------------------------------------------------- *)

(* Along the trace of the isotopy the cut-off field is the velocity. *)

let SCHI_ISOTOPY_EXTENSION = prove
 (`!(H:real->real^N->real^N) U K V.
     open U /\ compact K /\ K SUBSET U /\ open V /\ smooth_family U H /\
     (!t x y. x IN U /\ y IN U /\ H t x = H t y ==> x = y) /\
     (!t x h. x IN U /\ frechet_derivative (H t) (at x) h = vec 0 ==> h = vec 0) /\
     (!x. x IN U ==> H (&0) x = x) /\
     (!t x. &0 <= t /\ t <= &1 /\ x IN K ==> H t x IN V)
     ==> ?Phi Psi L. diffeomorphism_on (:real^N) (:real^N) Phi Psi /\
                     (!x. x IN K ==> Phi x = H (&1) x) /\
                     compact L /\ L SUBSET V /\ (!x. ~(x IN L) ==> Phi x = x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (CONJUNCTS_THEN2 (LABEL_TAC "imm") (CONJUNCTS_THEN2 (LABEL_TAC "H0")
       (LABEL_TAC "HV"))))))))) THEN
  SUBGOAL_THEN `!x:real^N. x IN K ==> x IN U` (LABEL_TAC "KU") THENL
   [UNDISCH_TAC `(K:real^N->bool) SUBSET U` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open((:real^1) PCROSS (U:real^N->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^1) PCROSS (U:real^N->bool))
                  (\z. (H:real->real^N->real^N) (drop(fstcart z)) (sndcart z))` ASSUME_TAC
  THENL
   [UNDISCH_TAC `smooth_family (U:real^N->bool) (H:real->real^N->real^N)` THEN
    REWRITE_TAC[smooth_family];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:real->real^N->real^N`; `U:real^N->bool`] SCHI_TRACK_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Tr = \z:real^(1,N)finite_sum.
                     pastecart (fstcart z) ((H:real->real^N->real^N) (drop(fstcart z)) (sndcart z))` THEN
  ABBREV_TAC `W = IMAGE (Tr:real^(1,N)finite_sum->real^(1,N)finite_sum)
                        ((:real^1) PCROSS (U:real^N->bool))` THEN
  DISCH_THEN(X_CHOOSE_THEN `Gt:real^(1,N)finite_sum->real^(1,N)finite_sum` ASSUME_TAC) THEN
  SUBGOAL_THEN `open(W:real^(1,N)finite_sum->bool) /\
                IMAGE (Gt:real^(1,N)finite_sum->real^(1,N)finite_sum) W =
                  (:real^1) PCROSS (U:real^N->bool) /\
                (!z. z IN (:real^1) PCROSS U ==> Gt((Tr:real^(1,N)finite_sum->real^(1,N)finite_sum) z) = z) /\
                smooth_map_on W Gt` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on ((:real^1) PCROSS (U:real^N->bool)) W
                   (Tr:real^(1,N)finite_sum->real^(1,N)finite_sum) Gt` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  ABBREV_TAC `Vel = \z:real^(1,N)finite_sum.
       frechet_derivative (\z. (H:real->real^N->real^N) (drop(fstcart z)) (sndcart z)) (at z)
                          (pastecart (lift(&1)) (vec 0:real^N))` THEN
  SUBGOAL_THEN `smooth_map_on ((:real^1) PCROSS (U:real^N->bool))
                  (Vel:real^(1,N)finite_sum->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "Vel" THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* The compact trace and the cutoff. *)
  ABBREV_TAC `C = IMAGE (Tr:real^(1,N)finite_sum->real^(1,N)finite_sum)
                        (interval[vec 0,lift(&1)] PCROSS (K:real^N->bool))` THEN
  SUBGOAL_THEN `compact(C:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^1) PCROSS (U:real^N->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      UNDISCH_TAC `diffeomorphism_on ((:real^1) PCROSS (U:real^N->bool)) W
                     (Tr:real^(1,N)finite_sum->real^(1,N)finite_sum) Gt` THEN
      SIMP_TAC[diffeomorphism_on];
      MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s x. s IN interval[vec 0,lift(&1)] /\ x IN K
                      ==> (Tr:real^(1,N)finite_sum->real^(1,N)finite_sum) (pastecart s x) IN C /\
                          Tr (pastecart s x) IN W /\
                          Tr (pastecart s x) = pastecart s ((H:real->real^N->real^N) (drop s) x) /\
                          (H:real->real^N->real^N) (drop s) x IN V`
  (LABEL_TAC "TRC") THENL
   [MAP_EVERY X_GEN_TAC [`s:real^1`; `x:real^N`] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "C" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
      EXPAND_TAC "W" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN USE_THEN "KU" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "Tr" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
      USE_THEN "HV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(s:real^1) IN interval[vec 0,lift(&1)]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C:real^(1,N)finite_sum->bool) SUBSET W INTER ((:real^1) PCROSS (V:real^N->bool))`
  ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; IN_INTER] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `x:real^N`] THEN STRIP_TAC THEN
    USE_THEN "TRC" (fun th -> STRIP_ASSUME_TAC(MP (SPECL [`s:real^1`; `x:real^N`] th)
      (CONJ (ASSUME `(s:real^1) IN interval[vec 0,lift(&1)]`) (ASSUME `(x:real^N) IN K`)))) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real^(1,N)finite_sum->bool`;
                 `W INTER ((:real^1) PCROSS (V:real^N->bool))`] GRGE_EUCLID_CUTOFF) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_INTER; OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^(1,N)finite_sum->real`
    (X_CHOOSE_THEN `L1:real^(1,N)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
  (* The cut-off velocity field. *)
  ABBREV_TAC `fv = \z:real^(1,N)finite_sum.
                     if z IN W then psi z % (Vel:real^(1,N)finite_sum->real^N)(Gt z)
                     else vec 0` THEN
  SUBGOAL_THEN `smooth_map_on (:real^(1,N)finite_sum) (fv:real^(1,N)finite_sum->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `z:real^(1,N)finite_sum` THEN
    ASM_CASES_TAC `(z:real^(1,N)finite_sum) IN W` THENL
     [EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
      EXISTS_TAC `\y:real^(1,N)finite_sum.
                    drop(lift(psi y)) % ((Vel:real^(1,N)finite_sum->real^N) o Gt) y` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "fv" THEN SIMP_TAC[o_THM; LIFT_DROP];
        MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
          EXISTS_TAC `(:real^(1,N)finite_sum)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
          MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
          EXISTS_TAC `(:real^1) PCROSS (U:real^N->bool)` THEN
          ASM_REWRITE_TAC[SUBSET_REFL]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((z:real^(1,N)finite_sum) IN L1)` ASSUME_TAC THENL
     [UNDISCH_TAC `L1 SUBSET W INTER ((:real^1) PCROSS (V:real^N->bool))` THEN
      UNDISCH_TAC `~((z:real^(1,N)finite_sum) IN W)` THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `(:real^(1,N)finite_sum) DIFF L1` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_UNIV; COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\y:real^(1,N)finite_sum. vec 0:real^N` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `y:real^(1,N)finite_sum` THEN DISCH_TAC THEN EXPAND_TAC "fv" THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:real^(1,N)finite_sum->real) y = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `L1:real^(1,N)finite_sum->bool`)) (concl th) &&
        can (find_term ((=) `&0`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,lift(&1)]
                    ==> !x. x IN K
                            ==> (fv:real^(1,N)finite_sum->real^N)
                                  (pastecart t ((H:real->real^N->real^N) (drop t) x)) =
                                (Vel:real^(1,N)finite_sum->real^N) (pastecart t x)`
  (LABEL_TAC "FVEL") THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "TRC" (fun th -> STRIP_ASSUME_TAC(MP (SPECL [`t:real^1`; `x:real^N`] th)
      (CONJ (ASSUME `(t:real^1) IN interval[vec 0,lift(&1)]`) (ASSUME `(x:real^N) IN K`)))) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `pastecart (t:real^1) ((H:real->real^N->real^N) (drop t) x)`)) THEN
    EXPAND_TAC "fv" THEN
    REWRITE_TAC[ASSUME `(Tr:real^(1,N)finite_sum->real^(1,N)finite_sum) (pastecart t x) IN W`] THEN
    SUBGOAL_THEN `(psi:real^(1,N)finite_sum->real)
                    ((Tr:real^(1,N)finite_sum->real^(1,N)finite_sum) (pastecart t x)) = &1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `C:real^(1,N)finite_sum->bool`)) (concl th) &&
        can (find_term ((=) `&1`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Gt:real^(1,N)finite_sum->real^(1,N)finite_sum`)) (concl th) &&
      is_imp(snd(strip_forall(concl th))))) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN USE_THEN "KU" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* The flow. *)
  SUBGOAL_THEN `compact(IMAGE sndcart (L1:real^(1,N)finite_sum->bool)) /\
                IMAGE sndcart L1 SUBSET (V:real^N->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
      UNDISCH_TAC `L1 SUBSET W INTER ((:real^1) PCROSS (V:real^N->bool))` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
      MESON_TAC[PASTECART_FST_SND; PASTECART_IN_PCROSS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`fv:real^(1,N)finite_sum->real^N`; `(:real^1)`; `(:real^N)`;
                 `IMAGE sndcart (L1:real^(1,N)finite_sum->bool)`] ODE_FLOW_ISOTOPY) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_UNIV; IS_INTERVAL_UNIV; UNIV_PCROSS_UNIV; SUBSET_UNIV; IN_UNIV] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^N`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(pastecart (t:real^1) (x:real^N) IN L1)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~((x:real^N) IN IMAGE sndcart (L1:real^(1,N)finite_sum->bool))` THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `pastecart (t:real^1) (x:real^N)` THEN
      ASM_REWRITE_TAC[SNDCART_PASTECART];
      ALL_TAC] THEN
    EXPAND_TAC "fv" THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:real^(1,N)finite_sum->real) (pastecart t x) = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `L1:real^(1,N)finite_sum->bool`)) (concl th) &&
        can (find_term ((=) `&0`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  REWRITE_TAC[UNIV_PCROSS_UNIV; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (MP_TAC o SPECL [`vec 0:real^1`; `lift(&1)`]) (LABEL_TAC "FIX")))) THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^N. ode_flow (fv:real^(1,N)finite_sum->real^N) (:real^(1,N)finite_sum) (lift(&1))
                         (pastecart (vec 0) x)`;
    `\y:real^N. ode_flow (fv:real^(1,N)finite_sum->real^N) (:real^(1,N)finite_sum) (vec 0)
                         (pastecart (lift(&1)) y)`;
    `IMAGE sndcart (L1:real^(1,N)finite_sum->bool)`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "FIX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`fv:real^(1,N)finite_sum->real^N`; `(:real^(1,N)finite_sum)`;
                 `pastecart (vec 0:real^1) (x:real^N)`; `interval[vec 0:real^1,lift(&1)]`;
                 `\r:real^1. (H:real->real^N->real^N) (drop r) x`] ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`fv:real^(1,N)finite_sum->real^N`; `(:real^(1,N)finite_sum)`]
      ODE_SMOOTH_IMP_LOCALLY_LIPSCHITZ) THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN CONJ_TAC THENL
     [ALL_TAC;
      CONJ_TAC THENL
       [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC;
        USE_THEN "H0" MATCH_MP_TAC THEN USE_THEN "KU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]] THEN
    REWRITE_TAC[ode_solution; IS_INTERVAL_INTERVAL; IN_UNIV] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    USE_THEN "FVEL" (fun th -> REWRITE_TAC[MP (SPEC `x:real^N` (MP (SPEC `t:real^1` th)
      (ASSUME `(t:real^1) IN interval[vec 0,lift(&1)]`))) (ASSUME `(x:real^N) IN K`)]) THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    EXPAND_TAC "Vel" THEN MATCH_MP_TAC SCHI_TIME_DERIV THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "KU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift(&1)` o CONJUNCT2) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP; REAL_POS; REAL_LE_REFL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* The same with hypotheses only for 0 <= t <= 1 (time reparametrized by    *)
(* smooth_step).                                                             *)

let SCHI_ISOTOPY_EXTENSION_01 = prove
 (`!(H:real->real^N->real^N) U K V.
     open U /\ compact K /\ K SUBSET U /\ open V /\ smooth_family U H /\
     (!t x y. &0 <= t /\ t <= &1 /\ x IN U /\ y IN U /\ H t x = H t y ==> x = y) /\
     (!t x h. &0 <= t /\ t <= &1 /\ x IN U /\ frechet_derivative (H t) (at x) h = vec 0
              ==> h = vec 0) /\
     (!x. x IN U ==> H (&0) x = x) /\
     (!t x. &0 <= t /\ t <= &1 /\ x IN K ==> H t x IN V)
     ==> ?Phi Psi L. diffeomorphism_on (:real^N) (:real^N) Phi Psi /\
                     (!x. x IN K ==> Phi x = H (&1) x) /\
                     compact L /\ L SUBSET V /\ (!x. ~(x IN L) ==> Phi x = x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (CONJUNCTS_THEN2 (LABEL_TAC "imm") (CONJUNCTS_THEN2 (LABEL_TAC "H0")
       (LABEL_TAC "HV"))))))))) THEN
  SUBGOAL_THEN `smooth_step(&0) = &0 /\ smooth_step(&1) = &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_0 THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_STEP_1 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (H:real->real^N->real^N) (smooth_step t)`; `U:real^N->bool`;
                 `K:real^N->bool`; `V:real^N->bool`] SCHI_ISOTOPY_EXTENSION) THEN
  REWRITE_TAC[ASSUME `smooth_step(&0) = &0`; ASSUME `smooth_step(&1) = &1`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[ASSUME `open(U:real^N->bool)`; ASSUME `compact(K:real^N->bool)`;
              ASSUME `(K:real^N->bool) SUBSET U`; ASSUME `open(V:real^N->bool)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMT_FAMILY_REPARAM THEN ASM_REWRITE_TAC[SMOOTH_STEP_SMOOTH];
    REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
    EXISTS_TAC `smooth_step t` THEN ASM_REWRITE_TAC[SMOOTH_STEP_BOUNDS];
    REPEAT STRIP_TAC THEN USE_THEN "imm" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`smooth_step t`; `x:real^N`] THEN
    ASM_REWRITE_TAC[SMOOTH_STEP_BOUNDS];
    USE_THEN "H0" ACCEPT_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "HV" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SMOOTH_STEP_BOUNDS]]);;

