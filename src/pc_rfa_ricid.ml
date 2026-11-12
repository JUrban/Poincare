(* ========================================================================= *)
(* Unit pc_rfa_ricid: commuting covariant derivatives: the Ricci identity    *)
(* for (0,k)-tensor fields, exact and with the curvature term as a member of *)
(* the class lbilin; the predicate lbilin_on (agreement with a class member  *)
(* on tensor fields) with its closure rules (permutations, contractions of   *)
(* arbitrary slot pairs, sums, exchange of the arguments, substitution of a  *)
(* contraction or a permutation into an argument).                           *)
(* ========================================================================= *)

needs "src/pc_rfa_talg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Slot linearity, lnabla at tuples agreeing on 1..k, and the                *)
(* derivative of the first covariant derivative.                             *)
(* ========================================================================= *)

let RFA_SLOT_LINEAR = prove
 (`!k U (tf:real^N->(num->real^N)->real) y i u.
        ltensor_field k U tf /\ y IN U /\ 1 <= i /\ i <= k
        ==> (!a b. tf y (\j. if j = i then a + b else u j) =
                   tf y (\j. if j = i then a else u j) +
                   tf y (\j. if j = i then b else u j)) /\
            (!a b. tf y (\j. if j = i then a - b else u j) =
                   tf y (\j. if j = i then a else u j) -
                   tf y (\j. if j = i then b else u j)) /\
            (!c a. tf y (\j. if j = i then c % a else u j) =
                   c * tf y (\j. if j = i then a else u j)) /\
            tf y (\j. if j = i then vec 0 else u j) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `linear (\v. lift((tf:real^N->(num->real^N)->real) y
                       (\j. if j = i then v else u j)))`
  ASSUME_TAC THENL [ASM_MESON_TAC[ltensor_field]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(MATCH_MP LINEAR_ADD th) THEN MP_TAC(MATCH_MP LINEAR_SUB th) THEN
    MP_TAC(MATCH_MP LINEAR_CMUL th) THEN MP_TAC(MATCH_MP LINEAR_0 th)) THEN
  REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_SUB; GSYM LIFT_CMUL; GSYM LIFT_NUM;
              LIFT_EQ] THEN
  SIMP_TAC[]);;

let RFA_LNABLA_REDUCE = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) z w w0.
        open U /\ ltensor_field k U tf /\ z IN U /\
        (!m. 1 <= m /\ m <= k ==> w m = w0 m)
        ==> lnabla k G tf z w =
            drop(frechet_derivative (\x. lift(tf x w0)) (at z) (w(k + 1))) -
            sum(1..k) (\j. tf z (\m. if m = j then christoffel G z (w(k + 1)) (w0 j)
                                     else w0 m))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla] THEN BINOP_TAC THENL
   [AP_TERM_TAC THEN AP_THM_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

(* Derivative of a Christoffel slot term (LRG_HAS_DERIVATIVE_LINFAM).       *)

let RFA_DERIV_CTERM = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y i a v.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U /\ 1 <= i /\ i <= k
        ==> ((\z. lift(tf z (\j. if j = i then christoffel G z a (v i) else v j)))
             has_derivative
             (\e. lift(tf y (\j. if j = i
                                 then frechet_derivative
                                        (\z. christoffel G z a (v i)) (at y) e
                                 else v j)) +
                  frechet_derivative
                    (\z. lift(tf z (\j. if j = i then christoffel G y a (v i)
                                        else v j)))
                    (at y) e)) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z:real^N b:real^N. lift((tf:real^N->(num->real^N)->real) z
                               (\j. if j = i then b else (v:num->real^N) j))`;
    `\z:real^N. christoffel (G:real^N->real^N^N) z a ((v:num->real^N) i)`;
    `frechet_derivative
       (\z:real^N. christoffel (G:real^N->real^N^N) z a ((v:num->real^N) i)) (at y)`;
    `U:real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_LINFAM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `v:num->real^N`]) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* Derivative of the first covariant derivative evaluated at a tuple w      *)
(* agreeing with v on the tensor slots.                                      *)

let RFA_DERIV_LNABLA = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y w v e.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U /\
        (!m. 1 <= m /\ m <= k ==> w m = v m)
        ==> drop(frechet_derivative (\z. lift(lnabla k G tf z w)) (at y) e) =
            drop(frechet_derivative
                   (\z. frechet_derivative (\x. lift(tf x v)) (at z) (w(k + 1)))
                   (at y) e) -
            sum(1..k) (\i. tf y (\j. if j = i
                                     then frechet_derivative
                                            (\z. christoffel G z (w(k + 1)) (v i))
                                            (at y) e
                                     else v j) +
                           drop(frechet_derivative
                                  (\z. lift(tf z (\j. if j = i
                                                      then christoffel G y (w(k + 1))
                                                                       (v i)
                                                      else v j)))
                                  (at y) e))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ABBREV_TAC `X:real^N = w(k + 1)` THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(lnabla k (G:real^N->real^N^N) tf z w)) (at y) =
    frechet_derivative
      (\z. frechet_derivative
             (\x. lift((tf:real^N->(num->real^N)->real) x v)) (at z) X -
           vsum(1..k) (\i. lift(tf z (\j. if j = i then christoffel G z X (v i)
                                          else v j))))
      (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `tf:real^N->(num->real^N)->real`; `z:real^N`;
                   `w:num->real^N`; `v:num->real^N`] RFA_LNABLA_REDUCE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LIFT_SUB; LIFT_DROP; LIFT_SUM; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. frechet_derivative
            (\x. lift((tf:real^N->(num->real^N)->real) x v)) (at z) X -
          vsum(1..k) (\i. lift(tf z (\j. if j = i
                                         then christoffel (G:real^N->real^N^N) z X (v i)
                                         else v j))))
     has_derivative
     (\e. frechet_derivative
            (\z. frechet_derivative (\x. lift(tf x v)) (at z) X) (at y) e -
          vsum(1..k)
            (\i. lift(tf y (\j. if j = i
                                then frechet_derivative
                                       (\z. christoffel G z X (v i)) (at y) e
                                else v j)) +
                 frechet_derivative
                   (\z. lift(tf z (\j. if j = i then christoffel G y X (v i)
                                       else v j)))
                   (at y) e))) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MP_TAC(ISPECL [`U:real^N->bool`;
                     `\x. lift((tf:real^N->(num->real^N)->real) x v)`;
                     `y:real^N`; `X:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                     `tf:real^N->(num->real^N)->real`; `y:real^N`; `i:num`;
                     `X:real^N`; `v:num->real^N`] RFA_DERIV_CTERM) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[DROP_SUB; DROP_VSUM; DROP_ADD; LIFT_DROP; o_DEF]);;

(* ========================================================================= *)
(* The second covariant derivative in explicit form, the cross               *)
(* terms, and the Ricci identity.                                            *)
(* ========================================================================= *)

let RFA_LNABLA2_EXPAND = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y X Y v.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
        ==> lnabla_iter k 2 G tf y
              (\m. if m = k + 1 then X else if m = k + 2 then Y else v m) =
            (drop(frechet_derivative
                   (\z. frechet_derivative (\x. lift(tf x v)) (at z) X) (at y) Y) -
             sum(1..k) (\i. tf y (\j. if j = i
                                      then frechet_derivative
                                             (\z. christoffel G z X (v i)) (at y) Y
                                      else v j) +
                            drop(frechet_derivative
                                   (\z. lift(tf z (\j. if j = i
                                                       then christoffel G y X (v i)
                                                       else v j)))
                                   (at y) Y))) -
            (sum(1..k) (\i. drop(frechet_derivative
                                   (\z. lift(tf z (\j. if j = i
                                                       then christoffel G y Y (v i)
                                                       else v j)))
                                   (at y) X) -
                            sum(1..k) (\j. tf y (\m. if m = j
                                                     then christoffel G y X
                                                            (if j = i
                                                             then christoffel G y Y (v i)
                                                             else v j)
                                                     else if m = i
                                                     then christoffel G y Y (v i)
                                                     else v m))) +
             (drop(frechet_derivative (\z. lift(tf z v)) (at y)
                     (christoffel G y Y X)) -
              sum(1..k) (\j. tf y (\m. if m = j
                                       then christoffel G y (christoffel G y Y X) (v j)
                                       else v m))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ABBREV_TAC `u':num->real^N = \m. if m = k + 1 then X else if m = k + 2 then Y
                                   else v m` THEN
  SUBGOAL_THEN `(u':num->real^N) (k + 1) = X /\ u' (k + 2) = Y /\
                (!m. 1 <= m /\ m <= k ==> u' m = v m)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u'" THEN REWRITE_TAC[ARITH_RULE `~(k + 2 = k + 1)`] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(m = k + 1) /\ ~(m = k + 2)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RFA_LNABLA_ITER_2] THEN
  GEN_REWRITE_TAC LAND_CONV [lnabla] THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2`] THEN ASM_REWRITE_TAC[] THEN
  BINOP_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `tf:real^N->(num->real^N)->real`; `y:real^N`;
                   `u':num->real^N`; `v:num->real^N`; `Y:real^N`]
           RFA_DERIV_LNABLA) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= k + 1`; SUM_SING_NUMSEG] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `tf:real^N->(num->real^N)->real`; `y:real^N`;
                   `\j. if j = i then christoffel (G:real^N->real^N^N) y Y
                                        ((u':num->real^N) i) else u' j`;
                   `\j. if j = i then christoffel (G:real^N->real^N^N) y Y
                                        ((v:num->real^N) i) else v j`]
           RFA_LNABLA_REDUCE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `~(k + 1 = i)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`;
                 `\j. if j = k + 1 then christoffel (G:real^N->real^N^N) y Y
                                      ((u':num->real^N) (k + 1)) else u' j`;
                 `v:num->real^N`] RFA_LNABLA_REDUCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* The terms with two Christoffel factors: off the diagonal they cancel     *)
(* under X <-> Y (no property of c or t is needed).                          *)

let RFA_CROSS_TERMS = prove
 (`!k (t:(num->real^N)->real) (c:real^N->real^N->real^N) X Y v.
        sum(1..k) (\i. sum(1..k) (\j. t (\m. if m = j
                                             then c X (if j = i then c Y (v i)
                                                       else v j)
                                             else if m = i then c Y (v i)
                                             else v m))) -
        sum(1..k) (\i. sum(1..k) (\j. t (\m. if m = j
                                             then c Y (if j = i then c X (v i)
                                                       else v j)
                                             else if m = i then c X (v i)
                                             else v m))) =
        sum(1..k) (\i. t (\m. if m = i then c X (c Y (v i)) else v m) -
                       t (\m. if m = i then c Y (c X (v i)) else v m))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..k) (\j. if j = i
                   then t (\m. if m = i then (c:real^N->real^N->real^N) X (c Y (v i))
                               else (v:num->real^N) m) -
                        t (\m. if m = i then c Y (c X (v i)) else v m)
                   else &0)` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN BINOP_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
    COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_0] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `m:num` THEN
  SUBGOAL_THEN `~(i:num = j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `m:num = i` THEN ASM_CASES_TAC `m:num = j` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let RFA_RICCI_IDENTITY = prove
 (`!k U (G:real^N->real^N^N) tf y u.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
        ==> lnabla_iter k 2 G tf y u -
            lnabla_iter k 2 G tf y
              (\m. if m = k + 1 then u(k + 2) else if m = k + 2 then u(k + 1)
                   else u m) =
            sum(1..k) (\i. tf y (\m. if m = i
                                     then lriemann G y (u(k + 1)) (u(k + 2)) (u i)
                                     else u m))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ABBREV_TAC `X:real^N = u(k + 1)` THEN ABBREV_TAC `Y:real^N = u(k + 2)` THEN
  SUBGOAL_THEN
   `(\m. if m = k + 1 then X else if m = k + 2 then Y else (u:num->real^N) m) = u`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
    ASM_CASES_TAC `m = k + 1` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `m = k + 2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `X:real^N`;
                 `Y:real^N`; `u:num->real^N`] RFA_LNABLA2_EXPAND) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `Y:real^N`;
                 `X:real^N`; `u:num->real^N`] RFA_LNABLA2_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `drop(frechet_derivative
          (\z. frechet_derivative
                 (\x. lift((tf:real^N->(num->real^N)->real) x u)) (at z) X)
          (at y) Y) =
    drop(frechet_derivative
          (\z. frechet_derivative (\x. lift(tf x u)) (at z) Y) (at y) X)`
  SUBST1_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC LRG_SECOND_DERIVATIVE_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `christoffel (G:real^N->real^N^N) y Y X = christoffel G y X Y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG] THEN
  MP_TAC(ISPECL [`k:num`; `(tf:real^N->(num->real^N)->real) y`;
                 `christoffel (G:real^N->real^N^N) y`; `X:real^N`; `Y:real^N`;
                 `u:num->real^N`] RFA_CROSS_TERMS) THEN
  SUBGOAL_THEN
   `sum(1..k) (\i. (tf:real^N->(num->real^N)->real) y
                     (\j. if j = i
                          then frechet_derivative
                                 (\z. christoffel (G:real^N->real^N^N) z Y (u i))
                                 (at y) X
                          else u j)) -
    sum(1..k) (\i. tf y (\j. if j = i
                             then frechet_derivative
                                    (\z. christoffel G z X (u i)) (at y) Y
                             else u j)) +
    sum(1..k) (\i. tf y (\m. if m = i then christoffel G y X (christoffel G y Y (u i))
                             else u m) -
                   tf y (\m. if m = i then christoffel G y Y (christoffel G y X (u i))
                             else u m)) =
    sum(1..k) (\i. tf y (\m. if m = i then lriemann G y X Y (u i) else u m))`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`;
                   `y:real^N`; `i:num`; `u:num->real^N`] RFA_SLOT_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[lriemann];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Operations that agree with a member of the class lbilin on                *)
(* tensor fields (lbilin_on), and their closure rules.  Goals of the form    *)
(* ?B. lbilin k p q B /\ (identity with B) follow from lbilin_on.            *)
(* ========================================================================= *)

let lbilin_on = new_definition
 `lbilin_on k p q
    (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) <=>
    ?B. lbilin k p q B /\
        !U G tf tg y u.
           metric_field U G /\ ltensor_field p U tf /\ ltensor_field q U tg /\
           y IN U
           ==> E G tf tg y u = B G tf tg y u`;;

let RFA_LBILIN_ON_LBILIN = prove
 (`!k p q (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin k p q B ==> lbilin_on k p q B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lbilin_on] THEN
  EXISTS_TAC `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real` THEN
  ASM_REWRITE_TAC[]);;

let RFA_LBILIN_ON_PROD = prove
 (`!p q. lbilin_on (p + q) p q
           (\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
             (tg:real^N->(num->real^N)->real). ltprod p tf tg)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_LBILIN THEN
  REWRITE_TAC[lbilin_RULES]);;

let RFA_LBILIN_ON_EQ = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) E'.
        lbilin_on k p q E /\
        (!U G tf tg y u.
           metric_field U G /\ ltensor_field p U tf /\ ltensor_field q U tg /\
           y IN U
           ==> E' G tf tg y u = E G tf tg y u)
        ==> lbilin_on k p q E'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN
   `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
      (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real` THEN
  ASM_MESON_TAC[]);;

let RFA_LBILIN_ON_PERM = prove
 (`!k p q s (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E /\ s permutes 1..k
        ==> lbilin_on k p q (\G tf tg. ltperm s (E G tf tg))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN
   `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
      (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `\G tf tg. ltperm s ((B:(real^N->real^N^N)->
                (real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->
                real^N->(num->real^N)->real) G tf tg)` THEN
  ASM_SIMP_TAC[lbilin_RULES] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[ltperm] THEN
  ASM_MESON_TAC[]);;

let RFA_LBILIN_ON_CONTR = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on (k + 2) p q E
        ==> lbilin_on k p q (\G tf tg. ltcontr G (E G tf tg))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
      (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\G tf tg. ltcontr G ((B:(real^N->real^N^N)->
                (real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->
                real^N->(num->real^N)->real) G tf tg)` THEN
  ASM_SIMP_TAC[lbilin_RULES] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[ltcontr] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
  STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[]);;

let RFA_LBILIN_ON_ADD = prove
 (`!k p q (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) E2.
        lbilin_on k p q E1 /\ lbilin_on k p q E2
        ==> lbilin_on k p q (\G tf tg y u. E1 G tf tg y u + E2 G tf tg y u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN
     `B1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
         (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
     STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN
     `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
         (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
     STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\G tf tg y u.
                (B1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                    (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                G tf tg y u +
                (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                    (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                G tf tg y u` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[lbilin_RULES];
    REPEAT STRIP_TAC THEN BETA_TAC THEN BINOP_TAC THEN ASM_MESON_TAC[]]);;

let RFA_LBILIN_ON_CMUL = prove
 (`!k p q c (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E
        ==> lbilin_on k p q (\G tf tg y u. c * E G tf tg y u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
      (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\G tf tg y u. c * (B:(real^N->real^N^N)->
                (real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->
                real^N->(num->real^N)->real) G tf tg y u` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[lbilin_RULES];
    REPEAT STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[]]);;

let RFA_LBILIN_ON_SUB = prove
 (`!k p q (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) E2.
        lbilin_on k p q E1 /\ lbilin_on k p q E2
        ==> lbilin_on k p q (\G tf tg y u. E1 G tf tg y u - E2 G tf tg y u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`; `--(&1)`;
    `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`]
    RFA_LBILIN_ON_CMUL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`;
    `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`;
    `\G tf tg y u. --(&1) *
       (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
           (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
       G tf tg y u`] RFA_LBILIN_ON_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `a + --(&1) * b = a - b`]);;

let RFA_LBILIN_ON_SUM = prove
 (`!k p q n (E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        1 <= n /\ (!i. 1 <= i /\ i <= n ==> lbilin_on k p q (E i))
        ==> lbilin_on k p q (\G tf tg y u. sum(1..n) (\i. E i G tf tg y u))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `~(1 <= 0)`]; ALL_TAC] THEN
  X_GEN_TAC `E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real` THEN
  STRIP_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_ADD_LID; ETA_AX] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`;
    `\G tf tg y u. sum(1..n) (\i. (E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i G tf tg y u)`;
    `(E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (SUC n)`] RFA_LBILIN_ON_ADD) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let RFA_LBILIN_ON_NORM = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E
        ==> ?C. &0 <= C /\
                !U G tf tg y.
                   metric_field U G /\ y IN U /\
                   ltensor_field p U tf /\ ltensor_field q U tg
                   ==> ltnorm2 k G (E G tf tg) y <=
                       C * ltnorm2 p G tf y * ltnorm2 q G tg y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree"))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RFA_LBILIN_NORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`;
                       `tf:real^N->(num->real^N)->real`;
                       `tg:real^N->(num->real^N)->real`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!u. (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg y u = (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg y u` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "agree" MATCH_MP_TAC THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 k (G:real^N->real^N^N) ((E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg) y =
    ltnorm2 k G ((B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg) y`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[ltnorm2]; ALL_TAC] THEN
  USE_THEN "bd" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Contraction of two arbitrary slots i < j (rfa_sig moves them              *)
(* to the front for ltcontr; rfa_ins describes the resulting argument        *)
(* tuple), and the metric expansion of a vector in one slot.                 *)
(* ========================================================================= *)

let rfa_sig = new_definition
 `rfa_sig i j = \m. if m = i then 1 else if m = j then 2
                    else if 1 <= m /\ m < i then m + 2
                    else if i < m /\ m < j then m + 1 else m`;;

let rfa_ins = new_definition
 `rfa_ins i j (v:real^N) (w:real^N) (u:num->real^N) =
    \m. if m = i then v else if m = j then w else if m < i then u m
        else if m < j then u(m - 1) else u(m - 2)`;;

let RFA_SIG_PERMUTES = prove
 (`!i j n. 1 <= i /\ i < j /\ j <= n ==> rfa_sig i j permutes 1..n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_sig] THEN
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 1 then i else if m = 2 then j
                  else if 3 <= m /\ m <= i + 1 then m - 2
                  else if i + 2 <= m /\ m <= j then m - 1 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_LTCONTR_SIG = prove
 (`!i j (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
        1 <= i /\ i < j
        ==> ltcontr G (ltperm (rfa_sig i j) tf) y u =
            sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\b. matrix_inv(G y)$a$b *
                    tf y (rfa_ins i j (basis a) (basis b) u)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltcontr; ltperm] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
  STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; rfa_sig; rfa_ins] THEN X_GEN_TAC `m:num` THEN
  ASM_CASES_TAC `m:num = i` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `m:num = j` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(j = 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(AP_TERM_TAC THEN ASM_ARITH_TAC) THEN ASM_ARITH_TAC);;

let RFA_LBILIN_ON_CTR_AT = prove
 (`!k p q i j (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                 (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on (k + 2) p q E /\ 1 <= i /\ i < j /\ j <= k + 2
        ==> lbilin_on k p q
              (\G tf tg y u.
                 sum(1..dimindex(:N))
                  (\a. sum(1..dimindex(:N))
                    (\b. matrix_inv(G y)$a$b *
                         E G tf tg y (rfa_ins i j (basis a) (basis b) u))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`;
    `\G tf tg. ltperm (rfa_sig i j)
       ((E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
           (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
        G tf tg)`] RFA_LBILIN_ON_CONTR) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC RFA_LBILIN_ON_PERM THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_SIG_PERMUTES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RFA_LTCONTR_SIG]);;

(* A vector in slot i, expanded against the metric. *)

let RFA_METRIC_EXPAND = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y i u v.
        metric_field U G /\ ltensor_field k U tf /\ y IN U /\ 1 <= i /\ i <= k
        ==> tf y (\m. if m = i then v else u m) =
            sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\b. matrix_inv(G y)$a$b * (basis a dot (G y ** v)) *
                    tf y (\m. if m = i then basis b else u m)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`(tf:real^N->(num->real^N)->real) y`; `i:num`;
                           `u:num->real^N`; `v:real^N`] LRG_SLOT_EXPAND)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ltensor_field]; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[SUM_SWAP_NUMSEG])) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC; SUM_RMUL] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. matrix_inv((G:real^N->real^N^N) y)$a$b = matrix_inv(G y)$b$a`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w:real^N = (G:real^N->real^N^N) y ** v` THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\a. matrix_inv((G:real^N->real^N^N) y)$b$a * (basis a dot w)) =
    (matrix_inv(G y) ** w)$b`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[DOT_BASIS];
    ALL_TAC] THEN
  EXPAND_TAC "w" THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]);;

(* ========================================================================= *)
(* The curvature action on the slots of a k-tensor                           *)
(* (rfa_ract, the right-hand side of the Ricci identity with Rm expanded    *)
(* against the metric) is in the class, and the Ricci identity in schematic *)
(* form.                                                                     *)
(* ========================================================================= *)

let rfa_ract = new_definition
 `rfa_ract k (G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
           (tf:real^N->(num->real^N)->real) y u =
    sum(1..k) (\i. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv(G y)$a$b *
       sf y (\m. if m = 1 then u(k + 1) else if m = 2 then u(k + 2)
                 else if m = 3 then basis a else u i) *
       tf y (\m. if m = i then basis b else u m))))`;;

let RFA_RACT_PERM = prove
 (`!k i. 1 <= i /\ i <= k
         ==> (\n. if n = 1 then k + 1 else if n = 2 then k + 2 else if n = 3 then i
                  else if 4 <= n /\ n <= i + 2 then n - 3
                  else if i + 3 <= n /\ n <= k + 2 then n - 2 else n)
             permutes 1..k + 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = k + 1 then 1 else if m = k + 2 then 2 else if m = i then 3
                  else if 1 <= m /\ m < i then m + 3
                  else if i < m /\ m <= k then m + 2 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_RACT_TERM = prove
 (`!k i. 1 <= i /\ i <= k
         ==> lbilin_on (k + 2) 4 k
               (\(G:real^N->real^N^N) sf tf y u.
                  sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
                    matrix_inv(G y)$a$b *
                    sf y (\m. if m = 1 then u(k + 1) else if m = 2 then u(k + 2)
                              else if m = 3 then basis a else u i) *
                    tf y (\m. if m = i then basis b else u m))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `tau = \n. if n = 1 then k + 1 else if n = 2 then k + 2
                        else if n = 3 then i
                        else if 4 <= n /\ n <= i + 2 then n - 3
                        else if i + 3 <= n /\ n <= k + 2 then n - 2 else n` THEN
  SUBGOAL_THEN `tau permutes 1..k + 2` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN MATCH_MP_TAC RFA_RACT_PERM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 2`; `4`; `k:num`; `3`; `4 + i`;
    `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
      (tf:real^N->(num->real^N)->real). ltprod 4 sf tf`] RFA_LBILIN_ON_CTR_AT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(k + 2) + 2 = 4 + k`] THEN
    REWRITE_TAC[RFA_LBILIN_ON_PROD] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `tau:num->num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ISPECL [`k + 2`; `4`; `k:num`] RFA_LBILIN_ON_PERM))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "tau" THEN
  UNDISCH_TAC `1 <= i` THEN UNDISCH_TAC `(i:num) <= k` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`;
                       `sf:real^N->(num->real^N)->real`;
                       `tf:real^N->(num->real^N)->real`; `y:real^N`;
                       `u:num->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[ltperm; ltprod] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
  STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN BINOP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
      check (fun th -> concl th = `ltensor_field 4 U (sf:real^N->(num->real^N)->real)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[rfa_ins] THEN
    ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[ARITH] THENL
     [SUBGOAL_THEN `~(1 = 4 + i)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `m = 2` THEN ASM_REWRITE_TAC[ARITH] THENL
     [SUBGOAL_THEN `~(2 = 4 + i)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `m = 3` THEN ASM_REWRITE_TAC[ARITH] THEN
    SUBGOAL_THEN `m = 4` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(4 = 4 + i) /\ 4 < 4 + i` (fun th -> REWRITE_TAC[th; ARITH]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
    check (fun th -> concl th = `ltensor_field k U (tf:real^N->(num->real^N)->real)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[rfa_ins] THEN
  SUBGOAL_THEN `~(m + 4 = 3) /\ ~(m + 4 < 3) /\ (m + 4 = 4 + i <=> m = i) /\
                (m + 4 < 4 + i <=> m < i)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `m:num = i` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `m < (i:num)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~((m + 4) - 1 = 1) /\ ~((m + 4) - 1 = 2) /\ ~((m + 4) - 1 = 3) /\
                  4 <= (m + 4) - 1 /\ (m + 4) - 1 <= i + 2 /\ ((m + 4) - 1) - 3 = m`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~((m + 4) - 2 = 1) /\ ~((m + 4) - 2 = 2) /\ ~((m + 4) - 2 = 3) /\
                  ~(4 <= (m + 4) - 2 /\ (m + 4) - 2 <= i + 2) /\
                  i + 3 <= (m + 4) - 2 /\ (m + 4) - 2 <= k + 2 /\
                  ((m + 4) - 2) - 2 = m`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

let RFA_RACT_LBILIN = prove
 (`!k. lbilin_on (k + 2) 4 k (rfa_ract k:(real^N->real^N^N)->
         (real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->
         real^N->(num->real^N)->real)`,
  GEN_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
    EXISTS_TAC `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
                 (tf:real^N->(num->real^N)->real) y u.
                 &0 * ltcontr G (ltprod 4 sf tf) y u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LBILIN_ON_CMUL THEN
      MP_TAC(ISPECL [`2`; `4`; `0`;
        `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
          (tf:real^N->(num->real^N)->real). ltprod 4 sf tf`] RFA_LBILIN_ON_CONTR) THEN
      REWRITE_TAC[ARITH_RULE `0 + 2 = 2 /\ 2 + 2 = 4 + 0`] THEN
      REWRITE_TAC[RFA_LBILIN_ON_PROD] THEN REWRITE_TAC[ETA_AX];
      REWRITE_TAC[rfa_ract; SUM_CLAUSES_NUMSEG; ARITH; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 2`; `4`; `k:num`; `k:num`;
    `\i (G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
       (tf:real^N->(num->real^N)->real) y u.
       sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
         matrix_inv(G y)$a$b *
         sf y (\m. if m = 1 then u(k + 1) else if m = 2 then u(k + 2)
                   else if m = 3 then basis a else u i) *
         tf y (\m. if m = i then basis b else u m)))`] RFA_LBILIN_ON_SUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_RACT_TERM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; rfa_ract]);;

let RFA_RACT_LRM4 = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
        metric_field U G /\ ltensor_field k U tf /\ y IN U
        ==> rfa_ract k G (lrm4 G) tf y u =
            sum(1..k) (\i. tf y (\m. if m = i
                                     then lriemann G y (u(k + 1)) (u(k + 2)) (u i)
                                     else u m))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ract; lrm4; ARITH] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `i:num`;
                 `u:num->real^N`;
                 `lriemann (G:real^N->real^N^N) y (u(k + 1)) (u(k + 2)) (u i)`]
         RFA_METRIC_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* The Ricci identity in schematic form (used for the commutator and the    *)
(* evolution of the curvature).                                              *)

let RFA_RICCI_IDENTITY_LB = prove
 (`!k. ?B. lbilin (k + 2) 4 k B /\
           !U (G:real^N->real^N^N) tf y u.
              metric_field U G /\ ltensor_field k U tf /\
              (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
              ==> lnabla_iter k 2 G tf y u -
                  lnabla_iter k 2 G tf y
                    (\m. if m = k + 1 then u(k + 2) else if m = k + 2 then u(k + 1)
                         else u m) =
                  B G (lrm4 G) tf y u`,
  GEN_TAC THEN
  MP_TAC(SPEC `k:num` (RFA_RACT_LBILIN:thm)) THEN
  REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
      (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree"))) THEN
  EXISTS_TAC `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
         RFA_RICCI_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
         RFA_RACT_LRM4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  USE_THEN "agree" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_MESON_TAC[LRM4_TENSOR_FIELD]);;

(* ========================================================================= *)
(* Substitution rules for lbilin_on: exchanging the arguments,               *)
(* and replacing an argument by a contraction or a permutation of it.       *)
(* ========================================================================= *)

let RFA_SWAP_PERMUTES = prove
 (`!p q. (\n. if 1 <= n /\ n <= q then n + p
              else if q + 1 <= n /\ n <= q + p then n - q else n)
         permutes 1..q + p`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\n. if 1 <= n /\ n <= p then n + q
                  else if p + 1 <= n /\ n <= p + q then n - p else n` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_LBILIN_ON_SWAP_BASE = prove
 (`!p q. lbilin_on (p + q) q p
           (\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
             (tf:real^N->(num->real^N)->real). ltprod p tf sf)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(p:num) + q = q + p` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`q + p:num`; `q:num`; `p:num`;
    `\n. if 1 <= n /\ n <= q then n + p
         else if q + 1 <= n /\ n <= q + p then n - q else n`;
    `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
      (tf:real^N->(num->real^N)->real). ltprod q sf tf`] RFA_LBILIN_ON_PERM) THEN
  REWRITE_TAC[RFA_LBILIN_ON_PROD; RFA_SWAP_PERMUTES] THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[ltperm; ltprod] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN BINOP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
      check (fun th -> concl th = `ltensor_field q U (tf:real^N->(num->real^N)->real)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
      check (fun th -> concl th = `ltensor_field p U (tg:real^N->(num->real^N)->real)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(1 <= m + q /\ m + q <= q) /\ q + 1 <= m + q /\ m + q <= q + p /\
                  (m + q) - q = m` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC]);;

let RFA_LBILIN_SWAP_IND = prove
 (`!k p q (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin k p q B ==> lbilin_on k q p (\G sf tf. B G tf sf)`,
  MATCH_MP_TAC lbilin_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  BETA_TAC THENL
   [REWRITE_TAC[RFA_LBILIN_ON_SWAP_BASE];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `q:num`; `p:num`; `s:num->num`;
                   `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf sf`] RFA_LBILIN_ON_PERM) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `q:num`; `p:num`;
                   `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf sf`] RFA_LBILIN_ON_CONTR) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `q:num`; `p:num`;
                   `\G sf tf. (B1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf sf`;
                   `\G sf tf. (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf sf`] RFA_LBILIN_ON_ADD) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `q:num`; `p:num`; `c:real`;
                   `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf sf`] RFA_LBILIN_ON_CMUL) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[]]);;

let RFA_LBILIN_ON_SWAP = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E ==> lbilin_on k q p (\G sf tf. E G tf sf)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `(B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real)` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree"))) THEN
  MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  EXISTS_TAC `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf sf` THEN
  ASM_SIMP_TAC[RFA_LBILIN_SWAP_IND] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "agree" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* Substituting a contraction for the first argument. *)

let RFA_LBILIN_SUBST1_CONTR_IND = prove
 (`!k p q (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin k p q B
        ==> lbilin_on k (p + 2) q (\G sf tf. B G (ltcontr G sf) tf)`,
  MATCH_MP_TAC lbilin_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  BETA_TAC THENL
   [MP_TAC(ISPECL [`p + q:num`; `p + 2`; `q:num`;
      `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
        (tf:real^N->(num->real^N)->real). ltprod (p + 2) sf tf`] RFA_LBILIN_ON_CONTR) THEN
    REWRITE_TAC[ARITH_RULE `(p + q) + 2 = (p + 2) + q`] THEN
    REWRITE_TAC[RFA_LBILIN_ON_PROD] THEN DISCH_TAC THEN
    MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[ltprod; ltcontr; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
      check (fun th -> concl th = `ltensor_field q U (tg:real^N->(num->real^N)->real)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(m + p + 2 = 1) /\ ~(m + p + 2 = 2) /\ (m + p + 2) - 2 = m + p`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `p + 2`; `q:num`; `s:num->num`;
                   `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltcontr G sf) tf`] RFA_LBILIN_ON_PERM) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `p + 2`; `q:num`;
                   `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltcontr G sf) tf`] RFA_LBILIN_ON_CONTR) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `p + 2`; `q:num`;
                   `\G sf tf. (B1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltcontr G sf) tf`;
                   `\G sf tf. (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltcontr G sf) tf`] RFA_LBILIN_ON_ADD) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `p + 2`; `q:num`; `c:real`;
                   `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltcontr G sf) tf`] RFA_LBILIN_ON_CMUL) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[]]);;

let RFA_LBILIN_ON_SUBST1_CONTR = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E
        ==> lbilin_on k (p + 2) q (\G sf tf. E G (ltcontr G sf) tf)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `(B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real)` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree"))) THEN
  MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  EXISTS_TAC `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltcontr G sf) tf` THEN
  ASM_SIMP_TAC[RFA_LBILIN_SUBST1_CONTR_IND] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "agree" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LTCONTR_FIELD THEN ASM_REWRITE_TAC[]);;

(* Substituting a permutation for the first argument. *)

let RFA_LBILIN_SUBST1_PERM_IND = prove
 (`!k p q (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin k p q B
        ==> !s. s permutes 1..p
                ==> lbilin_on k p q (\G sf tf. B G (ltperm s sf) tf)`,
  MATCH_MP_TAC lbilin_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  BETA_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`p + q:num`; `p:num`; `q:num`; `s:num->num`;
      `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
        (tf:real^N->(num->real^N)->real). ltprod p sf tf`] RFA_LBILIN_ON_PERM) THEN
    REWRITE_TAC[RFA_LBILIN_ON_PROD] THEN ANTS_TAC THENL
     [MATCH_MP_TAC PERMUTES_SUBSET THEN EXISTS_TAC `1..p` THEN
      ASM_REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ARITH_TAC;
      DISCH_TAC] THEN
    MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[ltprod; ltperm] THEN
    AP_TERM_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
      check (fun th -> concl th = `ltensor_field q U (tg:real^N->(num->real^N)->real)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [permutes]) THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`; `s:num->num`;
                   `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltperm r sf) tf`] RFA_LBILIN_ON_PERM) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`;
                   `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltperm r sf) tf`] RFA_LBILIN_ON_CONTR) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[];
    STRIP_TAC THEN X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`;
                   `\G sf tf. (B1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltperm r sf) tf`;
                   `\G sf tf. (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltperm r sf) tf`] RFA_LBILIN_ON_ADD) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`; `c:real`;
                   `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltperm r sf) tf`] RFA_LBILIN_ON_CMUL) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[]]);;

let RFA_LBILIN_ON_SUBST1_PERM = prove
 (`!k p q s (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E /\ s permutes 1..p
        ==> lbilin_on k p q (\G sf tf. E G (ltperm s sf) tf)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [lbilin_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `(B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real)` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree")))
    ASSUME_TAC) THEN
  MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  EXISTS_TAC `\G sf tf. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (ltperm s sf) tf` THEN
  ASM_SIMP_TAC[RFA_LBILIN_SUBST1_PERM_IND] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "agree" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[]);;

(* The same for the second argument, by exchanging the arguments. *)

let RFA_LBILIN_ON_SUBST2_CONTR = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E
        ==> lbilin_on k p (q + 2) (\G sf tf. E G sf (ltcontr G tf))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RFA_LBILIN_ON_SWAP) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_SUBST1_CONTR) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_SWAP) THEN REWRITE_TAC[]);;

let RFA_LBILIN_ON_SUBST2_PERM = prove
 (`!k p q s (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E /\ s permutes 1..q
        ==> lbilin_on k p q (\G sf tf. E G sf (ltperm s tf))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RFA_LBILIN_ON_SWAP) THEN
  DISCH_THEN(MP_TAC o SPEC `s:num->num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    RFA_LBILIN_ON_SUBST1_PERM)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_SWAP) THEN REWRITE_TAC[]);;

(* Members of the class depend on the metric and the arguments only through *)
(* their values at the point.                                                *)

let RFA_LBILIN_LOCAL = prove
 (`!k p q (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin k p q B
        ==> !G G' tf tf' tg tg' y.
               G y = G' y /\ tf y = tf' y /\ tg y = tg' y
               ==> B G tf tg y = B G' tf' tg' y`,
  MATCH_MP_TAC lbilin_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  BETA_TAC THENL
   [STRIP_TAC THEN REWRITE_TAC[ltprod; FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[ltperm; FUN_EQ_THM] THEN GEN_TAC THEN AP_THM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[ltcontr; FUN_EQ_THM] THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BINOP_TAC THEN AP_THM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

