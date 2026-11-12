(* ========================================================================= *)
(* Unit pc_p2a_lgeo1: chart level of the L-geodesic equation (MT eq. (6.5)   *)
(* in s = sqrt tau), dimension-generic.  Ricci flows read in a chart are     *)
(* local Ricci flows; joint smoothness in (s,y) of the Christoffel, Riemann, *)
(* Ricci and scalar terms, of grad R and of the Ricci operator for a smooth  *)
(* family of local metrics; smoothness of the first-order field p2a_lfield   *)
(* (input of the ODE package pc_ode_vf).                                     *)
(* ========================================================================= *)

needs "src/pc_p2a_defs.ml";;
needs "src/pc_ode_vf.ml";;
needs "src/pc_lrg_evol.ml";;
needs "src/pc_lrg_flowsmooth.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A Ricci flow read in an atlas chart is a local Ricci flow on the chart   *)
(* image: LRG_RICCI_FLOW_ON_CHART of pc_lrg_flowsmooth (proved there, the  *)
(* name below is kept for the units that use it).                           *)
(* ------------------------------------------------------------------------- *)

let P2A_RICCI_FLOW_ON_CHART = LRG_RICCI_FLOW_ON_CHART;;

(* ========================================================================= *)
(* Joint smoothness in (s,y) for a smooth family of local metrics.  The      *)
(* lemmas are proved in pc_lrg_flowsmooth for lrg_lsmooth (the same text as  *)
(* p2a_lsmooth); the theorems below are the same theorems read with          *)
(* p2a_lsmooth.  P2A_LSMOOTH_LGRADR (p2a_lgradR is defined in pc_p2a_defs)   *)
(* is proved here.                                                           *)
(* ========================================================================= *)

let P2A_LSMOOTH_ALT = prove
 (`!U ta tb (Gt:real->real^N->real^N^N).
     p2a_lsmooth U ta tb Gt <=> lrg_lsmooth U ta tb Gt`,
  REWRITE_TAC[p2a_lsmooth; lrg_lsmooth]);;

let P2A_LSMOOTH_BASIC = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_BASIC;;
let P2A_LSMOOTH_MDERIV = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_MDERIV;;
let P2A_LSMOOTH_MDERIV_ENTRY = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_MDERIV_ENTRY;;
let P2A_LSMOOTH_GINV = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_GINV;;
let P2A_LSMOOTH_CHRISTOFFEL = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_CHRISTOFFEL;;
let P2A_LSMOOTH_AT = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_AT;;
let P2A_LSMOOTH_DCHRISTOFFEL = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_DCHRISTOFFEL;;
let P2A_LSMOOTH_CHRISTOFFEL_ARG = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_CHRISTOFFEL_ARG;;
let P2A_LSMOOTH_CHRISTOFFEL2 = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_CHRISTOFFEL2;;
let P2A_LSMOOTH_LRIEMANN = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_LRIEMANN;;
let P2A_LSMOOTH_LRICCI = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_LRICCI;;
let P2A_LSMOOTH_GINV_ENTRY = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_GINV_ENTRY;;
let P2A_LSMOOTH_LSCALAR = PURE_REWRITE_RULE[GSYM P2A_LSMOOTH_ALT] LRG_LSMOOTH_LSCALAR;;

let P2A_JOINT_PARTIAL = LRG_JOINT_PARTIAL;;
let P2A_SMOOTH_LINEAR_ARG = LRG_SMOOTH_LINEAR_ARG;;
let P2A_SMOOTH_LIFT_MUL = LRG_SMOOTH_LIFT_MUL;;
let P2A_SMOOTH_LIFT_SUM = LRG_SMOOTH_LIFT_SUM;;

let P2A_LSMOOTH_LGRADR = prove
 (`!U ta tb (G:real->real^N->real^N^N).
     p2a_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. p2a_lgradR (G (drop(fstcart z))) (sndcart z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  REWRITE_TAC[p2a_lgradR] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_SIMP_TAC[P2A_LSMOOTH_GINV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LAMBDA THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
                 `\z. lift(lscalar ((G:real->real^N->real^N^N) (drop(fstcart z)))
                                   (sndcart z))`;
                 `basis k:real^N`] P2A_JOINT_PARTIAL) THEN
  ASM_SIMP_TAC[P2A_LSMOOTH_LSCALAR; FSTCART_PASTECART; SNDCART_PASTECART]);;

(* ========================================================================= *)
(* The first-order field of the L-geodesic system is smooth on (sa,sb) x U x *)
(* real^N when the s-family s |-> Gt(tt - s^2) is a smooth family of local   *)
(* metrics on U.                                                             *)
(* ========================================================================= *)

let P2A_SMOOTH_PROJ = prove
 (`!sa sb U (Fn:real^(1,N)finite_sum->real^P).
     open U /\ smooth_map_on (interval(lift sa,lift sb) PCROSS U) Fn
     ==> smooth_map_on (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N)))
           (\z. Fn(pastecart (fstcart z) (fstcart(sndcart z))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z:real^(1,(N,N)finite_sum)finite_sum.
       (Fn:real^(1,N)finite_sum->real^P) (pastecart (fstcart z) (fstcart(sndcart z)))) =
    Fn o (\z. pastecart (fstcart z) (fstcart(sndcart z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift sa,lift sb) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GEOL_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; IN_UNIV] THEN MESON_TAC[];
    MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                PASTECART_ADD; PASTECART_CMUL]]);;

let P2A_SMOOTH_RMUL = prove
 (`!s (c:real^M->real) (f:real^M->real^N).
     open s /\ smooth_map_on s (\x. lift(c x)) /\ smooth_map_on s f
     ==> smooth_map_on s (\x. c x % f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(c x)`; `f:real^M->real^N`]
                SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX]);;

let P2A_SMOOTH_LAMBDA = prove
 (`!s (g:num->real^M->real).
     open s /\ (!k. 1 <= k /\ k <= dimindex(:N) ==> smooth_map_on s (\x. lift(g k x)))
     ==> smooth_map_on s (\x. (lambda k. g k x):real^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\k x. lift((g:num->real^M->real) k x)`]
                SMOOTH_MAP_ON_LAMBDA) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2A_LFIELD_SMOOTH = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2))
     ==> smooth_map_on (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N)))
                       (p2a_lfield Gt tt)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `H = \s. (Gt:real->real^N->real^N^N)(tt - s pow 2)` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  ABBREV_TAC `W = interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
  SUBGOAL_THEN `open (W:real^(1,(N,N)finite_sum)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN (W:real^(1,(N,N)finite_sum)finite_sum->bool)
        ==> metric_field U ((H:real->real^N->real^N^N) (drop(fstcart z))) /\
            fstcart(sndcart z) IN U`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[GEOL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (W:real^(1,(N,N)finite_sum)finite_sum->bool) (\z:real^(1,(N,N)finite_sum)finite_sum. sndcart(sndcart z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear; SNDCART_ADD; SNDCART_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (W:real^(1,(N,N)finite_sum)finite_sum->bool) (\z:real^(1,(N,N)finite_sum)finite_sum. lift(drop(fstcart z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL];
    ALL_TAC] THEN
  (* coefficient functions *)
  SUBGOAL_THEN
   `!i j. smooth_map_on (W:real^(1,(N,N)finite_sum)finite_sum->bool)
            (\z. christoffel ((H:real->real^N->real^N^N) (drop(fstcart z)))
                             (fstcart(sndcart z)) (basis i) (basis j))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`sa:real`; `sb:real`; `U:real^N->bool`;
     `\z:real^(1,N)finite_sum. christoffel ((H:real->real^N->real^N^N) (drop(fstcart z)))
                                           (sndcart z) (basis i) (basis j)`] P2A_SMOOTH_PROJ) THEN
    ASM_SIMP_TAC[P2A_LSMOOTH_CHRISTOFFEL; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i k. smooth_map_on (W:real^(1,(N,N)finite_sum)finite_sum->bool)
            (\z. lift(lricci ((H:real->real^N->real^N^N) (drop(fstcart z)))
                             (fstcart(sndcart z)) (basis i) (basis k)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`sa:real`; `sb:real`; `U:real^N->bool`;
     `\z:real^(1,N)finite_sum. lift(lricci ((H:real->real^N->real^N^N) (drop(fstcart z)))
                                           (sndcart z) (basis i) (basis k))`] P2A_SMOOTH_PROJ) THEN
    ASM_SIMP_TAC[P2A_LSMOOTH_LRICCI; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (W:real^(1,(N,N)finite_sum)finite_sum->bool)
      (\z. p2a_lgradR ((H:real->real^N->real^N^N) (drop(fstcart z))) (fstcart(sndcart z)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sa:real`; `sb:real`; `U:real^N->bool`;
     `\z:real^(1,N)finite_sum. p2a_lgradR ((H:real->real^N->real^N^N) (drop(fstcart z)))
                                          (sndcart z)`] P2A_SMOOTH_PROJ) THEN
    ASM_SIMP_TAC[P2A_LSMOOTH_LGRADR; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (W:real^(1,(N,N)finite_sum)finite_sum->bool)
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       (\z. matrix_inv((H:real->real^N->real^N^N) (drop(fstcart z)) (fstcart(sndcart z)))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sa:real`; `sb:real`; `U:real^N->bool`;
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z:real^(1,N)finite_sum. matrix_inv((H:real->real^N->real^N^N) (drop(fstcart z))
                                                                      (sndcart z)))`] P2A_SMOOTH_PROJ) THEN
    ASM_SIMP_TAC[P2A_LSMOOTH_GINV; o_DEF; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  (* the A-dependent terms *)
  SUBGOAL_THEN
   `smooth_map_on (W:real^(1,(N,N)finite_sum)finite_sum->bool)
      (\z. christoffel ((H:real->real^N->real^N^N) (drop(fstcart z))) (fstcart(sndcart z))
                       (sndcart(sndcart z)) (sndcart(sndcart z)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`W:real^(1,(N,N)finite_sum)finite_sum->bool`;
      `\z:real^(1,(N,N)finite_sum)finite_sum.
         christoffel ((H:real->real^N->real^N^N) (drop(fstcart z))) (fstcart(sndcart z))
                     (sndcart(sndcart z))`;
      `\z:real^(1,(N,N)finite_sum)finite_sum. sndcart(sndcart z)`]
     P2A_SMOOTH_LINEAR_ARG) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^(1,(N,N)finite_sum)finite_sum` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`;
                     `(H:real->real^N->real^N^N) (drop(fstcart(z:real^(1,(N,N)finite_sum)finite_sum)))`;
                     `fstcart(sndcart(z:real^(1,(N,N)finite_sum)finite_sum))`]
                    LRG_CHRISTOFFEL_LINEAR) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`W:real^(1,(N,N)finite_sum)finite_sum->bool`;
      `\z:real^(1,(N,N)finite_sum)finite_sum a.
         christoffel ((H:real->real^N->real^N^N) (drop(fstcart z))) (fstcart(sndcart z))
                     a (basis j)`;
      `\z:real^(1,(N,N)finite_sum)finite_sum. sndcart(sndcart z)`]
     P2A_SMOOTH_LINEAR_ARG) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^(1,(N,N)finite_sum)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `(H:real->real^N->real^N^N) (drop(fstcart(z:real^(1,(N,N)finite_sum)finite_sum)))`;
                   `fstcart(sndcart(z:real^(1,(N,N)finite_sum)finite_sum))`]
                  LRG_CHRISTOFFEL_LINEAR) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (W:real^(1,(N,N)finite_sum)finite_sum->bool)
      (\z. p2a_lricop ((H:real->real^N->real^N^N) (drop(fstcart z))) (fstcart(sndcart z))
                      (sndcart(sndcart z)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2a_lricop] THEN MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_SMOOTH_LAMBDA THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`W:real^(1,(N,N)finite_sum)finite_sum->bool`;
      `\z:real^(1,(N,N)finite_sum)finite_sum a.
         lift(lricci ((H:real->real^N->real^N^N) (drop(fstcart z))) (fstcart(sndcart z))
                     a (basis k))`;
      `\z:real^(1,(N,N)finite_sum)finite_sum. sndcart(sndcart z)`]
     P2A_SMOOTH_LINEAR_ARG) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^(1,(N,N)finite_sum)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `(H:real->real^N->real^N^N) (drop(fstcart(z:real^(1,(N,N)finite_sum)finite_sum)))`;
                   `fstcart(sndcart(z:real^(1,(N,N)finite_sum)finite_sum))`]
                  LRG_LRICCI_LINEAR) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* assemble *)
  SUBGOAL_THEN
   `p2a_lfield Gt tt =
    (\z. pastecart (sndcart(sndcart z))
           (--(christoffel ((H:real->real^N->real^N^N) (drop(fstcart z)))
                           (fstcart(sndcart z)) (sndcart(sndcart z)) (sndcart(sndcart z))) +
            (&2 * drop(fstcart z) pow 2) %
              p2a_lgradR (H (drop(fstcart z))) (fstcart(sndcart z)) -
            (&4 * drop(fstcart z)) %
              p2a_lricop (H (drop(fstcart z))) (fstcart(sndcart z)) (sndcart(sndcart z))))`
  SUBST1_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[FUN_EQ_THM; p2a_lfield; p2a_lacc]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_NEG_OPEN] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC P2A_SMOOTH_RMUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`W:real^(1,(N,N)finite_sum)finite_sum->bool`;
                 `\z:real^(1,(N,N)finite_sum)finite_sum. lift(drop(fstcart z))`; `2`]
                SMOOTH_MAP_ON_LIFT_POW) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX]);;

(* ========================================================================= *)
(* Change of chart.  For a diffeomorphism h with G = mpullback h G', grad R  *)
(* and the Ricci operator are vectors (Dh grad_G R = grad_G' R at h y, Dh    *)
(* Ric_G(v) = Ric_G'(Dh v)), and the L-geodesic acceleration transforms with *)
(* the second derivative of h (P2A_LACC_PULLBACK); so chart curves of        *)
(* solutions are carried to chart curves of solutions (P2A_LSOL_TRANS,       *)
(* derivatives within any set).                                              *)
(* ========================================================================= *)

let P2A_PULLBACK_SOLVE = prove
 (`!(J:real^N^N) (B:real^N^N) (w:real^N).
     invertible J /\ invertible B
     ==> J ** (matrix_inv(transp J ** B ** J) ** (transp J ** w)) = matrix_inv B ** w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible(transp(J:real^N^N))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_TRANSP]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible((B:real^N^N) ** (J:real^N^N))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_MATRIX_MUL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_INV_MUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_LID; MATRIX_MUL_RID] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let P2A_LGRADR_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y.
     metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
     ==> frechet_derivative h (at y) (p2a_lgradR (mpullback h G) y) =
         p2a_lgradR G (h y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_JACOBIAN_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(U':real^N->bool) /\ open(U:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(lscalar (G:real^N->real^N^N) z))` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\z. lift(lscalar (G:real^N->real^N^N) z)) (at ((h:real^N->real^N) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((lambda k. drop(frechet_derivative
                       (\z. lift(lscalar (mpullback h (G:real^N->real^N^N)) z))
                       (at y) (basis k))):real^N) =
    transp(matrix(frechet_derivative (h:real^N->real^N) (at y))) **
    ((lambda k. drop(frechet_derivative (\z. lift(lscalar G z)) (at (h y)) (basis k))):real^N)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `frechet_derivative (\z. lift(lscalar (mpullback h (G:real^N->real^N^N)) z)) (at y) =
      frechet_derivative (\z. lift((lscalar G o (h:real^N->real^N)) z)) (at y)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `U':real^N->bool` THEN ASM_REWRITE_TAC[o_THM] THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC LSCALAR_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `lscalar (G:real^N->real^N^N)`; `y:real^N`]
                  LRG_COMPOSE_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_VECTOR_MUL_COMPONENT] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`frechet_derivative (\z. lift(lscalar (G:real^N->real^N^N) z))
                                       (at ((h:real^N->real^N) y))`;
                   `frechet_derivative (h:real^N->real^N) (at y)`; `k:num`]
                  LRG_DROP_LINEAR_MATRIX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; TRANSP_COMPONENT] THEN
    ASM_SIMP_TAC[transp; LAMBDA_BETA];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_lgradR] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN
   `!v. frechet_derivative (h:real^N->real^N) (at y) v =
        matrix(frechet_derivative h (at y)) ** v`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[MATRIX_WORKS]; ALL_TAC] THEN
  MATCH_MP_TAC P2A_PULLBACK_SOLVE THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(h:real^N->real^N) y`]
                LRG_METRIC_INVERTIBLE) THEN
  ASM_SIMP_TAC[]);;

let P2A_LRICOP_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y v.
     metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
     ==> frechet_derivative h (at y) (p2a_lricop (mpullback h G) y v) =
         p2a_lricop G (h y) (frechet_derivative h (at y) v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_JACOBIAN_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `linear(\w. lift(lricci (G:real^N->real^N^N) ((h:real^N->real^N) y)
                           (frechet_derivative h (at y) v) w))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(h:real^N->real^N) y`]
                  LRG_LRICCI_LINEAR) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((lambda k. lricci (mpullback h (G:real^N->real^N^N)) y v (basis k)):real^N) =
    transp(matrix(frechet_derivative (h:real^N->real^N) (at y))) **
    ((lambda k. lricci G (h y) (frechet_derivative h (at y) v) (basis k)):real^N)`
  ASSUME_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_VECTOR_MUL_COMPONENT] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`;
                   `basis k:real^N`] LRICCI_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`\w. lift(lricci (G:real^N->real^N^N) ((h:real^N->real^N) y)
                                    (frechet_derivative h (at y) v) w)`;
                   `frechet_derivative (h:real^N->real^N) (at y)`; `k:num`]
                  LRG_DROP_LINEAR_MATRIX) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; TRANSP_COMPONENT] THEN
    ASM_SIMP_TAC[transp; LAMBDA_BETA];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_lricop] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN
   `!w. frechet_derivative (h:real^N->real^N) (at y) w =
        matrix(frechet_derivative h (at y)) ** w`
  (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
   [ASM_SIMP_TAC[MATRIX_WORKS]; ALL_TAC] THEN
  MATCH_MP_TAC P2A_PULLBACK_SOLVE THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(h:real^N->real^N) y`]
                LRG_METRIC_INVERTIBLE) THEN
  ASM_SIMP_TAC[]);;

let P2A_LGRADR_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y.
     open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
     ==> p2a_lgradR G1 y = p2a_lgradR G2 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_lgradR] THEN
  BINOP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(lscalar (G1:real^N->real^N^N) z)) (at y) =
    frechet_derivative (\z. lift(lscalar G2 z)) (at y)`
  (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P2A_LRICOP_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y v.
     open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
     ==> p2a_lricop G1 y v = p2a_lricop G2 y v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_lricop] THEN
  BINOP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P2A_LACC_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' (Gt:real->real^N->real^N^N) Gt' tt s y A.
     metric_field U (Gt'(tt - s pow 2)) /\ diffeomorphism_on U' U h h' /\ y IN U' /\
     (!z. z IN U' ==> Gt(tt - s pow 2) z = mpullback h (Gt'(tt - s pow 2)) z)
     ==> frechet_derivative h (at y) (p2a_lacc Gt tt s y A) + dd2 h y A A =
         p2a_lacc Gt' tt s (h y) (frechet_derivative h (at y) A)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U':real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  REWRITE_TAC[p2a_lacc] THEN
  SUBGOAL_THEN
   `christoffel ((Gt:real->real^N->real^N^N)(tt - s pow 2)) y A A =
    christoffel (mpullback (h:real^N->real^N) (Gt'(tt - s pow 2))) y A A /\
    p2a_lgradR (Gt(tt - s pow 2)) y = p2a_lgradR (mpullback h (Gt'(tt - s pow 2))) y /\
    p2a_lricop (Gt(tt - s pow 2)) y A = p2a_lricop (mpullback h (Gt'(tt - s pow 2))) y A`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CHRISTOFFEL_LOCAL; MATCH_MP_TAC P2A_LGRADR_LOCAL;
      MATCH_MP_TAC P2A_LRICOP_LOCAL] THEN
    EXISTS_TAC `U':real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_SUB; LINEAR_CMUL; LINEAR_NEG] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `(Gt':real->real^N->real^N^N)(tt - s pow 2)`;
                 `y:real^N`; `A:real^N`; `A:real^N`] LCHRISTOFFEL_PULLBACK) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `(Gt':real->real^N->real^N^N)(tt - s pow 2)`;
                 `y:real^N`] P2A_LGRADR_PULLBACK) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `(Gt':real->real^N->real^N^N)(tt - s pow 2)`;
                 `y:real^N`; `A:real^N`] P2A_LRICOP_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN VECTOR_ARITH_TAC);;

(* Within-version of GEOL_FRECHET_ALONG (pc_geo_local), adapted from its proof. *)

let P2A_FRECHET_ALONG_WITHIN = prove
 (`!s (h:real^N->real^M) (y:real^1->real^N) (v:real^1->real^N) y' v' t S.
        open s /\ smooth_map_on s h /\ y t IN s /\ t IN S /\
        (y has_vector_derivative y') (at t within S) /\
        (v has_vector_derivative v') (at t within S)
        ==> ((\r. frechet_derivative h (at (y r)) (v r)) has_vector_derivative
             (frechet_derivative (\z. frechet_derivative h (at z) (v t))
                                 (at (y t)) y' +
              frechet_derivative h (at (y t)) v')) (at t within S)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN s ==> linear(frechet_derivative (h:real^N->real^M) (at z))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[LINEAR_FRECHET_DERIVATIVE; SMOOTH_MAP_ON_DIFFERENTIABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ((\z. frechet_derivative (h:real^N->real^M) (at z) (basis i))
         has_derivative
         frechet_derivative (\z. frechet_derivative h (at z) (basis i))
                            (at ((y:real^1->real^N) t))) (at (y t))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  (* the derivative of the expanded form *)
  SUBGOAL_THEN
   `((\r. vsum (1..dimindex(:N))
            (\i. drop(lift(((v:real^1->real^N) r)$i)) %
                 frechet_derivative (h:real^N->real^M) (at (y r)) (basis i)))
     has_vector_derivative
     vsum (1..dimindex(:N))
       (\i. drop(lift((v t)$i)) %
            frechet_derivative
              (\z. frechet_derivative h (at z) (basis i)) (at (y t)) y' +
            drop(lift((v':real^N)$i)) % frechet_derivative h (at (y t)) (basis i)))
    (at t within S)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_HAS_VECTOR_DERIVATIVE_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\x:real^1 w:real^M. drop x % w`;
      `\r. lift(((v:real^1->real^N) r)$i)`;
      `\r. frechet_derivative (h:real^N->real^M) (at ((y:real^1->real^N) r))
                              (basis i)`;
      `lift((v':real^N)$i)`;
      `frechet_derivative
         (\z. frechet_derivative (h:real^N->real^M) (at z) (basis i))
         (at ((y:real^1->real^N) t)) y'`;
      `t:real^1`; `S:real^1->bool`] HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN) THEN
    BETA_TAC THEN REWRITE_TAC[BILINEAR_DROP_MUL] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_WITHIN THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL
       [`y:real^1->real^N`;
        `\z. frechet_derivative (h:real^N->real^M) (at z) (basis i)`;
        `y':real^N`;
        `frechet_derivative
           (\z. frechet_derivative (h:real^N->real^M) (at z) (basis i))
           (at ((y:real^1->real^N) t))`;
        `t:real^1`; `S:real^1->bool`] GRGD_VECTOR_DERIVATIVE_CHAIN) THEN
      ASM_REWRITE_TAC[o_DEF]];
    ALL_TAC] THEN
  (* identify the derivative *)
  SUBGOAL_THEN
   `vsum (1..dimindex(:N))
       (\i. drop(lift(((v:real^1->real^N) t)$i)) %
            frechet_derivative
              (\z. frechet_derivative (h:real^N->real^M) (at z) (basis i))
              (at ((y:real^1->real^N) t)) y' +
            drop(lift((v':real^N)$i)) % frechet_derivative h (at (y t)) (basis i)) =
    frechet_derivative (\z. frechet_derivative h (at z) (v t)) (at (y t)) y' +
    frechet_derivative h (at (y t)) v'`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [SIMP_TAC[VSUM_ADD; FINITE_NUMSEG] THEN BINOP_TAC THENL
     [ALL_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOL_LINEAR_EXPAND THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN
     `((\z. frechet_derivative (h:real^N->real^M) (at z) ((v:real^1->real^N) t))
       has_derivative
       (\u. vsum (1..dimindex(:N))
              (\i. drop(lift((v t)$i)) %
                   frechet_derivative
                     (\z. frechet_derivative h (at z) (basis i))
                     (at ((y:real^1->real^N) t)) u))) (at (y t))`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      EXISTS_TAC
       `\z. vsum (1..dimindex(:N))
              (\i. drop(lift(((v:real^1->real^N) t)$i)) %
                   frechet_derivative (h:real^N->real^M) (at z) (basis i))` THEN
      EXISTS_TAC `s:real^N->bool` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOL_LINEAR_EXPAND THEN
        REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(INST
       [`\i:num u:real^N. drop(lift(((v:real^1->real^N) t)$i)) %
                  frechet_derivative
                    (\z. frechet_derivative (h:real^N->real^M) (at z) (basis i))
                    (at ((y:real^1->real^N) t)) u`,`f':num->real^N->real^M`]
       (ISPECL
       [`\i:num z. drop(lift(((v:real^1->real^N) t)$i)) %
                   frechet_derivative (h:real^N->real^M) (at z) (basis i)`;
        `at ((y:real^1->real^N) t)`; `1..dimindex(:N)`] HAS_DERIVATIVE_VSUM)) THEN
      BETA_TAC THEN REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[ETA_AX] THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)])];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  EXISTS_TAC
   `\r. vsum (1..dimindex(:N))
          (\i. drop(lift(((v:real^1->real^N) r)$i)) %
               frechet_derivative (h:real^N->real^M) (at (y r)) (basis i))` THEN
  SUBGOAL_THEN `(y:real^1->real^N) continuous (at t within S)` MP_TAC THENL
   [ASM_MESON_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN; differentiable;
                  has_vector_derivative]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(y:real^1->real^N) t` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[continuous_within] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOL_LINEAR_EXPAND THEN
  REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
    `!z:real^N. z IN s ==> linear(frechet_derivative (h:real^N->real^M) (at z))`)
    (concl th))) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  ASM_SIMP_TAC[]);;

let P2A_LSOL_TRANS = prove
 (`!U U' (h:real^N->real^N) h' (Gt:real->real^N->real^N^N) Gt' tt
    (Y:real^1->real^N) (V:real^1->real^N) t S.
     diffeomorphism_on U' U h h' /\ metric_field U (Gt'(tt - drop t pow 2)) /\
     (!z. z IN U' ==> Gt(tt - drop t pow 2) z = mpullback h (Gt'(tt - drop t pow 2)) z) /\
     Y t IN U' /\ t IN S /\
     (Y has_vector_derivative V t) (at t within S) /\
     (V has_vector_derivative p2a_lacc Gt tt (drop t) (Y t) (V t)) (at t within S)
     ==> ((\r. h(Y r)) has_vector_derivative frechet_derivative h (at (Y t)) (V t))
           (at t within S) /\
         ((\r. frechet_derivative h (at (Y r)) (V r)) has_vector_derivative
          p2a_lacc Gt' tt (drop t) (h(Y t)) (frechet_derivative h (at (Y t)) (V t)))
           (at t within S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U':real^N->bool) /\ smooth_map_on U' (h:real^N->real^N)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`Y:real^1->real^N`; `h:real^N->real^N`; `(V:real^1->real^N) t`;
                   `frechet_derivative (h:real^N->real^N) (at ((Y:real^1->real^N) t))`;
                   `t:real^1`; `S:real^1->bool`] GRGD_VECTOR_DERIVATIVE_CHAIN) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U':real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`; `Y:real^1->real^N`;
                 `V:real^1->real^N`; `(V:real^1->real^N) t`;
                 `p2a_lacc (Gt:real->real^N->real^N^N) tt (drop t)
                           ((Y:real^1->real^N) t) ((V:real^1->real^N) t)`;
                 `t:real^1`; `S:real^1->bool`] P2A_FRECHET_ALONG_WITHIN) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `(a:real^N) = b ==> (f has_vector_derivative a) net
                                         ==> (f has_vector_derivative b) net`) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `Gt:real->real^N->real^N^N`;
                 `Gt':real->real^N->real^N^N`; `tt:real`; `drop t`;
                 `(Y:real^1->real^N) t`; `(V:real^1->real^N) t`] P2A_LACC_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[dd2] THEN VECTOR_ARITH_TAC);;


(* ========================================================================= *)
(* Chart solutions as solutions of the ODE package (state pastecart y A,     *)
(* field p2a_lfield), and their uniqueness.                                  *)
(* ========================================================================= *)

let P2A_HVD_PASTECART_EQ = prove
 (`!(f:real^1->real^M) (g:real^1->real^N) f' g' net.
     ((\x. pastecart (f x) (g x)) has_vector_derivative pastecart f' g') net <=>
     (f has_vector_derivative f') net /\ (g has_vector_derivative g') net`,
  REWRITE_TAC[has_vector_derivative; GSYM PASTECART_CMUL; HAS_DERIVATIVE_PASTECART_EQ]);;

let P2A_LSOL_ODE = prove
 (`!(Gt:real->real^N->real^N^N) tt D J (Y:real^1->real^N) (V:real^1->real^N).
     ode_solution (p2a_lfield Gt tt) D J (\t. pastecart (Y t) (V t)) <=>
     is_interval J /\
     !t. t IN J
         ==> pastecart t (pastecart (Y t) (V t)) IN D /\
             (Y has_vector_derivative V t) (at t within J) /\
             (V has_vector_derivative p2a_lacc Gt tt (drop t) (Y t) (V t))
               (at t within J)`,
  REWRITE_TAC[ode_solution; p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART;
              P2A_HVD_PASTECART_EQ; CONJ_ASSOC]);;

let P2A_LFIELD_ODE_FACTS = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2))
     ==> open(interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N))) /\
         smooth_map_on (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N)))
                       (p2a_lfield Gt tt) /\
         p2a_lfield Gt tt continuous_on
           (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N))) /\
         ode_locally_lipschitz (p2a_lfield Gt tt)
           (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  SUBGOAL_THEN `open(interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LFIELD_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p2a_lfield (Gt:real->real^N->real^N^N) tt`;
                 `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))`]
                ODE_SMOOTH_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_SIMP_TAC[]);;

let P2A_LSOL_UNIQUE = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt J1 J2
    (Y1:real^1->real^N) V1 (Y2:real^1->real^N) V2 t0.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\
     ode_solution (p2a_lfield Gt tt)
       (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N))) J1
       (\t. pastecart (Y1 t) (V1 t)) /\
     ode_solution (p2a_lfield Gt tt)
       (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N))) J2
       (\t. pastecart (Y2 t) (V2 t)) /\
     t0 IN J1 /\ t0 IN J2 /\ Y1 t0 = Y2 t0 /\ V1 t0 = V2 t0
     ==> !t. t IN J1 INTER J2 ==> Y1 t = Y2 t /\ V1 t = V2 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
  REWRITE_TAC[GSYM PASTECART_INJ] THEN
  MATCH_MP_TAC ODE_SOLUTION_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`p2a_lfield (Gt:real->real^N->real^N^N) tt`;
    `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))`;
    `t0:real^1`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Ricci flows give smooth s-families in charts (the time t = tt - s^2 stays *)
(* in (a,b), or in (a,b] when the flow is smooth up to b; the extension of   *)
(* p2a_flow_upto covers s = 0), and local existence of chart solutions       *)
(* (pc_ode_vf).                                                              *)
(* ========================================================================= *)

let P2A_SMOOTH_TIME_SQ = prove
 (`!W tt. open W
          ==> smooth_map_on W
                (\z:real^(1,N)finite_sum. pastecart (lift(tt - drop(fstcart z) pow 2))
                                                    (sndcart z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                   `\z:real^(1,N)finite_sum. lift tt`;
                   `\z:real^(1,N)finite_sum. lift(drop(fstcart z) pow 2)`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                   `\z:real^(1,N)finite_sum. lift(drop(fstcart z))`; `2`]
                  SMOOTH_MAP_ON_LIFT_POW) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN
    ASM_REWRITE_TAC[ETA_AX; LINEAR_FSTCART];
    MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[ETA_AX; LINEAR_SNDCART]]);;

let P2A_FLOW_SFAMILY = prove
 (`!top atlas a b (g:real->A->real^N^N) c tt sa sb.
     ricci_flow_on (top,atlas) a b g /\ c IN atlas /\ sa < sb /\
     (!s. sa < s /\ s < sb ==> a < tt - s pow 2 /\ tt - s pow 2 < b)
     ==> p2a_lsmooth (IMAGE (SND c) (FST c)) sa sb
                     (\s. metric_local atlas c (g(tt - s pow 2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_on; p2a_lsmooth] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N)(tt - s pow 2))` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
         (metric_local atlas (c:(A->bool)#(A->real^N))
            ((g:real->A->real^N^N)(tt - drop(fstcart z) pow 2)) (sndcart z))) =
    (\z. vectorize(metric_local atlas c (g(drop(fstcart z))) (sndcart z))) o
    (\z:real^(1,N)finite_sum. pastecart (lift(tt - drop(fstcart z) pow 2)) (sndcart z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; P2A_SMOOTH_TIME_SQ] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GEOL_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
  ASM_SIMP_TAC[]);;

let P2A_UPTO_SFAMILY = prove
 (`!top atlas a b (g:real->A->real^N^N) c tt sa sb.
     p2a_flow_upto (top,atlas) a b g /\ c IN atlas /\ sa < sb /\
     (!s. sa < s /\ s < sb ==> a < tt - s pow 2 /\ tt - s pow 2 <= b)
     ==> p2a_lsmooth (IMAGE (SND c) (FST c)) sa sb
                     (\s. metric_local atlas c (g(tt - s pow 2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_flow_upto] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fx:real^(1,N)finite_sum->real^(N,N)finite_prod`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ASSUME `ricci_flow_on (top,atlas:((A->bool)#(A->real^N))->bool) a b
                               (g:real->A->real^N^N)`) THEN
  REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_lsmooth] THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N)(tt - s pow 2))` MP_TAC THENL
     [ASM_CASES_TAC `tt - s pow 2 = b` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!t. a < t /\ t < b ==> riemannian_metric (atlas:((A->bool)#(A->real^N))->bool)
                                                  ((g:real->A->real^N^N) t)`) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LT_LE];
      ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `(Fx:real^(1,N)finite_sum->real^(N,N)finite_prod) o
    (\z:real^(1,N)finite_sum. pastecart (lift(tt - drop(fstcart z) pow 2)) (sndcart z))` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; o_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`u:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift(b + e)) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; P2A_SMOOTH_TIME_SQ] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GEOL_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a < tt - drop(fstcart(z:real^(1,N)finite_sum)) pow 2 /\
                tt - drop(fstcart z) pow 2 <= b` MP_TAC THENL
   [ASM_SIMP_TAC[]; UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]);;

let P2A_LSOL_EXISTS = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt s0 (y0:real^N) (A0:real^N).
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < s0 /\ s0 < sb /\ y0 IN U
     ==> ?J (Y:real^1->real^N) (V:real^1->real^N).
           open J /\ is_interval J /\ lift s0 IN J /\
           Y(lift s0) = y0 /\ V(lift s0) = A0 /\
           ode_solution (p2a_lfield Gt tt)
             (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N))) J
             (\t. pastecart (Y t) (V t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
  MP_TAC(ISPECL [`p2a_lfield (Gt:real->real^N->real^N^N) tt`;
                 `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))`;
                 `pastecart (lift s0) (pastecart (y0:real^N) (A0:real^N))`]
                ODE_MAXIMAL_SOLUTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`ode_maxint (p2a_lfield (Gt:real->real^N->real^N^N) tt)
      (interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N)))
      (pastecart (lift s0) (pastecart y0 A0))`;
    `\t. fstcart(ode_flow (p2a_lfield (Gt:real->real^N->real^N^N) tt)
             (interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))) t
             (pastecart (lift s0) (pastecart (y0:real^N) (A0:real^N))))`;
    `\t. sndcart(ode_flow (p2a_lfield (Gt:real->real^N->real^N^N) tt)
             (interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))) t
             (pastecart (lift s0) (pastecart (y0:real^N) (A0:real^N))))`] THEN
  ASM_REWRITE_TAC[PASTECART_FST_SND; FSTCART_PASTECART; SNDCART_PASTECART; ETA_AX]);;

