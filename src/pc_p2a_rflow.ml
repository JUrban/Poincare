(* ========================================================================= *)
(* pc_p2a_rflow: the rescaled L-geodesic flow.  On a parameter interval of   *)
(* length h, the L-geodesic system (6.5) in the variable s is rescaled to    *)
(* sigma in [0,1]: Y(sigma) = y(s1 + h sigma), W(sigma) = h A(s1 + h sigma). *)
(* The system becomes autonomous with state ((Y,W),(s,h)):                   *)
(*   Y' = W, W' = p2a_racc(s,h,Y,W), s' = h, h' = 0,                         *)
(* where p2a_racc is smooth also at h = 0 (P2A_RFIELD_SMOOTH).  The points  *)
(* ((y1,0),(s1,0)) are equilibria (P2A_RBASE); the flow has the scaling    *)
(* law P2A_RFLOW_SCALE.  Main results: the shooting lemma P2A_RSHOOT and the *)
(* L-geodesics of the rescaled flow (P2A_RFLOW_LGEOD).                       *)
(*                                                                           *)
(* First: the field, smoothness, the time and step components, base points   *)
(* and scaling.                                                              *)
(* ========================================================================= *)

needs "src/pc_p2a_lgeo1.ml";;

prioritize_real();;
type_invention_error := true;;

let p2a_racc = new_definition
 `p2a_racc (Gt:real->real^N->real^N^N) (tt:real) (s:real) (h:real) (y:real^N) (w:real^N) =
    --(christoffel (Gt(tt - s pow 2)) y w w) +
    (&2 * h pow 2 * s pow 2) % p2a_lgradR (Gt(tt - s pow 2)) y -
    (&4 * h * s) % p2a_lricop (Gt(tt - s pow 2)) y w`;;

let p2a_rfield = new_definition
 `p2a_rfield (Gt:real->real^N->real^N^N) (tt:real)
             (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) =
    pastecart (pastecart (sndcart(fstcart x))
                         (p2a_racc Gt tt (drop(fstcart(sndcart x))) (drop(sndcart(sndcart x)))
                                   (fstcart(fstcart x)) (sndcart(fstcart x))))
              (pastecart (sndcart(sndcart x)) (vec 0:real^1))`;;

let p2a_rdom = new_definition
 `p2a_rdom (U:real^N->bool) (sa:real) (sb:real) =
    (U PCROSS (:real^N)) PCROSS (interval(lift sa,lift sb) PCROSS (:real^1))`;;

let P2A_RDOM_IN = prove
 (`!U sa sb x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum.
     x IN p2a_rdom U sa sb <=>
     fstcart(fstcart x) IN U /\ sa < drop(fstcart(sndcart x)) /\ drop(fstcart(sndcart x)) < sb`,
  REWRITE_TAC[p2a_rdom; GEOL_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
  MESON_TAC[]);;

let P2A_RDOM_PASTE = prove
 (`!U sa sb (y:real^N) w s h.
     pastecart (pastecart y w) (pastecart (lift s) (lift h)) IN p2a_rdom U sa sb <=>
     y IN U /\ sa < s /\ s < sb`,
  REWRITE_TAC[P2A_RDOM_IN; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]);;

let P2A_RDOM_OPEN = prove
 (`!U sa sb. open(U:real^N->bool) ==> open(p2a_rdom U sa sb)`,
  SIMP_TAC[p2a_rdom; OPEN_PCROSS; OPEN_UNIV; OPEN_INTERVAL]);;

let P2A_LRICCI_ADD_CMUL = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> (!a a' b. lricci G y (a + a') b = lricci G y a b + lricci G y a' b) /\
         (!c a b. lricci G y (c % a) b = c * lricci G y a b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP LRG_LRICCI_LINEAR) THEN
  REWRITE_TAC[linear; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN MESON_TAC[]);;

let P2A_LRICOP_LINEAR = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U ==> linear (p2a_lricop G y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LRICCI_ADD_CMUL) THEN
  REWRITE_TAC[linear; p2a_lricop; GSYM MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              GSYM MATRIX_VECTOR_MUL_RMUL] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  ASM_REWRITE_TAC[]);;

let P2A_RACC_SCALE = prove
 (`!U (Gt:real->real^N->real^N^N) tt s h c y w.
     metric_field U (Gt(tt - s pow 2)) /\ y IN U
     ==> p2a_racc Gt tt s (c * h) y (c % w) = (c pow 2) % p2a_racc Gt tt s h y w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_racc] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N)(tt - s pow 2)`; `y:real^N`]
                CHRISTOFFEL_BILINEAR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N)(tt - s pow 2)`; `y:real^N`]
                P2A_LRICOP_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BILINEAR_LMUL; BILINEAR_RMUL; LINEAR_CMUL] THEN
  REWRITE_TAC[REAL_POW_2; REAL_POW_MUL] THEN VECTOR_ARITH_TAC);;

let P2A_RACC_LACC = prove
 (`!U (Gt:real->real^N->real^N^N) tt s h y A.
     metric_field U (Gt(tt - s pow 2)) /\ y IN U
     ==> p2a_racc Gt tt s h y (h % A) = (h pow 2) % p2a_lacc Gt tt s y A`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `Gt:real->real^N->real^N^N`; `tt:real`; `s:real`; `&1`;
                 `h:real`; `y:real^N`; `A:real^N`] P2A_RACC_SCALE) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[p2a_racc; p2a_lacc; REAL_POW_ONE; REAL_MUL_LID; REAL_MUL_RID]);;

let P2A_RACC_POLAR = prove
 (`!U (Gt:real->real^N->real^N^N) tt s h y w.
     metric_field U (Gt(tt - s pow 2)) /\ y IN U
     ==> p2a_racc Gt tt s h y w =
         inv(&2) % (p2a_lacc Gt tt s y w + p2a_lacc Gt tt s y (--w)) -
         (&1 - h pow 2) % p2a_lacc Gt tt s y (vec 0) +
         (h / &2) % (p2a_lacc Gt tt s y w - p2a_lacc Gt tt s y (--w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_racc; p2a_lacc] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N)(tt - s pow 2)`; `y:real^N`]
                CHRISTOFFEL_BILINEAR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N)(tt - s pow 2)`; `y:real^N`]
                P2A_LRICOP_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `christoffel ((Gt:real->real^N->real^N^N)(tt - s pow 2)) y (vec 0) (vec 0) =
                vec 0 /\
                p2a_lricop ((Gt:real->real^N->real^N^N)(tt - s pow 2)) y (vec 0) = vec 0`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[BILINEAR_LZERO; LINEAR_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[BILINEAR_LNEG; BILINEAR_RNEG; LINEAR_NEG] THEN
  REWRITE_TAC[VECTOR_NEG_NEG; VECTOR_NEG_0; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  REWRITE_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  REPEAT STRIP_TAC THEN CONV_TAC REAL_RING);;

let P2A_RFIELD_SMOOTH = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2))
     ==> open(p2a_rdom U sa sb) /\ smooth_map_on (p2a_rdom U sa sb) (p2a_rfield Gt tt)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  MP_TAC(SPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`]
               P2A_LFIELD_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `D = p2a_rdom (U:real^N->bool) sa sb` THEN
  ABBREV_TAC `W0 = interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
  SUBGOAL_THEN `open(D:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool) /\
                open(W0:real^(1,(N,N)finite_sum)finite_sum->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "W0"] THEN
    ASM_SIMP_TAC[P2A_RDOM_OPEN; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `smooth_map_on (W0:real^(1,(N,N)finite_sum)finite_sum->bool)
      (\z. p2a_lacc (Gt:real->real^N->real^N^N) tt (drop(fstcart z)) (fstcart(sndcart z))
                    (sndcart(sndcart z)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`W0:real^(1,(N,N)finite_sum)finite_sum->bool`;
                   `p2a_lfield (Gt:real->real^N->real^N^N) tt`] SMOOTH_MAP_ON_SNDCART_OPEN) THEN
    ASM_REWRITE_TAC[o_DEF; p2a_lfield; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. smooth_map_on (D:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool)
          (\x. p2a_lacc (Gt:real->real^N->real^N^N) tt (drop(fstcart(sndcart x)))
                        (fstcart(fstcart x)) (c % sndcart(fstcart x)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL
     [`D:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool`;
      `W0:real^(1,(N,N)finite_sum)finite_sum->bool`;
      `\x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum.
         pastecart (fstcart(sndcart x)) (pastecart (fstcart(fstcart x)) (c % sndcart(fstcart x)))`;
      `\z:real^(1,(N,N)finite_sum)finite_sum.
         p2a_lacc (Gt:real->real^N->real^N^N) tt (drop(fstcart z)) (fstcart(sndcart z))
                  (sndcart(sndcart z))`] SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    ASM_REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["D"; "W0"] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; P2A_RDOM_IN; PASTECART_IN_PCROSS; IN_UNIV;
                  IN_INTERVAL_1; LIFT_DROP] THEN
      SIMP_TAC[];
      MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[linear] THEN
      REWRITE_TAC[FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL; PASTECART_ADD;
                  GSYM PASTECART_CMUL] THEN
      REPEAT STRIP_TAC THEN REPEAT AP_TERM_TAC THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (D:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool)
      (\x. sndcart(sndcart x)) /\
    smooth_map_on D (\x. sndcart(fstcart x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[linear] THEN
    REWRITE_TAC[FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum.
      pastecart
       (pastecart (sndcart(fstcart x))
         (inv(&2) % (p2a_lacc (Gt:real->real^N->real^N^N) tt (drop(fstcart(sndcart x)))
                       (fstcart(fstcart x)) (&1 % sndcart(fstcart x)) +
                     p2a_lacc Gt tt (drop(fstcart(sndcart x)))
                       (fstcart(fstcart x)) (--(&1) % sndcart(fstcart x))) -
          p2a_lacc Gt tt (drop(fstcart(sndcart x))) (fstcart(fstcart x))
                   (&0 % sndcart(fstcart x)) +
          (drop(sndcart(sndcart x)) pow 2) %
          p2a_lacc Gt tt (drop(fstcart(sndcart x))) (fstcart(fstcart x))
                   (&0 % sndcart(fstcart x)) +
          (inv(&2) * drop(sndcart(sndcart x))) %
          (p2a_lacc Gt tt (drop(fstcart(sndcart x))) (fstcart(fstcart x))
                    (&1 % sndcart(fstcart x)) -
           p2a_lacc Gt tt (drop(fstcart(sndcart x))) (fstcart(fstcart x))
                    (--(&1) % sndcart(fstcart x)))))
       (pastecart (sndcart(sndcart x)) (vec 0:real^1))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum` THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[P2A_RDOM_IN] THEN STRIP_TAC THEN
    REWRITE_TAC[p2a_rfield] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `drop(fstcart(sndcart(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)))`;
                   `drop(sndcart(sndcart(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)))`;
                   `fstcart(fstcart(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum))`;
                   `sndcart(fstcart(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum))`]
                  P2A_RACC_POLAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `drop(fstcart(sndcart(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)))` o
        check (fun th -> can (find_term ((=) `metric_field:(real^N->bool)->(real^N->real^N^N)->bool`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_MUL_LNEG; real_div] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `smooth_map_on (D:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool)
      (\x. lift(drop(sndcart(sndcart x)) pow 2)) /\
    smooth_map_on D (\x. lift(inv(&2) * drop(sndcart(sndcart x))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`D:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool`;
                     `\x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum. sndcart(sndcart x)`;
                     `2`] SMOOTH_MAP_ON_LIFT_POW);
      MP_TAC(ISPECL [`D:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool`; `inv(&2)`;
                     `\x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum. sndcart(sndcart x)`]
                    SMOOTH_MAP_ON_LIFT_CMUL)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC P2A_SMOOTH_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[]]);;

let P2A_HVD_FST_SND = prove
 (`!(f:real^1->real^(M,N)finite_sum) f' net.
     (f has_vector_derivative f') net
     ==> ((\x. fstcart(f x)) has_vector_derivative fstcart f') net /\
         ((\x. sndcart(f x)) has_vector_derivative sndcart f') net`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x. fstcart((f:real^1->real^(M,N)finite_sum) x)`;
                 `\x. sndcart((f:real^1->real^(M,N)finite_sum) x)`;
                 `fstcart(f':real^(M,N)finite_sum)`; `sndcart(f':real^(M,N)finite_sum)`;
                 `net:(real^1)net`] P2A_HVD_PASTECART_EQ) THEN
  REWRITE_TAC[PASTECART_FST_SND; ETA_AX] THEN ASM_REWRITE_TAC[]);;

let P2A_HVD_ZERO_CONST = prove
 (`!(f:real^1->real^N) J a.
     is_interval J /\ a IN J /\ (!t. t IN J ==> (f has_vector_derivative vec 0) (at t))
     ==> !t. t IN J ==> f t = f a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `J:real^1->bool`; `a:real^1`;
                 `(f:real^1->real^N) a`] HAS_DERIVATIVE_ZERO_UNIQUE) THEN
  ASM_REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
  ASM_REWRITE_TAC[has_vector_derivative; VECTOR_MUL_RZERO]);;

let P2A_RFLOW_FACTS = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt x0.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ x0 IN p2a_rdom U sa sb
     ==> open(p2a_rdom U sa sb) /\
         continuously_differentiable 1 (p2a_rdom U sa sb) (p2a_rfield Gt tt) /\
         open(ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x0) /\
         is_interval(ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x0) /\
         vec 0 IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x0 /\
         ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (vec 0) x0 = x0 /\
         !t. t IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x0
             ==> ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) t x0 IN p2a_rdom U sa sb /\
                 ((\s. ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) s x0)
                  has_vector_derivative
                  p2a_rfield Gt tt (ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) t x0))
                 (at t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_RFIELD_SMOOTH) THEN
  SUBGOAL_THEN `continuously_differentiable 1 (p2a_rdom U sa sb)
                  (p2a_rfield (Gt:real->real^N->real^N^N) tt)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1` o REWRITE_RULE[smooth_map_on] o
      check (fun th -> can (find_term ((=) `smooth_map_on:(real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool)->(real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)->bool`)) (concl th))) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ODE_VF_MAXIMAL THEN ASM_REWRITE_TAC[]);;

let P2A_HVD_AFFINE = prove
 (`!a b net. ((\t. lift(a + b * drop t)) has_vector_derivative lift b) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL; LIFT_DROP] THEN
  SUBGOAL_THEN `lift b = vec 0 + b % vec 1` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM LIFT_NUM; GSYM LIFT_CMUL; VECTOR_ADD_LID; REAL_MUL_RID]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID]);;

let P2A_RFLOW_SH = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (y1:real^N) V s1 h.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ y1 IN U /\ sa < s1 /\ s1 < sb
     ==> !t. t IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                   (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))
             ==> sndcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) t
                          (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))) =
                 pastecart (lift(s1 + h * drop t)) (lift h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `x0 = pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (lift h))` THEN
  SUBGOAL_THEN `x0 IN p2a_rdom (U:real^N->bool) sa sb` ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN ASM_REWRITE_TAC[P2A_RDOM_PASTE]; ALL_TAC] THEN
  SUBGOAL_THEN `fstcart(sndcart(x0:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)) = lift s1 /\ sndcart(sndcart x0) = lift h`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `x0:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`] P2A_RFLOW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `J = ode_vf_maxint (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb) x0` THEN
  ABBREV_TAC `Fl = \t. ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb) t x0` THEN
  SUBGOAL_THEN `!t. ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb) t x0 =
                    (Fl:real^1->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) t`
  (fun th -> REWRITE_TAC[th; ETA_AX]) THENL [EXPAND_TAC "Fl" THEN REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN J ==> ((\t. sndcart(sndcart((Fl:real^1->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) t))) has_vector_derivative vec 0) (at t) /\
                   ((\t. fstcart(sndcart(Fl t))) has_vector_derivative sndcart(sndcart(Fl t))) (at t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o C MP (ASSUME `(t:real^1) IN J`) o SPEC `t:real^1` o
      check (fun th -> is_forall (concl th) &&
                       can (find_term ((=) `p2a_rfield (Gt:real->real^N->real^N^N) tt`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP P2A_HVD_FST_SND) THEN
    DISCH_THEN(MP_TAC o MATCH_MP P2A_HVD_FST_SND) THEN
    REWRITE_TAC[p2a_rfield; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN J ==> sndcart(sndcart((Fl:real^1->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) t)) = lift h` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. sndcart(sndcart((Fl:real^1->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) t))`; `J:real^1->bool`; `vec 0:real^1`]
                  P2A_HVD_ZERO_CONST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o C MP (ASSUME `(t:real^1) IN J`) o SPEC `t:real^1` o
        check (fun th -> is_forall (concl th) &&
                         can (find_term ((=) `vec 0:real^1`)) (concl th))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN J ==> fstcart(sndcart((Fl:real^1->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) t)) - lift(s1 + h * drop t) = vec 0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. fstcart(sndcart((Fl:real^1->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) t)) - lift(s1 + h * drop t)`;
                   `J:real^1->bool`; `vec 0:real^1`] P2A_HVD_ZERO_CONST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      SUBGOAL_THEN `vec 0:real^1 = lift h - lift h` SUBST1_TAC THENL
       [REWRITE_TAC[VECTOR_SUB_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [ALL_TAC; REWRITE_TAC[P2A_HVD_AFFINE]] THEN
      SUBGOAL_THEN `lift h = sndcart(sndcart((Fl:real^1->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) t))` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o C MP (ASSUME `(t:real^1) IN J`) o SPEC `t:real^1` o
        check (fun th -> is_forall (concl th) &&
                         can (find_term ((=) `vec 0:real^1`)) (concl th) &&
                         can (find_term (fun u -> is_const u && fst(dest_const u) = "has_vector_derivative")) (concl th))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_ADD_RID; VECTOR_SUB_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let P2A_HVD_LINEAR = prove
 (`!(g:real^1->real^M) g' (l:real^M->real^N) net.
     linear l /\ (g has_vector_derivative g') net
     ==> ((\x. l(g x)) has_vector_derivative l g') net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative; has_derivative] THEN STRIP_TAC THEN
  CONJ_TAC THENL [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`net:(real^1)net`; `l:real^M->real^N`;
                 `\y. inv(norm(y - netlimit net)) %
                      ((g:real^1->real^M) y - (g(netlimit net) + drop(y - netlimit net) % g'))`;
                 `vec 0:real^M`] LIM_LINEAR) THEN
  ASM_SIMP_TAC[MATCH_MP LINEAR_0 (ASSUME `linear (l:real^M->real^N)`); LINEAR_CMUL; LINEAR_SUB;
               LINEAR_ADD]);;

let P2A_RBASE = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (y1:real^N) s1.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ y1 IN U /\ sa < s1 /\ s1 < sb
     ==> p2a_rfield Gt tt (pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) =
         vec 0 /\
         ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb)
           (pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) = (:real^1) /\
         !t. ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) t
               (pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) =
             pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  SUBGOAL_THEN
   `p2a_rfield (Gt:real->real^N->real^N^N) tt
      (pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) = vec 0`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2a_rfield; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; DROP_VEC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `Gt:real->real^N->real^N^N`; `tt:real`; `s1:real`; `&0`;
                   `&0`; `y1:real^N`; `vec 0:real^N`] P2A_RACC_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `metric_field:(real^N->bool)->(real^N->real^N^N)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO; VECTOR_MUL_LZERO] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; VECTOR_MUL_LZERO; PASTECART_VEC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ODE_VF_ZERO THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `pastecart (pastecart (y1:real^N) (vec 0:real^N)) (pastecart (lift s1) (vec 0:real^1))`]
                P2A_RFLOW_FACTS) THEN
  ASM_REWRITE_TAC[GSYM LIFT_NUM; P2A_RDOM_PASTE] THEN SIMP_TAC[]);;

let p2a_rscale = new_definition
 `p2a_rscale (c:real) (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) =
    pastecart (pastecart (fstcart(fstcart x)) (c % sndcart(fstcart x)))
              (pastecart (fstcart(sndcart x)) (c % sndcart(sndcart x)))`;;

let P2A_RSCALE_LINEAR = prove
 (`!c. linear(p2a_rscale c:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->
                           real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)`,
  REWRITE_TAC[linear; p2a_rscale; PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART;
              FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL] THEN
  VECTOR_ARITH_TAC);;

let P2A_RSCALE_RDOM = prove
 (`!U sa sb c x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum.
     p2a_rscale c x IN p2a_rdom U sa sb <=> x IN p2a_rdom U sa sb`,
  REWRITE_TAC[P2A_RDOM_IN; p2a_rscale; FSTCART_PASTECART; SNDCART_PASTECART]);;

let P2A_RFIELD_RSCALE = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt c x.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ x IN p2a_rdom U sa sb
     ==> p2a_rfield Gt tt (p2a_rscale c x) = p2a_rscale c (c % p2a_rfield Gt tt x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[P2A_RDOM_IN]) THEN
  REWRITE_TAC[p2a_rfield; p2a_rscale; FSTCART_PASTECART; SNDCART_PASTECART; FSTCART_CMUL;
              SNDCART_CMUL; DROP_CMUL] THEN
  REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_MUL_RZERO] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM REAL_POW_2] THEN
  MATCH_MP_TAC P2A_RACC_SCALE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop(fstcart(sndcart(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)))` o
    check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `metric_field:(real^N->bool)->(real^N->real^N^N)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let P2A_RFLOW_SCALE = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) c.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ x IN p2a_rdom U sa sb /\
     lift c IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x
     ==> lift(&1) IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) (p2a_rscale c x) /\
         ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift(&1)) (p2a_rscale c x) =
         p2a_rscale c (ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift c) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`] P2A_RFLOW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Jx = ode_vf_maxint (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb) x` THEN
  ABBREV_TAC `D = p2a_rdom (U:real^N->bool) sa sb` THEN
  ABBREV_TAC `X = p2a_rfield (Gt:real->real^N->real^N^N) tt` THEN
  MP_TAC(ISPECL [`X:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`;
                 `D:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool`;
                 `{t:real^1 | c % t IN Jx}`;
                 `\t:real^1. p2a_rscale c (ode_vf_flow X D (c % t) (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum))`;
                 `vec 0:real^1`] ODE_VF_UNIQUE) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; VECTOR_MUL_RZERO] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IS_INTERVAL_CONVEX_1] THEN
      MATCH_MP_TAC CONVEX_LINEAR_PREIMAGE THEN
      ASM_REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1] THEN
      REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONJ_TAC THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[P2A_RSCALE_RDOM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    SUBGOAL_THEN
     `X(p2a_rscale c (ode_vf_flow X D (c % t) (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum))) =
      p2a_rscale c (c % X(ode_vf_flow X D (c % t) x))`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["X"; "D"] THEN MATCH_MP_TAC P2A_RFIELD_RSCALE THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `sa:real`; `sb:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC P2A_HVD_LINEAR THEN REWRITE_TAC[P2A_RSCALE_LINEAR] THEN
    MP_TAC(ISPECL [`\t:real^1. c % t`; `\s. ode_vf_flow X D s (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)`;
                   `c % vec 1:real^1`; `X(ode_vf_flow X D (c % t) (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)):real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`;
                   `t:real^1`] VECTOR_DIFF_CHAIN_AT) THEN
    REWRITE_TAC[o_DEF; DROP_CMUL; DROP_VEC; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift(&1)`) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; GSYM LIFT_CMUL; REAL_MUL_RID] THEN
  MESON_TAC[]);;


(* ========================================================================= *)
(* The derivative of the rescaled flow at the base points                    *)
(* (P2A_RFLOW_DERIV_BASE, from the scaling law), and the uniform estimates   *)
(* on the compact boxes p2a_rbox: existence on [0,1]                         *)
(* (P2A_RFLOW_UNIFORM_EXIST), smallness (P2A_RFLOW_UNIFORM_SMALL), the       *)
(* derivative in the velocity variable near the identity                     *)
(* (P2A_RFLOW_UNIFORM_DERIV) and the resulting Lipschitz bound of the        *)
(* shooting map minus the identity (P2A_RFLOW_LIPSCHITZ).                    *)
(* ========================================================================= *)

let P2A_VF_DOMAIN_PASTE = prove
 (`!(X:real^N->real^N) U t x.
     pastecart t x IN ode_vf_domain X U <=> x IN U /\ t IN ode_vf_maxint X U x`,
  REWRITE_TAC[ode_vf_domain; IN_ELIM_THM; PASTECART_INJ] THEN MESON_TAC[]);;

let P2A_RFLOW_SMOOTH = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2))
     ==> open(ode_vf_domain (p2a_rfield Gt tt) (p2a_rdom U sa sb)) /\
         smooth_map_on (ode_vf_domain (p2a_rfield Gt tt) (p2a_rdom U sa sb))
           (\w. ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (fstcart w) (sndcart w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP ODE_VF_FLOW_SMOOTH o MATCH_MP P2A_RFIELD_SMOOTH));;

let P2A_RFLOW_DERIV_BASE = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (y1:real^N) s1 V.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ y1 IN U /\ sa < s1 /\ s1 < sb
     ==> fstcart(fstcart(frechet_derivative
            (\w. ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (fstcart w) (sndcart w))
            (at (pastecart (lift(&1))
                   (pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0)))))
            (pastecart (vec 0) (pastecart (pastecart (vec 0) V) (vec 0))))) = V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`]
                P2A_RFLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y1:real^N`; `s1:real`] P2A_RBASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pastecart (pastecart (y1:real^N) (vec 0:real^N)) (pastecart (lift s1) (vec 0:real^1)) IN
    p2a_rdom U sa sb /\
    pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (vec 0:real^1)) IN
    p2a_rdom U sa sb`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[P2A_RDOM_PASTE; GSYM LIFT_NUM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (vec 0:real^1))`]
                P2A_RFLOW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `fstcart(fstcart(p2a_rfield (Gt:real->real^N->real^N^N) tt
      (pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (vec 0:real^1))))) = V`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2a_rfield; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. pastecart (lift(&1))
          (pastecart (pastecart (y1:real^N) (vec 0:real^N)) (pastecart (lift s1) (vec 0:real^1))) +
        drop c % pastecart (vec 0:real^1)
                   (pastecart (pastecart (vec 0:real^N) (V:real^N)) (vec 0:real^(1,1)finite_sum)) =
        pastecart (lift(&1))
          (p2a_rscale (drop c)
             (pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (vec 0:real^1))))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[p2a_rscale; FSTCART_PASTECART; SNDCART_PASTECART; GSYM PASTECART_CMUL;
                PASTECART_ADD; VECTOR_MUL_RZERO; VECTOR_ADD_RID; VECTOR_ADD_LID];
    ALL_TAC] THEN
  ABBREV_TAC `X = p2a_rfield (Gt:real->real^N->real^N^N) tt` THEN
  ABBREV_TAC `D = p2a_rdom (U:real^N->bool) sa sb` THEN
  ABBREV_TAC `Phi = \w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum. ode_vf_flow X D (fstcart w) (sndcart w)` THEN
  ABBREV_TAC `x0 = pastecart (pastecart (y1:real^N) (vec 0:real^N)) (pastecart (lift s1) (vec 0:real^1))` THEN
  ABBREV_TAC `x1 = pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (vec 0:real^1))` THEN
  ABBREV_TAC `e = pastecart (vec 0:real^1) (pastecart (pastecart (vec 0:real^N) (V:real^N)) (vec 0:real^(1,1)finite_sum))` THEN
  SUBGOAL_THEN `pastecart (lift(&1)) (x0:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) IN ode_vf_domain X D` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[P2A_VF_DOMAIN_PASTE; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) has_derivative frechet_derivative Phi (at (pastecart (lift(&1)) x0)))
    (at (pastecart (lift(&1)) x0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ode_vf_domain (X:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) D`; `Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Phi' = frechet_derivative (Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (at (pastecart (lift(&1)) x0))` THEN
  SUBGOAL_THEN `linear(Phi':real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\c:real^1. pastecart (lift(&1)) (x0:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) + drop c % (e:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)) has_derivative
     (\h. drop h % e)) (at (vec 0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\c:real^1. pastecart (lift(&1)) (x0:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)`; `\h:real^1. vec 0:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum`;
                   `\c:real^1. drop c % (e:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)`; `\h:real^1. drop h % (e:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)`;
                   `at (vec 0:real^1)`] HAS_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\c:real^1. (Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (pastecart (lift(&1)) x0 + drop c % e)) has_vector_derivative
     (Phi':real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (e:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)) (at (vec 0))`
  ASSUME_TAC THENL
   [REWRITE_TAC[has_vector_derivative] THEN
    MP_TAC(ISPECL [`\c:real^1. pastecart (lift(&1)) (x0:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) + drop c % (e:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)`; `Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`;
                   `\h:real^1. drop h % (e:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)`; `Phi':real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`; `vec 0:real^1`] DIFF_CHAIN_AT) THEN
    REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID; o_DEF] THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\c:real^1. fstcart(fstcart((Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (pastecart (lift(&1)) x0 + drop c % e))))
     has_vector_derivative fstcart(fstcart((Phi':real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (e:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)))) (at (vec 0))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2A_HVD_FST_SND o
      check (fun th -> can (find_term ((=) `Phi':real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP P2A_HVD_FST_SND) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\c:real^1. fstcart(fstcart(ode_vf_flow X D c (x1:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)))) has_vector_derivative V)
    (at (vec 0))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o C MP (ASSUME `vec 0 IN ode_vf_maxint X D (x1:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)`) o
      SPEC `vec 0:real^1` o
      check (fun th -> is_forall (concl th) &&
                       can (find_term ((=) `x1:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP P2A_HVD_FST_SND) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP P2A_HVD_FST_SND) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ ball(vec 0:real^1,d) SUBSET ode_vf_maxint X D (x1:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\c:real^1. fstcart(fstcart((Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (pastecart (lift(&1)) x0 + drop c % e)))`;
                 `vec 0:real^1`; `fstcart(fstcart((Phi':real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (e:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)))`; `V:real^N`]
                VECTOR_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\c:real^1. fstcart(fstcart(ode_vf_flow X D c (x1:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)))`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:real^1` THEN DISCH_TAC THEN
  EXPAND_TAC "Phi" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `x1:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`; `drop c`] P2A_RFLOW_SCALE) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (is_binary "SUBSET" o concl)) THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[p2a_rscale; FSTCART_PASTECART]);;

let P2A_LINEAR_BASIS_BOUND = prove
 (`!(f:real^M->real^N) x.
     linear f ==> norm(f x) <= sum(1..dimindex(:M)) (\j. norm(f(basis j))) * norm x`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[NORM_MUL] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[COMPONENT_LE_NORM; NORM_POS_LE]);;

let p2a_rbox = new_definition
 `p2a_rbox (Kc:real^N->bool) (a:real) (b:real) (e:real) =
    (Kc PCROSS cball(vec 0:real^N,e)) PCROSS
    (interval[lift a,lift b] PCROSS interval[lift(--e),lift e])`;;

let P2A_RBOX_IN = prove
 (`!Kc a b e x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum.
     x IN p2a_rbox Kc a b e <=>
     fstcart(fstcart x) IN Kc /\ norm(sndcart(fstcart x)) <= e /\
     a <= drop(fstcart(sndcart x)) /\ drop(fstcart(sndcart x)) <= b /\
     abs(drop(sndcart(sndcart x))) <= e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p2a_rbox; GEOL_IN_PCROSS; IN_CBALL_0; IN_INTERVAL_1; LIFT_DROP; DROP_NEG;
              REAL_ABS_BOUNDS] THEN
  CONV_TAC TAUT);;

let P2A_RBOX_PASTE = prove
 (`!Kc a b e (y:real^N) V s h.
     pastecart (pastecart y V) (pastecart (lift s) (lift h)) IN p2a_rbox Kc a b e <=>
     y IN Kc /\ norm V <= e /\ a <= s /\ s <= b /\ abs h <= e`,
  REWRITE_TAC[P2A_RBOX_IN; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]);;

let P2A_RBOX_COMPACT = prove
 (`!Kc a b e. compact(Kc:real^N->bool) ==> compact(p2a_rbox Kc a b e)`,
  SIMP_TAC[p2a_rbox; COMPACT_PCROSS; COMPACT_CBALL; COMPACT_INTERVAL]);;

let P2A_RBOX_SUBSET = prove
 (`!U sa sb Kc a b e.
     Kc SUBSET (U:real^N->bool) /\ sa < a /\ b < sb
     ==> p2a_rbox Kc a b e SUBSET p2a_rdom U sa sb`,
  REWRITE_TAC[SUBSET; P2A_RBOX_IN; P2A_RDOM_IN] THEN
  MESON_TAC[REAL_LTE_TRANS; REAL_LET_TRANS]);;

let P2A_RSCALE_RSCALE = prove
 (`!c d x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum.
     p2a_rscale c (p2a_rscale d x) = p2a_rscale (c * d) x /\ p2a_rscale (&1) x = x`,
  REWRITE_TAC[p2a_rscale; FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_MUL_ASSOC;
              VECTOR_MUL_LID; PASTECART_FST_SND]);;

let P2A_RFLOW_UNIFORM_EXIST = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt Kc a b.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ compact Kc /\ Kc SUBSET U /\
     sa < a /\ b < sb
     ==> ?e. &0 < e /\
             !x. x IN p2a_rbox Kc a b e
                 ==> lift(&1) IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_RFIELD_SMOOTH) THEN
  MP_TAC(ISPECL [`p2a_rfield (Gt:real->real^N->real^N^N) tt`; `p2a_rdom (U:real^N->bool) sa sb`;
                 `p2a_rbox (Kc:real^N->bool) a b (&1)`] ODE_VF_DOMAIN_UNIFORM_TIME) THEN
  ASM_SIMP_TAC[P2A_RBOX_COMPACT; P2A_RBOX_SUBSET] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[smooth_map_on]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum` THEN DISCH_TAC THEN
  SUBGOAL_THEN `x = p2a_rscale e (p2a_rscale (inv e) (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[P2A_RSCALE_RSCALE; REAL_MUL_RINV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_rscale (inv e) (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) IN
                p2a_rbox Kc a b (&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) IN p2a_rbox Kc a b e` THEN
    REWRITE_TAC[P2A_RBOX_IN; p2a_rscale; FSTCART_PASTECART; SNDCART_PASTECART; NORM_MUL;
                DROP_CMUL; REAL_ABS_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `p2a_rscale (inv e) (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)`; `e:real`]
                P2A_RFLOW_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Kc:real^N->bool`; `a:real`;
                     `b:real`; `&1`] P2A_RBOX_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

let P2A_RFLOW_MAXINT_UNIT = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt x sig.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ x IN p2a_rdom U sa sb /\
     lift(&1) IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x /\
     &0 <= sig /\ sig <= &1
     ==> lift sig IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`] P2A_RFLOW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IS_INTERVAL_1] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "is_interval" with Failure _ -> false)) THEN
  MAP_EVERY EXISTS_TAC [`vec 0:real^1`; `lift(&1)`] THEN ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP]);;

let P2A_RFLOW_UNIFORM_SMALL = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt Kc a b e r.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ compact Kc /\ Kc SUBSET U /\
     sa < a /\ b < sb /\ &0 < e /\
     (!x. x IN p2a_rbox Kc a b e
          ==> lift(&1) IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x) /\ &0 < r
     ==> ?d. &0 < d /\ d <= e /\
             !y1 V s1 h sig.
               y1 IN Kc /\ norm V <= d /\ a <= s1 /\ s1 <= b /\ abs h <= d /\
               &0 <= sig /\ sig <= &1
               ==> norm(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift sig)
                          (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h))) -
                        pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) < r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`]
                P2A_RFLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Kc:real^N->bool`; `a:real`; `b:real`;
                 `e:real`] P2A_RBOX_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `C = interval[vec 0:real^1,lift(&1)] PCROSS p2a_rbox (Kc:real^N->bool) a b e` THEN
  SUBGOAL_THEN `C SUBSET ode_vf_domain (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                                        (p2a_rdom U sa sb)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum` THEN
    MP_TAC(ISPECL [`w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum`]
                  PASTECART_FST_SND) THEN
    ABBREV_TAC `t = fstcart(w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)` THEN
    ABBREV_TAC `x = sndcart(w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; P2A_VF_DOMAIN_PASTE] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) IN p2a_rdom U sa sb`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`; `drop t`]
                  P2A_RFLOW_MAXINT_UNIT) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(t:real^1) IN interval[vec 0,lift(&1)]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)
           (fstcart w) (sndcart w)) uniformly_continuous_on C`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ode_vf_domain (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      EXPAND_TAC "C" THEN ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; P2A_RBOX_COMPACT]];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e (dd / &3)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y1:real^N`; `V:real^N`; `s1:real`; `h:real`; `sig:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y1:real^N`; `s1:real`] P2A_RBASE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; REAL_LTE_TRANS; REAL_LET_TRANS];
                  STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`pastecart (lift sig) (pastecart (pastecart (y1:real^N) (vec 0:real^N))
                                     (pastecart (lift s1) (vec 0:real^1)))`;
    `pastecart (lift sig) (pastecart (pastecart (y1:real^N) (V:real^N))
                                     (pastecart (lift s1) (lift h)))`]) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DIST_PASTECART_CANCEL] THEN
  REWRITE_TAC[dist] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXPAND_TAC "C" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
  ASM_REWRITE_TAC[P2A_RBOX_PASTE; GSYM LIFT_NUM; NORM_0; REAL_ABS_0] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL; VECTOR_SUB_RZERO; GSYM LIFT_SUB; REAL_SUB_REFL;
              REAL_SUB_RZERO; LIFT_NUM] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm(pastecart (vec 0:real^N) (V:real^N)) + norm(pastecart (vec 0:real^1) (lift h))` THEN
  REWRITE_TAC[NORM_PASTECART_LE] THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `V:real^N`] NORM_PASTECART_LE) THEN
  MP_TAC(ISPECL [`vec 0:real^1`; `lift h`] NORM_PASTECART_LE) THEN
  REWRITE_TAC[NORM_0; NORM_LIFT] THEN ASM_REAL_ARITH_TAC);;

let P2A_REMBED_LINEAR = prove
 (`linear (\u:real^N. pastecart (vec 0:real^1)
                        (pastecart (pastecart (vec 0:real^N) u) (vec 0:real^(1,1)finite_sum)))`,
  REWRITE_TAC[linear; PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART; FSTCART_ADD;
              SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL; VECTOR_ADD_LID; VECTOR_MUL_RZERO]);;

let P2A_FF_LINEAR = prove
 (`linear (\z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum. fstcart(fstcart z))`,
  REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL]);;

let P2A_RFLOW_UNIFORM_DERIV = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt Kc a b e.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ compact Kc /\ Kc SUBSET U /\
     sa < a /\ b < sb /\ &0 < e /\
     (!x. x IN p2a_rbox Kc a b e
          ==> lift(&1) IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x)
     ==> ?d. &0 < d /\ d <= e /\
             !y1 V s1 h u.
               y1 IN Kc /\ norm V <= d /\ a <= s1 /\ s1 <= b /\ abs h <= d
               ==> norm(fstcart(fstcart(frechet_derivative
                      (\w. ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (fstcart w)
                                       (sndcart w))
                      (at (pastecart (lift(&1))
                             (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))))
                      (pastecart (vec 0) (pastecart (pastecart (vec 0) u) (vec 0))))) - u)
                   <= norm u / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`]
                P2A_RFLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Kc:real^N->bool`; `a:real`; `b:real`;
                 `e:real`] P2A_RBOX_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `Phi = \w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum.
                ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)
                            (fstcart w) (sndcart w)` THEN
  ABBREV_TAC `dom = ode_vf_domain (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)` THEN
  ABBREV_TAC `R = p2a_rbox (Kc:real^N->bool) a b e` THEN
  ABBREV_TAC `emb = \u:real^N. pastecart (vec 0:real^1)
                      (pastecart (pastecart (vec 0:real^N) u) (vec 0:real^(1,1)finite_sum))` THEN
  ABBREV_TAC `DF = \(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (u:real^N).
                 fstcart(fstcart(frechet_derivative
                   (Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->
                        real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)
                   (at (pastecart (lift(&1)) x)) (emb u)))` THEN
  SUBGOAL_THEN `!x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum.
                  x IN R ==> pastecart (lift(&1)) x IN dom` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["R"; "dom"] THEN REWRITE_TAC[P2A_VF_DOMAIN_PASTE] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum.
                  x IN R ==> linear (\u. (DF:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real^N->real^N) x u - u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum` THEN DISCH_TAC THEN
    MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN REWRITE_TAC[LINEAR_ID] THEN
    EXPAND_TAC "DF" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `linear(frechet_derivative (Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->
                                     real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)
               (at (pastecart (lift(&1)) x)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `dom:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `linear (emb:real^N->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)`
    ASSUME_TAC THENL [EXPAND_TAC "emb" THEN REWRITE_TAC[P2A_REMBED_LINEAR]; ALL_TAC] THEN
    REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; FSTCART_ADD; FSTCART_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. (\x. (DF:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real^N->real^N) x v) continuous_on R` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "DF" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[LINEAR_FSTCART] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[LINEAR_FSTCART] THEN
    SUBGOAL_THEN
     `(\x. frechet_derivative (Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (at (pastecart (lift(&1)) x))
             ((emb:real^N->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum) v)) =
      (\w. frechet_derivative Phi (at w) (emb v)) o (\x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum. pastecart (lift(&1)) x)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `dom:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `phi = \x. sum(1..dimindex(:N))
                          (\j. norm((DF:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real^N->real^N) x (basis j) - basis j))` THEN
  SUBGOAL_THEN `(\x. lift((phi:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real) x)) uniformly_continuous_on R` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN CONJ_TAC THENL
     [ALL_TAC; EXPAND_TAC "R" THEN ASM_SIMP_TAC[P2A_RBOX_COMPACT]] THEN
    EXPAND_TAC "phi" THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `inv(&2)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e (dd / &3)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y1:real^N`; `V:real^N`; `s1:real`; `h:real`; `u:real^N`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `xx = pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (lift h))` THEN
  ABBREV_TAC `x0 = pastecart (pastecart (y1:real^N) (vec 0:real^N)) (pastecart (lift s1) (vec 0:real^1))` THEN
  SUBGOAL_THEN `(xx:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) IN R /\ (x0:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) IN R` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["xx"; "x0"; "R"] THEN
    REWRITE_TAC[P2A_RBOX_PASTE; GSYM LIFT_NUM; NORM_0; REAL_ABS_0] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real) x0 = &0` ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN
    MAP_EVERY EXPAND_TAC ["DF"; "emb"; "Phi"; "x0"] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_RFLOW_DERIV_BASE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real) xx < inv(&2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x0:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`; `xx:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`]) THEN
    ASM_REWRITE_TAC[DIST_LIFT; REAL_SUB_RZERO] THEN ANTS_TAC THENL
     [MAP_EVERY EXPAND_TAC ["xx"; "x0"] THEN
      REWRITE_TAC[dist; PASTECART_SUB; VECTOR_SUB_REFL; VECTOR_SUB_RZERO; GSYM LIFT_SUB;
                  REAL_SUB_REFL; REAL_SUB_RZERO; LIFT_NUM] THEN
      MP_TAC(ISPECL [`pastecart (vec 0:real^N) (V:real^N)`; `pastecart (vec 0:real^1) (lift h)`]
                    NORM_PASTECART_LE) THEN
      MP_TAC(ISPECL [`vec 0:real^N`; `V:real^N`] NORM_PASTECART_LE) THEN
      MP_TAC(ISPECL [`vec 0:real^1`; `lift h`] NORM_PASTECART_LE) THEN
      REWRITE_TAC[NORM_0; NORM_LIFT] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fstcart(fstcart(frechet_derivative (Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)
      (at (pastecart (lift(&1)) (xx:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)))
      (pastecart (vec 0) (pastecart (pastecart (vec 0) (u:real^N)) (vec 0))))) =
    (DF:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real^N->real^N) xx u`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["DF"; "emb"] THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\u. (DF:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real^N->real^N) xx u - u`; `u:real^N`] P2A_LINEAR_BASIS_BOUND) THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  SUBGOAL_THEN `sum (1..dimindex(:N)) (\j. norm((DF:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real^N->real^N) xx (basis j) - basis j)) =
                (phi:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real) xx` SUBST1_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC);;

let P2A_RAFFINE_DERIV = prove
 (`!(y1:real^N) s1 h (V:real^N).
     ((\V:real^N. pastecart (lift(&1)) (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h))))
      has_derivative
      (\u:real^N. pastecart (vec 0:real^1)
                    (pastecart (pastecart (vec 0:real^N) u) (vec 0:real^(1,1)finite_sum)))) (at V)`,
  REPEAT GEN_TAC THEN
  REPEAT(MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC) THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID]);;

let P2A_RFLOW_LIPSCHITZ = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt Kc a b e d.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ Kc SUBSET U /\
     sa < a /\ b < sb /\ &0 < d /\ d <= e /\
     (!x. x IN p2a_rbox Kc a b e
          ==> lift(&1) IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x) /\
     (!y1 V s1 h u.
        y1 IN Kc /\ norm V <= d /\ a <= s1 /\ s1 <= b /\ abs h <= d
        ==> norm(fstcart(fstcart(frechet_derivative
               (\w. ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (fstcart w) (sndcart w))
               (at (pastecart (lift(&1))
                      (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))))
               (pastecart (vec 0) (pastecart (pastecart (vec 0) u) (vec 0))))) - u)
            <= norm u / &2)
     ==> !y1 s1 h V V'.
           y1 IN Kc /\ a <= s1 /\ s1 <= b /\ abs h <= d /\ norm V <= d /\ norm V' <= d
           ==> norm((fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift(&1))
                       (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h))))) - V) -
                    (fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift(&1))
                       (pastecart (pastecart y1 V') (pastecart (lift s1) (lift h))))) - V'))
               <= norm(V - V') / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`y1:real^N`; `s1:real`; `h:real`] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[GSYM IMP_CONJ] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`]
                P2A_RFLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Phi = \w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum.
                ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)
                            (fstcart w) (sndcart w)` THEN
  ABBREV_TAC `dom = ode_vf_domain (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)` THEN
  ABBREV_TAC `gam = \V:real^N. pastecart (lift(&1))
                       (pastecart (pastecart (y1:real^N) V) (pastecart (lift s1) (lift h)))` THEN
  SUBGOAL_THEN `!V:real^N. norm V <= d ==> (gam:real^N->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum) V IN dom`
  ASSUME_TAC THENL
   [X_GEN_TAC `V:real^N` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["gam"; "dom"] THEN
    REWRITE_TAC[P2A_VF_DOMAIN_PASTE] THEN
    SUBGOAL_THEN `pastecart (pastecart (y1:real^N) V) (pastecart (lift s1) (lift h)) IN
                  p2a_rbox Kc a b e` ASSUME_TAC THENL
     [REWRITE_TAC[P2A_RBOX_PASTE] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Kc:real^N->bool`; `a:real`; `b:real`;
                   `e:real`] P2A_RBOX_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\V:real^N. fstcart(fstcart((Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->
                                     real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)
                                 ((gam:real^N->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum) V))) - V`;
    `\V:real^N u:real^N.
       fstcart(fstcart(frechet_derivative (Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->
                                     real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)
                         (at ((gam:real^N->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum) V))
                         (pastecart (vec 0) (pastecart (pastecart (vec 0) u) (vec 0))))) - u`;
    `cball(vec 0:real^N,d)`; `inv(&2)`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_CBALL; IN_CBALL_0] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
      MP_TAC(ISPECL [`gam:real^N->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum`; `Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`;
                     `\u:real^N. pastecart (vec 0:real^1)
                        (pastecart (pastecart (vec 0:real^N) u) (vec 0:real^(1,1)finite_sum))`;
                     `frechet_derivative (Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (at ((gam:real^N->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum) x))`; `x:real^N`]
                    DIFF_CHAIN_AT) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [EXPAND_TAC "gam" THEN REWRITE_TAC[P2A_RAFFINE_DERIV];
          MP_TAC(ISPECL [`dom:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->bool`; `Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> MP_TAC(MATCH_MP DIFF_CHAIN_AT (CONJ th
        (ISPEC `at (((Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) o (gam:real^N->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)) x)`
               (MATCH_MP HAS_DERIVATIVE_LINEAR P2A_FF_LINEAR))))) THEN
      REWRITE_TAC[o_DEF];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `linear (\u:real^N. fstcart(fstcart(frechet_derivative (Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (at ((gam:real^N->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum) x))
                (pastecart (vec 0:real^1) (pastecart (pastecart (vec 0:real^N) u)
                                                     (vec 0:real^(1,1)finite_sum))))) - u)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN REWRITE_TAC[LINEAR_ID] THEN
      SUBGOAL_THEN
       `(\u:real^N. fstcart(fstcart(frechet_derivative (Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (at ((gam:real^N->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum) x))
                (pastecart (vec 0:real^1) (pastecart (pastecart (vec 0:real^N) u)
                                                     (vec 0:real^(1,1)finite_sum)))))) =
        (\z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum. fstcart(fstcart z)) o
        (frechet_derivative (Phi:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) (at ((gam:real^N->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum) x)) o
         (\u:real^N. pastecart (vec 0:real^1) (pastecart (pastecart (vec 0:real^N) u)
                                                     (vec 0:real^(1,1)finite_sum))))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[P2A_FF_LINEAR] THEN
      MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[P2A_REMBED_LINEAR] THEN
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `dom:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->bool` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o MATCH_MP ONORM) THEN
    X_GEN_TAC `u:real^N` THEN REWRITE_TAC[] THEN EXPAND_TAC "gam" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y1:real^N`; `x:real^N`; `s1:real`; `h:real`; `u:real^N`] o
      check (fun th -> is_forall (concl th) &&
                       can (find_term ((=) `frechet_derivative:(real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)->(real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)net->real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `V:real^N` THEN DISCH_TAC THEN X_GEN_TAC `V':real^N` THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`V:real^N`; `V':real^N`]) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["Phi"; "gam"] THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The contraction argument.  P2A_RSHOOT: for compact Kc in U and [a,b]      *)
(* inside the open s-range, there are a velocity radius dV, a step bound dh, *)
(* an end-point radius rho and a choice Vs of initial velocities such that   *)
(* the rescaled flow from ((y1,Vs),(s1,h)) stays within r of the base point  *)
(* on [0,1], hits y2 at time 1, Vs is the unique such velocity in the ball,  *)
(* and Vs depends sequentially continuously on the data (y1,y2,s1,h).        *)
(* ========================================================================= *)

let P2A_CONTRACTION_FIX = prove
 (`!(Fm:real^N->real^N) y2 R.
     &0 <= R /\
     (!V V'. norm V <= R /\ norm V' <= R
             ==> norm((Fm V - V) - (Fm V' - V')) <= norm(V - V') / &2) /\
     norm(y2 - Fm(vec 0)) <= R / &2
     ==> ?!V. norm V <= R /\ Fm V = y2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\V:real^N. V + y2 - (Fm:real^N->real^N) V`; `cball(vec 0:real^N,R)`; `inv(&2)`]
                BANACH_FIX) THEN
  REWRITE_TAC[IN_CBALL_0; VECTOR_ARITH `x + y2 - f:real^N = x <=> f = y2`] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[COMPACT_IMP_COMPLETE; COMPACT_CBALL];
    REWRITE_TAC[CBALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV;
    CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0] THEN X_GEN_TAC `V:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`V:real^N`; `vec 0:real^N`]) THEN
    ASM_REWRITE_TAC[NORM_0; VECTOR_SUB_RZERO] THEN
    UNDISCH_TAC `norm(y2 - (Fm:real^N->real^N)(vec 0)) <= R / &2` THEN
    UNDISCH_TAC `norm(V:real^N) <= R` THEN CONV_TAC NORM_ARITH;
    REWRITE_TAC[dist] THEN MAP_EVERY X_GEN_TAC [`V:real^N`; `V':real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`V:real^N`; `V':real^N`]) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NORM_ARITH]);;

let P2A_CONTRACTION_STABLE = prove
 (`!(Fm:real^N->real^N) Gm y2 z2 R V W.
     (!V V'. norm V <= R /\ norm V' <= R
             ==> norm((Gm V - V) - (Gm V' - V')) <= norm(V - V') / &2) /\
     norm V <= R /\ norm W <= R /\ Fm V = y2 /\ Gm W = z2
     ==> norm(W - V) <= &2 * norm((z2 - y2) - (Gm V - Fm V))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`W:real^N`; `V:real^N`]) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  CONV_TAC NORM_ARITH);;

let P2A_RFLOW_SEQ = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt
    (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) xn.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ x IN p2a_rdom U sa sb /\
     lift(&1) IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x /\
     (xn --> x) sequentially
     ==> ((\n. ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift(&1)) (xn n)) -->
          ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift(&1)) x) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`]
                P2A_RFLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum.
       ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)
                   (fstcart w) (sndcart w)`;
    `sequentially`;
    `\n. pastecart (lift(&1)) ((xn:num->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) n)`;
    `pastecart (lift(&1)) (x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)`]
   LIM_CONTINUOUS_FUNCTION) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `ode_vf_domain (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)` THEN
    ASM_REWRITE_TAC[P2A_VF_DOMAIN_PASTE];
    MATCH_MP_TAC LIM_PASTECART THEN ASM_REWRITE_TAC[LIM_CONST; ETA_AX]]);;

let P2A_ARITH_TAC : tactic =
  fun (asl,w) ->
    let ok t = (is_binary "real_le" t || is_binary "real_lt" t ||
                (is_eq t && type_of(lhand t) = `:real`)) &&
               not (can (find_term is_abs) t) in
    (MAP_EVERY (fun (_,th) -> if ok (concl th) then MP_TAC th else ALL_TAC) asl THEN
     REAL_ARITH_TAC) (asl,w);;

let P2A_RSHOOT = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt Kc a b r.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ compact Kc /\ Kc SUBSET U /\
     sa < a /\ b < sb /\ &0 < r
     ==> ?dV dh rho Vs.
           &0 < dV /\ &0 < dh /\ &0 < rho /\
           (!y1 V s1 h sig.
              y1 IN Kc /\ norm V <= dV /\ a <= s1 /\ s1 <= b /\ abs h <= dh /\
              &0 <= sig /\ sig <= &1
              ==> lift sig IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                                (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h))) /\
                  norm(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift sig)
                         (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h))) -
                       pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) < r) /\
           (!y1 y2 s1 h.
              y1 IN Kc /\ norm(y2 - y1) <= rho /\ a <= s1 /\ s1 <= b /\ abs h <= dh
              ==> norm(Vs y1 y2 s1 h) <= dV /\
                  fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift(&1))
                     (pastecart (pastecart y1 (Vs y1 y2 s1 h)) (pastecart (lift s1) (lift h))))) =
                  y2 /\
                  !V. norm V <= dV /\
                      fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift(&1))
                         (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h))))) = y2
                      ==> V = Vs y1 y2 s1 h) /\
           (!y1 y2 s1 h y1n y2n s1n hn.
              y1 IN Kc /\ norm(y2 - y1) <= rho /\ a <= s1 /\ s1 <= b /\ abs h <= dh /\
              (!n:num. y1n n IN Kc /\ norm(y2n n - y1n n) <= rho /\ a <= s1n n /\
                       s1n n <= b /\ abs(hn n) <= dh) /\
              (y1n --> y1) sequentially /\ (y2n --> y2) sequentially /\
              ((\n. lift(s1n n)) --> lift s1) sequentially /\
              ((\n. lift(hn n)) --> lift h) sequentially
              ==> ((\n. Vs (y1n n) (y2n n) (s1n n) (hn n)) --> Vs y1 y2 s1 h) sequentially)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `Kc:real^N->bool`; `a:real`; `b:real`] P2A_RFLOW_UNIFORM_EXIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `Kc:real^N->bool`; `a:real`; `b:real`; `e:real`; `r:real`]
                P2A_RFLOW_UNIFORM_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `Kc:real^N->bool`; `a:real`; `b:real`; `e:real`] P2A_RFLOW_UNIFORM_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `R = min d1 d2` THEN
  SUBGOAL_THEN `&0 < R /\ R <= d1 /\ R <= d2 /\ R <= e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN P2A_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `Kc:real^N->bool`; `a:real`; `b:real`; `e:real`; `R:real`]
                P2A_RFLOW_LIPSCHITZ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `d2:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN P2A_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `Kc:real^N->bool`; `a:real`; `b:real`; `e:real`; `R / &4`]
                P2A_RFLOW_UNIFORM_SMALL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [P2A_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `Y1 = \(y1:real^N) V s1 h.
           fstcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                             (p2a_rdom U sa sb) (lift(&1))
                             (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))))` THEN
  SUBGOAL_THEN
   `!y1 y2 s1 h.
      y1 IN Kc /\ norm(y2 - y1) <= R / &4 /\ a <= s1 /\ s1 <= b /\ abs h <= min R d4
      ==> ?!V. norm V <= R /\ (Y1:real^N->real^N->real->real->real^N) y1 V s1 h = y2`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\V:real^N. (Y1:real^N->real^N->real->real->real^N) y1 V s1 h`; `y2:real^N`;
                   `R:real`] P2A_CONTRACTION_FIX) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [P2A_ARITH_TAC;
      REPEAT STRIP_TAC THEN EXPAND_TAC "Y1" THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `V':real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN P2A_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`y1:real^N`; `vec 0:real^N`; `s1:real`; `h:real`; `&1`] o
        check (fun th -> is_forall (concl th) &&
                         can (find_term ((=) `d4:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[NORM_0; REAL_POS; REAL_LE_REFL] THEN
      ANTS_TAC THENL [P2A_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "Y1" THEN REWRITE_TAC[] THEN
      ABBREV_TAC `z = ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)
                        (lift(&1)) (pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (lift h)))` THEN
      DISCH_TAC THEN
      MP_TAC(ISPEC `fstcart((z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) - pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0)))`
                   NORM_FSTCART) THEN
      MP_TAC(ISPEC `(z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) - pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))`
                   NORM_FSTCART) THEN
      REWRITE_TAC[FSTCART_SUB; FSTCART_PASTECART] THEN
      UNDISCH_TAC `norm(y2 - y1:real^N) <= R / &4` THEN
      UNDISCH_TAC `norm((z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) - pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) <
                   R / &4` THEN
      CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y1 y2 s1 h.
      y1 IN Kc /\ norm(y2 - y1) <= R / &4 /\ a <= s1 /\ s1 <= b /\ abs h <= min R d4
      ==> norm(@V. norm V <= R /\ (Y1:real^N->real^N->real->real->real^N) y1 V s1 h = y2) <= R /\
          (Y1:real^N->real^N->real->real->real^N) y1 (@V. norm V <= R /\ (Y1:real^N->real^N->real->real->real^N) y1 V s1 h = y2) s1 h = y2 /\
          !V. norm V <= R /\ (Y1:real^N->real^N->real->real->real^N) y1 V s1 h = y2 ==> V = (@V. norm V <= R /\ (Y1:real^N->real^N->real->real->real^N) y1 V s1 h = y2)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y1:real^N`; `y2:real^N`; `s1:real`; `h:real`] o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "?!")) (concl th))) THEN
    ASM_REWRITE_TAC[EXISTS_UNIQUE] THEN
    DISCH_THEN(X_CHOOSE_THEN `V0:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(@V. norm V <= R /\ (Y1:real^N->real^N->real->real->real^N) y1 V s1 h = (y2:real^N)) = V0` SUBST1_TAC THENL
     [MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y1 V s1 h. y1 IN Kc /\ a <= s1 /\ s1 <= b /\ norm V <= R /\ abs h <= min R d4
                ==> pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)) IN p2a_rdom U sa sb /\
                    lift(&1) IN ode_vf_maxint (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                                  (p2a_rdom U sa sb)
                                  (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))`
  (LABEL_TAC "rdomfacts") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[P2A_RDOM_PASTE] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; P2A_ARITH_TAC];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `p2a_rbox:(real^N->bool)->real->real->real->real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool`)) (concl th))) THEN
      REWRITE_TAC[P2A_RBOX_PASTE] THEN ASM_REWRITE_TAC[] THEN P2A_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`R:real`; `min R d4`; `R / &4`;
    `\y1 y2 s1 h. @V. norm V <= R /\ (Y1:real^N->real^N->real->real->real^N) y1 V s1 h = (y2:real^N)`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    P2A_ARITH_TAC;
    P2A_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`y1:real^N`; `V:real^N`; `s1:real`; `h:real`; `sig:real`] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2A_RFLOW_MAXINT_UNIT THEN
      USE_THEN "rdomfacts" (MP_TAC o SPECL [`y1:real^N`; `V:real^N`; `s1:real`; `h:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `r:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN P2A_ARITH_TAC];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y1:real^N`; `y2:real^N`; `s1:real`; `h:real`] o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "@")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Y1" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y1:real^N`; `y2:real^N`; `s1:real`; `h:real`; `y1n:num->real^N`;
                       `y2n:num->real^N`; `s1n:num->real`; `hn:num->real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`y1:real^N`; `y2:real^N`; `s1:real`; `h:real`] o
    check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "@")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `V0 = @V. norm V <= R /\ (Y1:real^N->real^N->real->real->real^N) y1 V s1 h = (y2:real^N)` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. &2 * norm(((y2n:num->real^N) n - y2) -
                            ((Y1:real^N->real^N->real->real->real^N) (y1n n) V0 (s1n n) (hn n) - (Y1:real^N->real^N->real->real->real^N) y1 V0 s1 h))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `y1n:num->real^N`)) (concl th))) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(y1n:num->real^N) n`; `(y2n:num->real^N) n`;
                                  `(s1n:num->real) n`; `(hn:num->real) n`] o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "@")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`\V:real^N. (Y1:real^N->real^N->real->real->real^N) y1 V s1 h`; `\V:real^N. (Y1:real^N->real^N->real->real->real^N) ((y1n:num->real^N) n) V
                                    ((s1n:num->real) n) ((hn:num->real) n)`;
                   `y2:real^N`; `(y2n:num->real^N) n`; `R:real`; `V0:real^N`;
                   `@V. norm V <= R /\ (Y1:real^N->real^N->real->real->real^N) ((y1n:num->real^N) n) V (s1n n) (hn n) = y2n n`]
                  P2A_CONTRACTION_STABLE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN EXPAND_TAC "Y1" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `V':real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN P2A_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN REWRITE_TAC[GSYM LIM_NULL_NORM] THEN
  MATCH_MP_TAC LIM_NULL_SUB THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM LIM_NULL] THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LIM_NULL] THEN EXPAND_TAC "Y1" THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`sequentially`; `\z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum. fstcart(fstcart z)`;
    `\n. ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb) (lift(&1))
           (pastecart (pastecart ((y1n:num->real^N) n) V0) (pastecart (lift(s1n n)) (lift(hn n))))`;
    `ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb) (lift(&1))
       (pastecart (pastecart (y1:real^N) V0) (pastecart (lift s1) (lift h)))`] LIM_LINEAR) THEN
  REWRITE_TAC[P2A_FF_LINEAR] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC P2A_RFLOW_SEQ THEN
  USE_THEN "rdomfacts" (MP_TAC o SPECL [`y1:real^N`; `V0:real^N`; `s1:real`; `h:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REPEAT(MATCH_MP_TAC LIM_PASTECART THEN CONJ_TAC) THEN ASM_REWRITE_TAC[LIM_CONST; ETA_AX]);;


(* ========================================================================= *)
(* For h nonzero, the rescaled flow gives L-geodesics (P2A_RFLOW_LGEOD):     *)
(* y(s) = Y((s - s1)/h) and A(s) = W((s - s1)/h)/h solve y' = A, A' =        *)
(* p2a_lacc(s,y,A), with derivatives at s (the maximal interval is open).    *)
(* ========================================================================= *)

let P2A_RFLOW_LGEOD = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (y1:real^N) V s1 h s.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ y1 IN U /\ sa < s1 /\ s1 < sb /\
     ~(h = &0) /\
     lift((s - s1) / h) IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                             (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))
     ==> (\v. fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                 (lift((drop v - s1) / h))
                 (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))))) (lift s) IN U /\
         ((\v. fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                 (lift((drop v - s1) / h))
                 (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))))) has_vector_derivative
          (\v. inv h % sndcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                 (lift((drop v - s1) / h))
                 (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))))) (lift s))
         (at (lift s)) /\
         ((\v. inv h % sndcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                 (lift((drop v - s1) / h))
                 (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))))) has_vector_derivative
          p2a_lacc Gt tt s
            ((\v. fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                 (lift((drop v - s1) / h))
                 (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))))) (lift s))
            ((\v. inv h % sndcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                 (lift((drop v - s1) / h))
                 (pastecart (pastecart y1 V) (pastecart (lift s1) (lift h)))))) (lift s)))
         (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  ABBREV_TAC `x0 = pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (lift h))` THEN
  SUBGOAL_THEN `x0 IN p2a_rdom (U:real^N->bool) sa sb` ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN ASM_REWRITE_TAC[P2A_RDOM_PASTE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `x0:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`] P2A_RFLOW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y1:real^N`; `V:real^N`; `s1:real`; `h:real`] P2A_RFLOW_SH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `sig = lift((s - s1) / h)` THEN
  ABBREV_TAC `z = ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb) sig x0` THEN
  SUBGOAL_THEN `z IN p2a_rdom (U:real^N->bool) sa sb /\
                sndcart(z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) =
                pastecart (lift s) (lift h)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN ASM_SIMP_TAC[] THEN EXPAND_TAC "sig" THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_INJ; LIFT_EQ] THEN
    UNDISCH_TAC `~(h = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `fstcart(fstcart(z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)) IN U /\ sa < s /\ s < sb` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) IN p2a_rdom U sa sb` THEN REWRITE_TAC[P2A_RDOM_IN] THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((\v. ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)
            (lift((drop v - s1) / h)) x0) has_vector_derivative
     inv h % p2a_rfield Gt tt z) (at (lift s))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\v:real^1. lift((drop v - s1) / h)`;
                   `\t. ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)
                          t (x0:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)`;
                   `lift(inv h)`; `p2a_rfield (Gt:real->real^N->real^N^N) tt z`; `lift s`]
                  VECTOR_DIFF_CHAIN_AT) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `(\v:real^1. lift((drop v - s1) / h)) = (\v. lift(--(s1 / h) + inv h * drop v))`
        SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; real_div; LIFT_EQ] THEN REAL_ARITH_TAC;
          REWRITE_TAC[P2A_HVD_AFFINE]];
        FIRST_ASSUM(MP_TAC o CONJUNCT2 o C MP (ASSUME
          `(sig:real^1) IN ode_vf_maxint (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                                          (p2a_rdom U sa sb) x0`) o
          SPEC `sig:real^1` o check (fun th -> is_forall (concl th) &&
            can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
                (concl th))) THEN
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2A_HVD_FST_SND) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2A_HVD_FST_SND) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FSTCART_CMUL; SNDCART_CMUL]) THEN
  SUBGOAL_THEN `fstcart(fstcart(p2a_rfield (Gt:real->real^N->real^N^N) tt z)) = sndcart(fstcart z) /\
                sndcart(fstcart(p2a_rfield Gt tt z)) =
                p2a_racc Gt tt s h (fstcart(fstcart z)) (sndcart(fstcart z))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p2a_rfield; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `fstcart:real^(N,N)finite_sum->real^N`)) (concl th) &&
      is_comb (concl th) && not (is_eq (concl th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - s pow 2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`;
                   `\s. (Gt:real->real^N->real^N^N)(tt - s pow 2)`] P2A_LSMOOTH_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `metric_field:(real^N->bool)->(real^N->real^N^N)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_lacc (Gt:real->real^N->real^N^N) tt s (fstcart(fstcart(z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum))) (inv h % sndcart(fstcart z)) =
    inv h % inv h % p2a_racc Gt tt s h (fstcart(fstcart z)) (sndcart(fstcart z))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `Gt:real->real^N->real^N^N`; `tt:real`; `s:real`; `h:real`;
                   `fstcart(fstcart(z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum))`; `inv h % sndcart(fstcart(z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum))`] P2A_RACC_LACC) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(inv h * inv h) * h pow 2 = &1` SUBST1_TAC THENL
     [UNDISCH_TAC `~(h = &0)` THEN CONV_TAC REAL_FIELD; REWRITE_TAC[VECTOR_MUL_LID]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `sndcart(fstcart(p2a_rfield (Gt:real->real^N->real^N^N) tt (z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)))`))
        (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th))) THEN
  ASM_REWRITE_TAC[]);;


