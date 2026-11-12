(* ========================================================================= *)
(* Unit pc_cmc_cyl: the unified Colding-Minicozzi Lemma B.1 (GT 2008, App.   *)
(* B, B.1 and B.8), CMC_CYL_STATEMENT of pc_cmc_defs, proved on the cylinder *)
(* Phi(t,theta) = y + rho e^t (cos theta, sin theta):                        *)
(*   - the cylinder map and the conformal identities for V = U o Phi;        *)
(*   - polar integrals on annuli in cylinder coordinates;                    *)
(*   - derivatives of circle integrals, integration by parts in theta,       *)
(*     f'' >= f - int |V_tt + V_qq|^2 for f(t) = int |V_q|^2 (Wirtinger);    *)
(*   - a general one-dimensional comparison lemma, CMCY_ODE_BOUND, with the  *)
(*     maximum principle CMCY_MAXPR (cosh barrier);                          *)
(*   - the bound on V_tt + V_qq and the Hopf constancy of                    *)
(*     int (|V_t|_H^2 - |V_q|_H^2), H = G(q);                                *)
(*   - ellipticity on each circle;                                           *)
(*   - the whole estimate in cylinder terms, CMCY_CYL_CORE;                  *)
(*   - the constants and the headline theorem CMC_CYL.                       *)
(* ========================================================================= *)

needs "src/pc_cmc_defs.ml";;
needs "src/pc_wan_sob2c.ml";;
needs "src/pc_wan_sob2p.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The cylinder map Phi(z) = y + rho cexp z (real^2 = complex: z$1 = t, z$2  *)
(* = theta) and the radial and angular derivative operators of the plane, rd *)
(* F x = DF(x)(x - y) and ad F x = DF(x)(ii (x - y)).  For V = F o Phi: d_t  *)
(* V = (rd F) o Phi and d_theta V = (ad F) o Phi.                            *)
(* ------------------------------------------------------------------------- *)

let cmcy_phi = new_definition
 `cmcy_phi (y:real^2) (rho:real) (z:real^2) = y + Cx rho * cexp z`;;

let cmcy_rd = new_definition
 `cmcy_rd (y:real^2) (f:real^2->real^N) (x:real^2) =
    frechet_derivative f (at x) (x - y)`;;

let cmcy_ad = new_definition
 `cmcy_ad (y:real^2) (f:real^2->real^N) (x:real^2) =
    frechet_derivative f (at x) (ii * (x - y))`;;

let CMCY_PHI_EQ = prove
 (`!y rho. cmcy_phi y rho = \z. y + Cx rho * cexp z`,
  REWRITE_TAC[FUN_EQ_THM; cmcy_phi]);;

let CMCY_PHI_CIRC = prove
 (`!y rho z. cmcy_phi y rho z = wan_circ y (rho * exp(z$1)) (z$2)`,
  REWRITE_TAC[cmcy_phi; wan_circ; CART_EQ; DIMINDEX_2; FORALL_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_MUL_CX; IM_MUL_CX; RE_CEXP; IM_CEXP] THEN
  REAL_ARITH_TAC);;

let CMCY_PHI_SUB = prove
 (`!y rho z. cmcy_phi y rho z - y = Cx rho * cexp z`,
  REWRITE_TAC[cmcy_phi] THEN VECTOR_ARITH_TAC);;

let CMCY_PHI_NORM = prove
 (`!y rho z. &0 <= rho ==> norm(cmcy_phi y rho z - y) = rho * exp(z$1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CMCY_PHI_SUB; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_CEXP; RE_DEF] THEN
  ASM_REWRITE_TAC[real_abs]);;

let CMCY_PHI_HAS_DERIVATIVE = prove
 (`!y rho z. (cmcy_phi y rho has_derivative (\h. Cx rho * cexp z * h)) (at z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMCY_PHI_EQ] THEN
  MP_TAC(SPEC `z:complex` HAS_COMPLEX_DERIVATIVE_CEXP) THEN
  DISCH_THEN(MP_TAC o SPEC `Cx rho` o MATCH_MP HAS_COMPLEX_DERIVATIVE_LMUL_AT) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(\w. y):complex->complex`; `Cx(&0)`;
                 `\w. Cx rho * cexp w`; `Cx rho * cexp z`; `at (z:complex)`]
                HAS_COMPLEX_DERIVATIVE_ADD) THEN
  ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CONST; COMPLEX_ADD_LID] THEN
  REWRITE_TAC[has_complex_derivative; COMPLEX_MUL_ASSOC]);;

let CMCY_PHI_DIFFERENTIABLE = prove
 (`!y rho z. cmcy_phi y rho differentiable (at z)`,
  REWRITE_TAC[differentiable] THEN MESON_TAC[CMCY_PHI_HAS_DERIVATIVE]);;

let CMCY_PHI_SMOOTH = prove
 (`!y rho. smooth_map_on (:real^2) (cmcy_phi y rho)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMCY_PHI_EQ; GSYM COMPLEX_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
  MP_TAC(SPEC `\w:complex. w` BEL_SMOOTH_CEXP) THEN REWRITE_TAC[SMOOTH_MAP_ON_ID; ETA_AX]);;

let CMCY_PARTIAL_PHI = prove
 (`!y rho z. partial_derivative 1 (cmcy_phi y rho) z = cmcy_phi y rho z - y /\
             partial_derivative 2 (cmcy_phi y rho) z = ii * (cmcy_phi y rho z - y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`y:real^2`; `rho:real`; `z:real^2`] CMCY_PHI_HAS_DERIVATIVE) THEN
  DISCH_THEN(fun th ->
    REWRITE_TAC[MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE th]) THEN
  REWRITE_TAC[COMPLEX_BASIS; COMPLEX_MUL_RID; CMCY_PHI_SUB] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let CMCY_CHAIN = prove
 (`!y rho (f:real^2->real^N) z.
     f differentiable (at (cmcy_phi y rho z))
     ==> partial_derivative 1 (f o cmcy_phi y rho) z = cmcy_rd y f (cmcy_phi y rho z) /\
         partial_derivative 2 (f o cmcy_phi y rho) z = cmcy_ad y f (cmcy_phi y rho z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_CHAIN; CMCY_PHI_DIFFERENTIABLE] THEN
  REWRITE_TAC[CMCY_PARTIAL_PHI; cmcy_rd; cmcy_ad]);;

(* ------------------------------------------------------------------------- *)
(* Coordinates: DF(x)h = h$1 F_1 + h$2 F_2, so rd F = w1 F_1 + w2 F_2 and ad *)
(* F = -w2 F_1 + w1 F_2 with w = x - y; smoothness of rd F and ad F; the     *)
(* conformal identities rd rd F + ad ad F = |w|^2 Lap F, |rd F|^2 + |ad F|^2 *)
(* = |w|^2 |DF|^2, ad F = |w| cmc_angd and the trace of a bilinear form;     *)
(* their cylinder forms for V = u o Phi.                                     *)
(* ------------------------------------------------------------------------- *)

let CMCY_BASIS2 = prove
 (`(basis 1:real^2)$1 = &1 /\ (basis 1:real^2)$2 = &0 /\
   (basis 2:real^2)$1 = &0 /\ (basis 2:real^2)$2 = &1`,
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH]);;

let CMCY_FD_COORDS = prove
 (`!(f:real^2->real^N) x h.
     f differentiable (at x)
     ==> frechet_derivative f (at x) h =
         h$1 % partial_derivative 1 f x + h$2 % partial_derivative 2 f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; DIMINDEX_2; VSUM_2; o_THM; LINEAR_CMUL]);;

let CMCY_RD_COORDS = prove
 (`!y (f:real^2->real^N) x.
     f differentiable (at x)
     ==> cmcy_rd y f x = (x - y)$1 % partial_derivative 1 f x +
                         (x - y)$2 % partial_derivative 2 f x /\
         cmcy_ad y f x = --((x - y)$2) % partial_derivative 1 f x +
                         (x - y)$1 % partial_derivative 2 f x`,
  SIMP_TAC[cmcy_rd; cmcy_ad; CMCY_FD_COORDS] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_MUL_II; IM_MUL_II]);;

let CMCY_COORD_SMOOTH = prove
 (`!s (y:real^2) k. open s ==> smooth_map_on s (\x:real^2. lift((x - y)$k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let CMCY_COORD_PD = prove
 (`!(y:real^2) k x i.
     (\x:real^2. lift((x - y)$k)) differentiable (at x) /\
     partial_derivative i (\x:real^2. lift((x - y)$k)) x = lift((basis i:real^2)$k)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `((\x:real^2. lift((x - y)$k)) has_derivative (\h. lift(h$k))) (at x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^2. lift(x$k)`; `\h:real^2. lift(h$k)`;
                   `\x:real^2. lift((y:real^2)$k)`; `\h:real^2. vec 0:real^1`;
                   `at (x:real^2)`] HAS_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO; GSYM LIFT_SUB;
                GSYM VECTOR_SUB_COMPONENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE th])]);;

let CMCY_DIFF_MUL_DROP = prove
 (`!(a:real^M->real^1) (g:real^M->real^N) x.
     a differentiable (at x) /\ g differentiable (at x)
     ==> (\x. drop(a x) % g x) differentiable (at x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^M. drop((a:real^M->real^1) x)`; `g:real^M->real^N`; `x:real^M`]
                DIFFERENTIABLE_MUL_AT) THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]);;

let CMCY_RD_SMOOTH = prove
 (`!s y (f:real^2->real^N).
     open s /\ smooth_map_on s f
     ==> smooth_map_on s (cmcy_rd y f) /\ smooth_map_on s (cmcy_ad y f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN s ==> (f:real^2->real^N) differentiable (at z)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. smooth_map_on s (partial_derivative i (f:real^2->real^N))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. smooth_map_on s (\x:real^2. lift((x - y)$k)) /\
                    smooth_map_on s (\x:real^2. --(lift((x - y)$k)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[CMCY_COORD_SMOOTH] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_SIMP_TAC[CMCY_COORD_SMOOTH];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THENL
   [EXISTS_TAC `\x. drop(lift((x - y)$1)) % partial_derivative 1 (f:real^2->real^N) x +
                    drop(lift((x - y)$2)) % partial_derivative 2 f x`;
    EXISTS_TAC `\x. drop(--(lift((x - y)$2))) % partial_derivative 1 (f:real^2->real^N) x +
                    drop(lift((x - y)$1)) % partial_derivative 2 f x`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CMCY_RD_COORDS; LIFT_DROP; DROP_NEG];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ASM_SIMP_TAC[CMCY_RD_COORDS; LIFT_DROP; DROP_NEG];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX]]);;

let CMCY_PD_RD = prove
 (`!s y (f:real^2->real^N) x i.
     open s /\ smooth_map_on s f /\ x IN s
     ==> partial_derivative i (cmcy_rd y f) x =
         (basis i:real^2)$1 % partial_derivative 1 f x +
         (basis i:real^2)$2 % partial_derivative 2 f x +
         (x - y)$1 % partial_derivative i (partial_derivative 1 f) x +
         (x - y)$2 % partial_derivative i (partial_derivative 2 f) x /\
         partial_derivative i (cmcy_ad y f) x =
         --((basis i:real^2)$2) % partial_derivative 1 f x +
         (basis i:real^2)$1 % partial_derivative 2 f x +
         --((x - y)$2) % partial_derivative i (partial_derivative 1 f) x +
         (x - y)$1 % partial_derivative i (partial_derivative 2 f) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. (partial_derivative j (f:real^2->real^N)) differentiable (at x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN s ==> (f:real^2->real^N) differentiable (at z)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS
     `partial_derivative i
        (\x. drop(lift((x - y)$1)) % partial_derivative 1 (f:real^2->real^N) x +
             drop(lift((x - y)$2)) % partial_derivative 2 f x) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_SIMP_TAC[CMCY_RD_COORDS; LIFT_DROP];
      ALL_TAC];
    TRANS_TAC EQ_TRANS
     `partial_derivative i
        (\x. drop(--(lift((x - y)$2))) % partial_derivative 1 (f:real^2->real^N) x +
             drop(lift((x - y)$1)) % partial_derivative 2 f x) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_SIMP_TAC[CMCY_RD_COORDS; LIFT_DROP; DROP_NEG];
      ALL_TAC]] THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_ADD; CMCY_DIFF_MUL_DROP; CMCY_COORD_PD;
               DIFFERENTIABLE_NEG; ETA_AX] THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_MUL; CMCY_COORD_PD; DIFFERENTIABLE_NEG;
               PARTIAL_DERIVATIVE_NEG; ETA_AX] THEN
  REWRITE_TAC[LIFT_DROP; DROP_NEG] THEN VECTOR_ARITH_TAC);;

let CMCY_LAPLACE = prove
 (`!s y (f:real^2->real^N) x.
     open s /\ smooth_map_on s f /\ x IN s
     ==> cmcy_rd y (cmcy_rd y f) x + cmcy_ad y (cmcy_ad y f) x =
         (norm(x - y) pow 2) % hmr_vlap f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on s (cmcy_rd y (f:real^2->real^N)) /\
                smooth_map_on s (cmcy_ad y f)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CMCY_RD_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `cmcy_rd y (f:real^2->real^N) differentiable (at x) /\
                cmcy_ad y f differentiable (at x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CMCY_RD_COORDS] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `y:real^2`; `f:real^2->real^N`; `x:real^2`]
                CMCY_PD_RD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[hmr_vlap; VSUM_2; NORM_POW_2; DOT_2; CMCY_BASIS2] THEN
  VECTOR_ARITH_TAC);;

let CMCY_RD_AD_NORMS = prove
 (`!y (f:real^2->real^N) x.
     f differentiable (at x)
     ==> norm(cmcy_rd y f x) pow 2 + norm(cmcy_ad y f x) pow 2 =
         norm(x - y) pow 2 * (norm(partial_derivative 1 f x) pow 2 +
                              norm(partial_derivative 2 f x) pow 2)`,
  SIMP_TAC[CMCY_RD_COORDS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; DOT_2] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

let CMCY_AD_ANGD = prove
 (`!y (f:real^2->real^N) x.
     f differentiable (at x) /\ ~(x = y)
     ==> cmcy_ad y f x =
         norm(x - y) % cmc_angd y x (partial_derivative 1 f x) (partial_derivative 2 f x)`,
  SIMP_TAC[CMCY_RD_COORDS; cmc_angd; VECTOR_MUL_ASSOC] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(x - y:real^2) * inv(norm(x - y)) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ];
    REWRITE_TAC[VECTOR_MUL_LID]]);;

let CMCY_BIL_TRACE = prove
 (`!y (f:real^2->real^N) x (bb:real^N->real^N->real^P).
     f differentiable (at x) /\ bilinear bb
     ==> bb (cmcy_rd y f x) (cmcy_rd y f x) + bb (cmcy_ad y f x) (cmcy_ad y f x) =
         (norm(x - y) pow 2) %
         (bb (partial_derivative 1 f x) (partial_derivative 1 f x) +
          bb (partial_derivative 2 f x) (partial_derivative 2 f x))`,
  SIMP_TAC[CMCY_RD_COORDS] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP BILINEAR_LADD th; MATCH_MP BILINEAR_RADD th;
                                    MATCH_MP BILINEAR_LMUL th; MATCH_MP BILINEAR_RMUL th]) THEN
  REWRITE_TAC[NORM_POW_2; DOT_2] THEN VECTOR_ARITH_TAC);;

(* The cylinder forms, for V = u o Phi on the open set of z with Phi z in s. *)

let CMCY_CYL_OPEN = prove
 (`!s y rho. open s ==> open {z:real^2 | cmcy_phi y rho z IN s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  ASM_REWRITE_TAC[ETA_AX] THEN GEN_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  REWRITE_TAC[CMCY_PHI_DIFFERENTIABLE]);;

let CMCY_CYL_SMOOTH = prove
 (`!s y rho (u:real^2->real^N).
     open s /\ smooth_map_on s u
     ==> smooth_map_on {z | cmcy_phi y rho z IN s} (u o cmcy_phi y rho)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[CMCY_CYL_OPEN] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[CMCY_PHI_SMOOTH; SUBSET_UNIV]);;

let CMCY_CYL_D1 = prove
 (`!s y rho (u:real^2->real^N) z.
     open s /\ smooth_map_on s u /\ cmcy_phi y rho z IN s
     ==> partial_derivative 1 (u o cmcy_phi y rho) z = cmcy_rd y u (cmcy_phi y rho z) /\
         partial_derivative 2 (u o cmcy_phi y rho) z = cmcy_ad y u (cmcy_phi y rho z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMCY_CHAIN THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
  ASM_REWRITE_TAC[]);;

let CMCY_CYL_D2 = prove
 (`!s y rho (u:real^2->real^N) z.
     open s /\ smooth_map_on s u /\ cmcy_phi y rho z IN s
     ==> partial_derivative 1 (partial_derivative 1 (u o cmcy_phi y rho)) z =
           cmcy_rd y (cmcy_rd y u) (cmcy_phi y rho z) /\
         partial_derivative 2 (partial_derivative 1 (u o cmcy_phi y rho)) z =
           cmcy_ad y (cmcy_rd y u) (cmcy_phi y rho z) /\
         partial_derivative 1 (partial_derivative 2 (u o cmcy_phi y rho)) z =
           cmcy_rd y (cmcy_ad y u) (cmcy_phi y rho z) /\
         partial_derivative 2 (partial_derivative 2 (u o cmcy_phi y rho)) z =
           cmcy_ad y (cmcy_ad y u) (cmcy_phi y rho z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on s (cmcy_rd y (u:real^2->real^N)) /\
                smooth_map_on s (cmcy_ad y u)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CMCY_RD_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. cmcy_phi y rho w IN s
        ==> partial_derivative 1 (u o cmcy_phi y rho) w =
            (cmcy_rd y (u:real^2->real^N) o cmcy_phi y rho) w /\
            partial_derivative 2 (u o cmcy_phi y rho) w = (cmcy_ad y u o cmcy_phi y rho) w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC CMCY_CYL_D1 THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (partial_derivative 1 (u o cmcy_phi y rho)) z =
        partial_derivative i (cmcy_rd y (u:real^2->real^N) o cmcy_phi y rho) z /\
        partial_derivative i (partial_derivative 2 (u o cmcy_phi y rho)) z =
        partial_derivative i (cmcy_ad y u o cmcy_phi y rho) z`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `{z:real^2 | cmcy_phi y rho z IN s}` THEN
    ASM_SIMP_TAC[CMCY_CYL_OPEN; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `y:real^2`; `rho:real`; `cmcy_rd y (u:real^2->real^N)`;
                 `z:real^2`] CMCY_CYL_D1) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `y:real^2`; `rho:real`; `cmcy_ad y (u:real^2->real^N)`;
                 `z:real^2`] CMCY_CYL_D1) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let CMCY_CYL_LAPLACE = prove
 (`!s y rho (u:real^2->real^N) z.
     open s /\ smooth_map_on s u /\ cmcy_phi y rho z IN s
     ==> partial_derivative 1 (partial_derivative 1 (u o cmcy_phi y rho)) z +
         partial_derivative 2 (partial_derivative 2 (u o cmcy_phi y rho)) z =
         (norm(cmcy_phi y rho z - y) pow 2) % hmr_vlap u (cmcy_phi y rho z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `y:real^2`; `rho:real`; `u:real^2->real^N`; `z:real^2`]
                CMCY_CYL_D2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC CMCY_LAPLACE THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integrals over annuli in cylinder coordinates: for h absolutely           *)
(* integrable on cmc_ann y (rho e^t1) (rho e^t2),                            *)
(*   int_ann h = int_{t1}^{t2} (rho e^t)^2 int_0^{2pi} h(Phi(t,theta)),      *)
(* from WAN_POLAR_ANNULUS and the substitution r = rho e^t.                 *)
(* ------------------------------------------------------------------------- *)

(* A copy of PDM_INTEGRABLE_CONTINUOUS_COMPACT (pc_pde_mloc), which this    *)
(* unit does not load.                                                       *)

let CMCY_CONT_COMPACT_ABSINT = prove
 (`!(f:real^M->real^N) k.
        f continuous_on k /\ compact k
        ==> f absolutely_integrable_on k /\ f integrable_on k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  SUBGOAL_THEN `bounded (IMAGE (f:real^M->real^N) k)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real^M. lift B` THEN
  ASM_SIMP_TAC[LIFT_DROP; INTEGRABLE_ON_CONST; MEASURABLE_COMPACT] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]);;

let CMCY_CANN_COMPACT = prove
 (`!(y:real^2) r1 r2. compact {x:real^2 | r1 <= norm(x - y) /\ norm(x - y) <= r2}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x:real^2 | r1 <= norm(x - y) /\ norm(x - y) <= r2} =
                cball(y,r2) DIFF ball(y,r1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_BALL; IN_CBALL; dist] THEN
    GEN_TAC THEN REWRITE_TAC[NORM_SUB] THEN REAL_ARITH_TAC;
    SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]]);;

let CMCY_ANN_ABSINT = prove
 (`!(h:real^2->real^N) y r1 r2.
     h continuous_on {x | r1 <= norm(x - y) /\ norm(x - y) <= r2}
     ==> h absolutely_integrable_on cmc_ann y r1 r2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `{x:real^2 | r1 <= norm(x - y) /\ norm(x - y) <= r2}` THEN
  ASM_SIMP_TAC[CMCY_CONT_COMPACT_ABSINT; CMCY_CANN_COMPACT] THEN
  REWRITE_TAC[cmc_ann] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`y:real^2`; `r1:real`; `r2:real`] WAN_ANNULUS_EQ) THEN SIMP_TAC[]]);;

let CMCY_EXP_VDERIV = prove
 (`!rho x s. ((\x. lift(rho * exp(drop x))) has_vector_derivative lift(rho * exp(drop x)))
             (at x within s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
  MP_TAC(SPEC `drop x` HAS_REAL_DERIVATIVE_EXP) THEN
  DISCH_THEN(MP_TAC o SPEC `rho:real` o MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP]);;

let CMCY_EXP_IMAGE = prove
 (`!rho t1 t2. &0 < rho /\ t1 <= t2
     ==> IMAGE (\x. lift(rho * exp(drop x))) (interval[lift t1,lift t2]) =
         interval[lift(rho * exp t1),lift(rho * exp t2)]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTERVAL_1; LIFT_DROP] THEN
  X_GEN_TAC `r:real^1` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^1` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE];
    STRIP_TAC THEN EXISTS_TAC `lift(log(drop r / rho))` THEN
    SUBGOAL_THEN `&0 < drop r / rho` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `rho * exp t1` THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LIFT_DROP; EXP_LOG] THEN
    SUBGOAL_THEN `rho * drop r / rho = drop r` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[EXP_LOG] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let CMCY_POLAR = prove
 (`!y rho t1 t2 (h:real^2->real^N).
     &0 < rho /\ t1 <= t2 /\ h absolutely_integrable_on cmc_ann y (rho * exp t1) (rho * exp t2)
     ==> (\t. (rho * exp(drop t)) pow 2 %
              integral (interval[vec 0,lift(&2 * pi)])
                (\q. h(cmcy_phi y rho (vector[drop t; drop q]))))
         absolutely_integrable_on interval[lift t1,lift t2] /\
         integral (interval[lift t1,lift t2])
           (\t. (rho * exp(drop t)) pow 2 %
                integral (interval[vec 0,lift(&2 * pi)])
                  (\q. h(cmcy_phi y rho (vector[drop t; drop q])))) =
         integral (cmc_ann y (rho * exp t1) (rho * exp t2)) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= rho * exp t1 /\ rho * exp t1 <= rho * exp t2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_EXP_POS_LE; REAL_LE_LMUL;
                 REAL_EXP_MONO_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^2->real^N`; `y:real^2`; `&0`; `rho * exp t1`; `rho * exp t2`]
                WAN_POLAR_ANNULUS) THEN
  ASM_REWRITE_TAC[GSYM cmc_ann; REAL_ADD_LID] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`\r. drop r % integral (interval[vec 0,lift(&2 * pi)])
                         (\t. (h:real^2->real^N)(wan_circ y (drop r) (drop t)))`;
                 `\x. lift(rho * exp(drop x))`; `\t. rho * exp t`;
                 `interval[lift t1,lift t2]`;
                 `integral (cmc_ann y (rho * exp t1) (rho * exp t2)) (h:real^2->real^N)`]
                HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_1) THEN
  ASM_SIMP_TAC[CMCY_EXP_IMAGE; LEBESGUE_MEASURABLE_INTERVAL; CMCY_EXP_VDERIV] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LIFT_EQ; REAL_EQ_MUL_LCANCEL; REAL_EXP_INJ; GSYM DROP_EQ] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. abs(rho * exp(drop x)) % drop(lift(rho * exp(drop x))) %
         integral (interval[vec 0,lift(&2 * pi)])
           (\t. (h:real^2->real^N)(wan_circ y (drop(lift(rho * exp(drop x)))) (drop t)))) =
    (\t. (rho * exp(drop t)) pow 2 %
         integral (interval[vec 0,lift(&2 * pi)])
           (\q. h(cmcy_phi y rho (vector[drop t; drop q]))))`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; LIFT_DROP; CMCY_PHI_CIRC; VECTOR_2; VECTOR_MUL_ASSOC] THEN
  X_GEN_TAC `t:real^1` THEN
  SUBGOAL_THEN `abs(rho * exp(drop t)) = rho * exp(drop t)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_EXP_POS_LE];
    REWRITE_TAC[REAL_POW_2]]);;

let CMCY_VEC2_EQ = prove
 (`!a b. (vector[a; b]:real^2) = vector[a; &0] + b % basis 2`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; CMCY_BASIS2] THEN REAL_ARITH_TAC);;

let CMCY_PHI_SECTION_NORM = prove
 (`!y rho t q. &0 <= rho
               ==> norm(cmcy_phi y rho (vector[t; q]) - y) = rho * exp t`,
  SIMP_TAC[CMCY_PHI_NORM; VECTOR_2]);;

let CMCY_SECTION_CONT = prove
 (`!y rho t1 t2 (h:real^2->real^N) t.
     &0 < rho /\
     h continuous_on {x | rho * exp t1 <= norm(x - y) /\ norm(x - y) <= rho * exp t2} /\
     t1 <= t /\ t <= t2
     ==> (\q. h(cmcy_phi y rho (vector[t; drop q]))) continuous_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\q. (h:real^2->real^N)(cmcy_phi y rho (vector[t; drop q]))) =
                h o cmcy_phi y rho o (\q. vector[t; &0] + drop q % basis 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM CMCY_VEC2_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[CMCY_PHI_DIFFERENTIABLE]];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{x | rho * exp t1 <= norm(x - y) /\ norm(x - y) <= rho * exp t2}` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; o_THM; IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM CMCY_VEC2_EQ] THEN
    ASM_SIMP_TAC[CMCY_PHI_SECTION_NORM; REAL_LT_IMP_LE] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE]]);;

let CMCY_CYL_TRANSFER = prove
 (`!y rho t1 t2 (h:real^2->real^N) (g:real^2->real^N).
     &0 < rho /\ t1 <= t2 /\
     h continuous_on {x | rho * exp t1 <= norm(x - y) /\ norm(x - y) <= rho * exp t2} /\
     (!z. t1 <= z$1 /\ z$1 <= t2 ==> g z = (rho * exp(z$1)) pow 2 % h(cmcy_phi y rho z))
     ==> integral (cmc_ann y (rho * exp t1) (rho * exp t2)) h =
         integral (interval[lift t1,lift t2])
           (\t. integral (interval[vec 0,lift(&2 * pi)]) (\q. g(vector[drop t; drop q])))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^2`; `rho:real`; `t1:real`; `t2:real`; `h:real^2->real^N`]
                CMCY_POLAR) THEN
  ASM_SIMP_TAC[CMCY_ANN_ABSINT] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `t:real^1` THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `integral (interval[vec 0,lift(&2 * pi)])
      (\q. (rho * exp(drop t)) pow 2 %
           (h:real^2->real^N)(cmcy_phi y rho (vector[drop t; drop q])))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC CMCY_SECTION_CONT THEN
    MAP_EVERY EXISTS_TAC [`t1:real`; `t2:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `q:real^1` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vector[drop t; drop q]:real^2`) THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

(* The angular and total energy densities of v on the circle {t} x [0,2pi]. *)

let cmcy_f = new_definition
 `cmcy_f (v:real^2->real^K) t =
    drop(integral (interval[vec 0,lift(&2 * pi)])
           (\q. lift(norm(partial_derivative 2 v (vector[t; drop q])) pow 2)))`;;

let cmcy_dd = new_definition
 `cmcy_dd (v:real^2->real^K) t =
    drop(integral (interval[vec 0,lift(&2 * pi)])
           (\q. lift(norm(partial_derivative 1 v (vector[t; drop q])) pow 2 +
                     norm(partial_derivative 2 v (vector[t; drop q])) pow 2)))`;;

let CMCY_PD_CONT = prove
 (`!s (u:real^2->real^K) k i.
     open s /\ smooth_map_on s u /\ k SUBSET s ==> partial_derivative i u continuous_on k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `s:real^2->bool` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

let CMCY_ANGD_CONT = prove
 (`!s y (u:real^2->real^K) k.
     open s /\ smooth_map_on s u /\ k SUBSET s /\ (!x. x IN k ==> ~(x = y))
     ==> (\x. lift(norm(cmc_angd y x (partial_derivative 1 u x)
                                     (partial_derivative 2 u x)) pow 2))
         continuous_on k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. partial_derivative i (u:real^2->real^K) continuous_on k` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CMCY_PD_CONT THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^2. lift((x - y)$1)) continuous_on k /\
                (\x:real^2. lift((x - y)$2)) continuous_on k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
  MATCH_MP_TAC(TAUT `p ==> p /\ p`) THEN REWRITE_TAC[cmc_angd] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(lift o (\x:real^2. inv(norm(x - y)))) = (lift o inv o (\x. norm(x - y)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN
    ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_NEG; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_NEG THEN ASM_REWRITE_TAC[]]);;

let CMCY_GRAD_CONT = prove
 (`!s (u:real^2->real^K) k.
     open s /\ smooth_map_on s u /\ k SUBSET s
     ==> (\x. lift(norm(partial_derivative 1 u x) pow 2 +
                   norm(partial_derivative 2 u x) pow 2)) continuous_on k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. partial_derivative i (u:real^2->real^K) continuous_on k` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CMCY_PD_CONT THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_ADD; NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN ASM_REWRITE_TAC[ETA_AX]);;

let CMCY_CANN_PHI = prove
 (`!y rho t1 t2 z.
     &0 < rho /\ t1 <= z$1 /\ z$1 <= t2
     ==> cmcy_phi y rho z IN
         {x | rho * exp t1 <= norm(x - y) /\ norm(x - y) <= rho * exp t2} /\
         ~(cmcy_phi y rho z = y) /\
         norm(cmcy_phi y rho z - y) = rho * exp(z$1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMCY_PHI_NORM; REAL_LT_IMP_LE; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE];
    DISCH_TAC THEN
    MP_TAC(SPECL [`y:real^2`; `rho:real`; `z:real^2`] CMCY_PHI_NORM) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_IMP_NZ; REAL_LT_MUL; REAL_EXP_POS_LT]]);;

let CMCY_ANG_TO_CYL = prove
 (`!s y rho t1 t2 (u:real^2->real^K).
     open s /\ smooth_map_on s u /\ &0 < rho /\ t1 <= t2 /\
     {x | rho * exp t1 <= norm(x - y) /\ norm(x - y) <= rho * exp t2} SUBSET s
     ==> drop(integral (cmc_ann y (rho * exp t1) (rho * exp t2))
                (\x. lift(norm(cmc_angd y x (partial_derivative 1 u x)
                                            (partial_derivative 2 u x)) pow 2))) =
         drop(integral (interval[lift t1,lift t2])
                (\t. lift(cmcy_f (u o cmcy_phi y rho) (drop t))))`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[cmcy_f; LIFT_DROP] THEN
  MP_TAC(ISPECL [`y:real^2`; `rho:real`; `t1:real`; `t2:real`;
                 `\x. lift(norm(cmc_angd y x (partial_derivative 1 (u:real^2->real^K) x)
                                             (partial_derivative 2 u x)) pow 2)`;
                 `\z. lift(norm(partial_derivative 2 ((u:real^2->real^K) o cmcy_phi y rho) z)
                           pow 2)`] CMCY_CYL_TRANSFER) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMCY_ANGD_CONT THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `rho * exp t1 <= norm(y - y:real^2)` THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_NOT_LE] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^2`; `rho:real`; `t1:real`; `t2:real`; `z:real^2`] CMCY_CANN_PHI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cmcy_phi y rho z IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `y:real^2`; `rho:real`; `u:real^2->real^K`; `z:real^2`]
                CMCY_CYL_D1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`y:real^2`; `u:real^2->real^K`; `cmcy_phi y rho z`] CMCY_AD_ANGD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_POW_MUL; LIFT_CMUL; REAL_POW2_ABS]);;

let CMCY_GRAD_TO_CYL = prove
 (`!s y rho t1 t2 (u:real^2->real^K).
     open s /\ smooth_map_on s u /\ &0 < rho /\ t1 <= t2 /\
     {x | rho * exp t1 <= norm(x - y) /\ norm(x - y) <= rho * exp t2} SUBSET s
     ==> drop(integral (cmc_ann y (rho * exp t1) (rho * exp t2))
                (\x. lift(norm(partial_derivative 1 u x) pow 2 +
                          norm(partial_derivative 2 u x) pow 2))) =
         drop(integral (interval[lift t1,lift t2])
                (\t. lift(cmcy_dd (u o cmcy_phi y rho) (drop t))))`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[cmcy_dd; LIFT_DROP] THEN
  MP_TAC(ISPECL [`y:real^2`; `rho:real`; `t1:real`; `t2:real`;
                 `\x. lift(norm(partial_derivative 1 (u:real^2->real^K) x) pow 2 +
                           norm(partial_derivative 2 u x) pow 2)`;
                 `\z. lift(norm(partial_derivative 1 ((u:real^2->real^K) o cmcy_phi y rho) z)
                           pow 2 +
                           norm(partial_derivative 2 (u o cmcy_phi y rho) z) pow 2)`]
                CMCY_CYL_TRANSFER) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMCY_GRAD_CONT THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^2`; `rho:real`; `t1:real`; `t2:real`; `z:real^2`] CMCY_CANN_PHI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cmcy_phi y rho z IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `y:real^2`; `rho:real`; `u:real^2->real^K`; `z:real^2`]
                CMCY_CYL_D1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`y:real^2`; `u:real^2->real^K`; `cmcy_phi y rho z`] CMCY_RD_AD_NORMS) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[LIFT_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* Calculus on the strip: derivatives along the lines vector[s; q],          *)
(* differentiation in t of int_0^{2pi} h(vector[t; q]) dq for smooth h, the  *)
(* periodicity of Phi in theta and integration by parts in theta.            *)
(* ------------------------------------------------------------------------- *)

let CMCY_VEC2_LINES = prove
 (`!s q. (vector[&0; q]:real^2) + s % basis 1 = vector[s; q] /\
         (vector[s; &0]:real^2) + q % basis 2 = vector[s; q]`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; CMCY_BASIS2] THEN REAL_ARITH_TAC);;

let CMCY_SEC_VDERIV = prove
 (`!(u:real^2->real^N) s q.
     u differentiable (at (vector[s; q]))
     ==> ((\r. u(vector[drop r; q])) has_vector_derivative
          partial_derivative 1 u (vector[s; q])) (at (lift s)) /\
         ((\r. u(vector[s; drop r])) has_vector_derivative
          partial_derivative 2 u (vector[s; q])) (at (lift q))`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`u:real^2->real^N`; `vector[&0; q]:real^2`; `1`; `s:real`]
                  PDE_LINE_DERIV);
    MP_TAC(ISPECL [`u:real^2->real^N`; `vector[s; &0]:real^2`; `2`; `q:real`]
                  PDE_LINE_DERIV)] THEN
  ASM_REWRITE_TAC[CMCY_VEC2_LINES]);;

let CMCY_SEC_RDERIV = prove
 (`!(u:real^2->real^1) s q.
     u differentiable (at (vector[s; q]))
     ==> ((\s. drop(u(vector[s; q]))) has_real_derivative
          drop(partial_derivative 1 u (vector[s; q]))) (atreal s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  ASM_SIMP_TAC[CMCY_SEC_VDERIV]);;

let CMCY_LINE_CONT = prove
 (`!s. (\r:real^1. vector[s; drop r]:real^2) continuous_on (:real^1)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\r:real^1. vector[s; drop r]:real^2) = (\r. vector[s; &0] + drop r % basis 2)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; CMCY_VEC2_LINES]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]);;

let CMCY_STRIP_LINEAR = prove
 (`linear(\z:real^(1,1)finite_sum. vector[drop(sndcart z); drop(fstcart z)]:real^2)`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
              DROP_ADD; DROP_CMUL]);;

let CMCY_PARAM_DERIV = prove
 (`!O (h:real^2->real^1) c d.
     open O /\ smooth_map_on O h /\ c <= d /\
     (!s q. c <= s /\ s <= d ==> vector[s; q] IN O)
     ==> !t. c <= t /\ t <= d
             ==> ((\s. drop(integral (interval[vec 0,lift(&2 * pi)])
                                     (\q. h(vector[s; drop q]))))
                  has_real_derivative
                  drop(integral (interval[vec 0,lift(&2 * pi)])
                         (\q. partial_derivative 1 h (vector[t; drop q]))))
                 (atreal t within real_interval[c,d])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN O ==> (h:real^2->real^1) differentiable (at z)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `O:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `h continuous_on (O:real^2->bool) /\
                partial_derivative 1 (h:real^2->real^1) continuous_on O`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^1 s. drop((h:real^2->real^1)(vector[s; drop x]))`;
                 `\x:real^1 s. drop(partial_derivative 1 (h:real^2->real^1)
                                                       (vector[s; drop x]))`;
                 `vec 0:real^1`; `lift(&2 * pi)`; `c:real`; `d:real`; `t:real`]
                NSPU_REAL_PARAMETRIC_INTEGRAL) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^1`; `s:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC CMCY_SEC_RDERIV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `(\z. partial_derivative 1 (h:real^2->real^1) (vector[drop(sndcart z); drop(fstcart z)])) =
      partial_derivative 1 h o
      (\z:real^(1,1)finite_sum. vector[drop(sndcart z); drop(fstcart z)]:real^2)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; CMCY_STRIP_LINEAR] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                    SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    SUBGOAL_THEN `(\x:real^1. (h:real^2->real^1)(vector[s; drop x])) =
                  h o (\r. vector[s; drop r])` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      REWRITE_TAC[CMCY_LINE_CONT; SUBSET_UNIV];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^2->bool` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let CMCY_PHI_PERIODIC = prove
 (`!y rho t. cmcy_phi y rho (vector[t; &2 * pi]) = cmcy_phi y rho (vector[t; &0])`,
  REWRITE_TAC[CMCY_PHI_CIRC; VECTOR_2; wan_circ] THEN
  REWRITE_TAC[REWRITE_RULE[REAL_ADD_LID] (SPEC `&0` COS_PERIODIC);
              REWRITE_RULE[REAL_ADD_LID] (SPEC `&0` SIN_PERIODIC)]);;

let CMCY_LINE_INTEGRABLE = prove
 (`!O (h:real^2->real^N) t a b.
     h continuous_on O /\ (!q. vector[t; q] IN O)
     ==> (\q. h(vector[t; drop q])) continuous_on (:real^1) /\
         (\q. h(vector[t; drop q])) integrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\q:real^1. (h:real^2->real^N)(vector[t; drop q])) =
                  h o (\r. vector[t; drop r])` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CMCY_LINE_CONT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE];
    DISCH_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let CMCY_THETA_FTC = prove
 (`!O (h:real^2->real^N) t x.
     open O /\ smooth_map_on O h /\ (!q. vector[t; q] IN O) /\ &0 <= drop x
     ==> ((\q. partial_derivative 2 h (vector[t; drop q])) has_integral
          (h(vector[t; drop x]) - h(vector[t; &0]))) (interval[vec 0,x])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r:real^1. (h:real^2->real^N)(vector[t; drop r])`;
                 `\q:real^1. partial_derivative 2 (h:real^2->real^N) (vector[t; drop q])`;
                 `vec 0:real^1`; `x:real^1`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[DROP_VEC] THEN ANTS_TAC THENL
   [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    MP_TAC(ISPECL [`h:real^2->real^N`; `t:real`; `drop r`] CMCY_SEC_VDERIV) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    REWRITE_TAC[DROP_VEC]]);;

let CMCY_THETA_IBP = prove
 (`!O (a:real^2->real^N) (b:real^2->real^N) t.
     open O /\ smooth_map_on O a /\ smooth_map_on O b /\ (!q. vector[t; q] IN O) /\
     a(vector[t; &2 * pi]) dot b(vector[t; &2 * pi]) =
     a(vector[t; &0]) dot b(vector[t; &0])
     ==> integral (interval[vec 0,lift(&2 * pi)])
           (\q. lift(partial_derivative 2 a (vector[t; drop q]) dot b(vector[t; drop q]))) =
         --(integral (interval[vec 0,lift(&2 * pi)])
              (\q. lift(a(vector[t; drop q]) dot partial_derivative 2 b (vector[t; drop q]))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on O (\z. lift((a:real^2->real^N) z dot b z))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^2->bool`; `\z. lift((a:real^2->real^N) z dot (b:real^2->real^N) z)`;
                 `t:real`;
                 `lift(&2 * pi)`] CMCY_THETA_FTC) THEN
  ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_MUL; REAL_POS; PI_POS_LE; VECTOR_SUB_REFL] THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; PI_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. partial_derivative 2 (\z. lift((a:real^2->real^N) z dot (b:real^2->real^N) z))
          (vector[t; drop q]) =
        lift(partial_derivative 2 a (vector[t; drop q]) dot b(vector[t; drop q])) +
        lift(a(vector[t; drop q]) dot partial_derivative 2 b (vector[t; drop q]))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC PDE_PARTIAL_DOT THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  SUBGOAL_THEN
   `(\q. lift(partial_derivative 2 (a:real^2->real^N) (vector[t; drop q]) dot
              (b:real^2->real^N)(vector[t; drop q]))) integrable_on
    interval[vec 0,lift(&2 * pi)] /\
    (\q. lift((a:real^2->real^N)(vector[t; drop q]) dot
              partial_derivative 2 (b:real^2->real^N) (vector[t; drop q]))) integrable_on
    interval[vec 0,lift(&2 * pi)]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN (
    MP_TAC(ISPECL [`O:real^2->bool`;
                   `\z. lift(partial_derivative 2 (a:real^2->real^N) z dot
                             (b:real^2->real^N) z)`; `t:real`;
                   `vec 0:real^1`; `lift(&2 * pi)`] CMCY_LINE_INTEGRABLE) THEN
    MP_TAC(ISPECL [`O:real^2->bool`;
                   `\z. lift((a:real^2->real^N) z dot
                             partial_derivative 2 (b:real^2->real^N) z)`; `t:real`;
                   `vec 0:real^1`; `lift(&2 * pi)`] CMCY_LINE_INTEGRABLE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\z. lift((a:real^2->real^N) z dot partial_derivative 2 (b:real^2->real^N) z))
                  continuous_on O /\
                  (\z. lift(partial_derivative 2 (a:real^2->real^N) z dot (b:real^2->real^N) z))
                  continuous_on O`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
      SIMP_TAC[]]);
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD] THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The second derivative of f(t) = int_0^{2pi} |v_theta(t,q)|^2 dq for       *)
(* smooth v, 2pi-periodic in theta:                                          *)
(*   f'' = 2 int v_ttheta . v_theta... = 2 int |v_ttheta|^2 - 2 int v_tt .   *)
(*   v_thetatheta >= f - int |v_tt + v_thetatheta|^2                         *)
(* (integration by parts in theta and Wirtinger for v_theta).                *)
(* ------------------------------------------------------------------------- *)

let CMCY_LINE_INT_SMOOTH = prove
 (`!O (h:real^2->real^N) t a b.
     smooth_map_on O h /\ (!q. vector[t; q] IN O)
     ==> (\q. h(vector[t; drop q])) integrable_on interval[a,b]`,
  MESON_TAC[CMCY_LINE_INTEGRABLE; SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let CMCY_H2_PD2 = prove
 (`!O (v:real^2->real^K) z.
     open O /\ smooth_map_on O v /\ z IN O
     ==> partial_derivative 1
           (partial_derivative 1 (\z. lift(norm(partial_derivative 2 v z) pow 2))) z =
         &2 % lift(partial_derivative 1 (partial_derivative 1 (partial_derivative 2 v)) z dot
                   partial_derivative 2 v z) +
         &2 % lift(norm(partial_derivative 1 (partial_derivative 2 v) z) pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `b = partial_derivative 2 (v:real^2->real^K)` THEN
  SUBGOAL_THEN `smooth_map_on O (b:real^2->real^K) /\
                smooth_map_on O (partial_derivative 1 b) /\
                smooth_map_on O (partial_derivative 1 (partial_derivative 1 b))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN O ==> (b:real^2->real^K) differentiable (at w) /\
                               partial_derivative 1 b differentiable (at w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `O:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `partial_derivative 1
      (\w. lift(partial_derivative 1 (b:real^2->real^K) w dot b w) +
           lift(b w dot partial_derivative 1 b w)) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `O:real^2->bool` THEN
    ASM_REWRITE_TAC[NORM_POW_2] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PDE_PARTIAL_DOT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift(partial_derivative 1 (b:real^2->real^K) w dot b w)) differentiable (at z) /\
    (\w. lift((b:real^2->real^K) w dot partial_derivative 1 b w)) differentiable (at z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `O:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_ADD] THEN
  ASM_SIMP_TAC[PDE_PARTIAL_DOT; ETA_AX] THEN
  REWRITE_TAC[NORM_POW_2] THEN
  REWRITE_TAC[DOT_SYM] THEN VECTOR_ARITH_TAC);;

let CMCY_E3_EQ = prove
 (`!O (v:real^2->real^K) z.
     open O /\ smooth_map_on O v /\ z IN O
     ==> partial_derivative 1 (partial_derivative 1 (partial_derivative 2 v)) z =
         partial_derivative 2 (partial_derivative 1 (partial_derivative 1 v)) z`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `partial_derivative 1 (partial_derivative 2 (partial_derivative 1 (v:real^2->real^K))) (z:real^2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `O:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_SYM THEN
    EXISTS_TAC `O:real^2->bool` THEN ASM_REWRITE_TAC[DIMINDEX_2; ARITH] THEN
    ASM_MESON_TAC[smooth_map_on];
    MATCH_MP_TAC PARTIAL_DERIVATIVE_SYM THEN
    EXISTS_TAC `O:real^2->bool` THEN ASM_REWRITE_TAC[DIMINDEX_2; ARITH] THEN
    ASM_MESON_TAC[smooth_map_on; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]]);;

let CMCY_F2_LOWER = prove
 (`!O (v:real^2->real^K) t.
     open O /\ smooth_map_on O v /\ (!q. vector[t; q] IN O) /\
     v(vector[t; &2 * pi]) = v(vector[t; &0]) /\
     partial_derivative 2 v (vector[t; &2 * pi]) = partial_derivative 2 v (vector[t; &0]) /\
     partial_derivative 1 (partial_derivative 1 v) (vector[t; &2 * pi]) =
     partial_derivative 1 (partial_derivative 1 v) (vector[t; &0])
     ==> cmcy_f v t -
         drop(integral (interval[vec 0,lift(&2 * pi)])
                (\q. lift(norm(partial_derivative 1 (partial_derivative 1 v) (vector[t; drop q]) +
                               partial_derivative 2 (partial_derivative 2 v) (vector[t; drop q]))
                          pow 2)))
         <= drop(integral (interval[vec 0,lift(&2 * pi)])
                   (\q. partial_derivative 1
                          (partial_derivative 1 (\z. lift(norm(partial_derivative 2 v z) pow 2)))
                          (vector[t; drop q])))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!q. partial_derivative 1
          (partial_derivative 1 (\z. lift(norm(partial_derivative 2 (v:real^2->real^K) z) pow 2)))
          (vector[t; drop q]) =
        &2 % lift(partial_derivative 2 (partial_derivative 1 (partial_derivative 1 v))
                    (vector[t; drop q]) dot partial_derivative 2 v (vector[t; drop q])) +
        &2 % lift(norm(partial_derivative 1 (partial_derivative 2 v) (vector[t; drop q])) pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`O:real^2->bool`; `v:real^2->real^K`; `vector[t; drop q]:real^2`]
                  CMCY_H2_PD2) THEN
    MP_TAC(ISPECL [`O:real^2->bool`; `v:real^2->real^K`; `vector[t; drop q]:real^2`]
                  CMCY_E3_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* smoothness of the integrands, hence integrability on the circle *)
  SUBGOAL_THEN
   `!i j. smooth_map_on O (partial_derivative i (v:real^2->real^K)) /\
          smooth_map_on O (partial_derivative i (partial_derivative j v)) /\
          smooth_map_on O (partial_derivative i (partial_derivative j (partial_derivative 1 v)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(h:real^2->real^1). smooth_map_on O h
        ==> (\q. h(vector[t; drop q])) integrable_on interval[vec 0,lift(&2 * pi)]`
  (LABEL_TAC "lint") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMCY_LINE_INT_SMOOTH THEN
    EXISTS_TAC `O:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ia = drop(integral (interval[vec 0,lift(&2 * pi)])
     (\q. lift(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) (vector[t; drop q]) dot
               partial_derivative 2 (partial_derivative 2 v) (vector[t; drop q]))))` THEN
  ABBREV_TAC `ic = drop(integral (interval[vec 0,lift(&2 * pi)])
     (\q. lift(norm(partial_derivative 2 (partial_derivative 2 (v:real^2->real^K))
                    (vector[t; drop q])) pow 2)))` THEN
  ABBREV_TAC `id = drop(integral (interval[vec 0,lift(&2 * pi)])
     (\q. lift(norm(partial_derivative 1 (partial_derivative 2 (v:real^2->real^K))
                    (vector[t; drop q])) pow 2)))` THEN
  ABBREV_TAC `iw = drop(integral (interval[vec 0,lift(&2 * pi)])
     (\q. lift(norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) (vector[t; drop q]) +
                    partial_derivative 2 (partial_derivative 2 v) (vector[t; drop q])) pow 2)))` THEN
  (* the right side is -2 ia + 2 id *)
  SUBGOAL_THEN
   `drop(integral (interval[vec 0,lift(&2 * pi)])
      (\q. &2 % lift(partial_derivative 2 (partial_derivative 1 (partial_derivative 1 v))
                       (vector[t; drop q]) dot partial_derivative 2 (v:real^2->real^K)
                                                 (vector[t; drop q])) +
           &2 % lift(norm(partial_derivative 1 (partial_derivative 2 v) (vector[t; drop q]))
                     pow 2))) = --(&2 * ia) + &2 * id`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`O:real^2->bool`; `partial_derivative 1 (partial_derivative 1 (v:real^2->real^K))`;
                   `partial_derivative 2 (v:real^2->real^K)`; `t:real`] CMCY_THETA_IBP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["ia"; "id"] THEN
    SUBGOAL_THEN
     `(\q. lift(partial_derivative 2 (partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)))
                  (vector[t; drop q]) dot partial_derivative 2 v (vector[t; drop q])))
      integrable_on interval[vec 0,lift(&2 * pi)] /\
      (\q. lift(norm(partial_derivative 1 (partial_derivative 2 (v:real^2->real^K))
                       (vector[t; drop q])) pow 2))
      integrable_on interval[vec 0,lift(&2 * pi)]`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "lint" (MP_TAC o SPEC
         `\z. lift(partial_derivative 2 (partial_derivative 1 (partial_derivative 1
                     (v:real^2->real^K))) z dot partial_derivative 2 v z)`);
        USE_THEN "lint" (MP_TAC o SPEC
         `\z. lift(norm(partial_derivative 1 (partial_derivative 2 (v:real^2->real^K)) z)
                   pow 2)`)] THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_DOT_OPEN; SMOOTH_MAP_ON_NORM_POW2_OPEN; ETA_AX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_CMUL; INTEGRAL_CMUL; DROP_ADD; DROP_CMUL] THEN
    REWRITE_TAC[DROP_NEG] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * pi` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; PI_POS_LE]; ALL_TAC] THEN
  (* Wirtinger for v_theta *)
  SUBGOAL_THEN `cmcy_f (v:real^2->real^K) t <= ic` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:K)` WAN_WIRTINGER_VEC) THEN REWRITE_TAC[WAN_WIRTINGER_VEC_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`\x. partial_derivative 2 (v:real^2->real^K) (vector[t; x])`;
      `\x. partial_derivative 2 (partial_derivative 2 (v:real^2->real^K)) (vector[t; x])`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`O:real^2->bool`; `partial_derivative 2 (v:real^2->real^K)`; `t:real`;
                       `lift x`] CMCY_THETA_FTC) THEN
        ASM_REWRITE_TAC[LIFT_DROP];
        ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`O:real^2->bool`; `v:real^2->real^K`; `t:real`;
                       `lift(&2 * pi)`] CMCY_THETA_FTC) THEN
        ASM_REWRITE_TAC[LIFT_DROP; VECTOR_SUB_REFL];
        USE_THEN "lint" (MP_TAC o SPEC
         `\z. lift(norm(partial_derivative 2 (partial_derivative 2 (v:real^2->real^K)) z)
                   pow 2)`) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_NORM_POW2_OPEN; ETA_AX]];
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN EXPAND_TAC "ic" THEN REWRITE_TAC[cmcy_f]];
    ALL_TAC] THEN
  (* the pointwise inequality |C|^2 <= |A + C|^2 - 2 A.C *)
  SUBGOAL_THEN `ic <= iw - &2 * ia` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ic"; "iw"; "ia"] THEN
    SUBGOAL_THEN
     `(\q. lift(norm(partial_derivative 2 (partial_derivative 2 (v:real^2->real^K))
                       (vector[t; drop q])) pow 2)) integrable_on interval[vec 0,lift(&2 * pi)] /\
      (\q. lift(norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K))
                       (vector[t; drop q]) +
                     partial_derivative 2 (partial_derivative 2 v) (vector[t; drop q])) pow 2))
      integrable_on interval[vec 0,lift(&2 * pi)] /\
      (\q. lift(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) (vector[t; drop q]) dot
                partial_derivative 2 (partial_derivative 2 v) (vector[t; drop q])))
      integrable_on interval[vec 0,lift(&2 * pi)]`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "lint" (MP_TAC o SPEC
         `\z. lift(norm(partial_derivative 2 (partial_derivative 2 (v:real^2->real^K)) z)
                   pow 2)`);
        USE_THEN "lint" (MP_TAC o SPEC
         `\z. lift(norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) z +
                        partial_derivative 2 (partial_derivative 2 v) z) pow 2)`);
        USE_THEN "lint" (MP_TAC o SPEC
         `\z. lift(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) z dot
                   partial_derivative 2 (partial_derivative 2 v) z)`)] THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_NORM_POW2_OPEN; SMOOTH_MAP_ON_DOT_OPEN;
                   SMOOTH_MAP_ON_ADD_OPEN; ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral (interval[vec 0,lift(&2 * pi)])
        (\q. lift(norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K))
                         (vector[t; drop q]) +
                       partial_derivative 2 (partial_derivative 2 v) (vector[t; drop q])) pow 2) -
             &2 % lift(partial_derivative 1 (partial_derivative 1 v) (vector[t; drop q]) dot
                       partial_derivative 2 (partial_derivative 2 v) (vector[t; drop q]))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_CMUL] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_SUB; DROP_CMUL; LIFT_DROP] THEN
      REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD] THEN
      MP_TAC(ISPEC `partial_derivative 1 (partial_derivative 1 (v:real^2->real^K))
                      (vector[t; drop x])` DOT_POS_LE) THEN
      REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRABLE_CMUL; INTEGRAL_CMUL; DROP_SUB; DROP_CMUL] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= id` ASSUME_TAC THENL
   [EXPAND_TAC "id" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    USE_THEN "lint" (MP_TAC o SPEC
     `\z. lift(norm(partial_derivative 1 (partial_derivative 2 (v:real^2->real^K)) z) pow 2)`) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_NORM_POW2_OPEN; ETA_AX];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* One-dimensional comparison (CM B.8 with the barrier cosh(t/2)).           *)
(* CMCY_MAXPR: a maximum principle for w'' > 0 where w > 0.  CMCY_ODE_BOUND: *)
(* if f >= 0 is continuous on [-2l,2l], twice differentiable inside, and f'' *)
(* >= f/4 - A there (A >= 0), then                                           *)
(*   int_{-l}^{l} f <= 8 l A + 8 exp(-l/4) int_{-2l}^{2l} f.                 *)
(* ------------------------------------------------------------------------- *)

let CMCY_MAXPR = prove
 (`!w w' w'' a b.
     a <= b /\ w real_continuous_on real_interval[a,b] /\
     (!t. t IN real_interval(a,b)
          ==> (w has_real_derivative w' t) (atreal t) /\
              (w' has_real_derivative w'' t) (atreal t)) /\
     (!t. t IN real_interval(a,b) /\ &0 < w t ==> &0 < w'' t) /\
     w a <= &0 /\ w b <= &0
     ==> !t. t IN real_interval[a,b] ==> w t <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t1:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(w:real->real) t1 <= &0` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`w:real->real`; `real_interval[a,b]`] REAL_CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_NE_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (w:real->real) t0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t1:real`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t0 IN real_interval(a,b)` ASSUME_TAC THENL
   [UNDISCH_TAC `t0 IN real_interval[a,b]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl))) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w':real->real) t0 = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_ZERO_MAXMIN THEN
    MAP_EVERY EXISTS_TAC [`w:real->real`; `t0:real`; `real_interval(a,b)`] THEN
    ASM_SIMP_TAC[REAL_OPEN_REAL_INTERVAL] THEN DISJ1_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] REAL_INTERVAL_OPEN_SUBSET_CLOSED) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ !t. abs(t - t0) < d ==> &0 < (w:real->real) t`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`w:real->real`; `t0:real`] REAL_CONTINUOUS_ATREAL) THEN
    SUBGOAL_THEN `(w:real->real) real_continuous (atreal t0)` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `(w':real->real) t0` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REALLIM_ATREAL] THEN DISCH_THEN(MP_TAC o SPEC `(w:real->real) t0`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `t:real = t0` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `t2 = t0 + min d (b - t0) / &2` THEN
  SUBGOAL_THEN `t0 < t2 /\ t2 < b /\ t2 - t0 < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t2" THEN UNDISCH_TAC `t0 IN real_interval(a,b)` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t0 <= t /\ t <= t2 ==> t IN real_interval(a,b)` ASSUME_TAC THENL
   [UNDISCH_TAC `t0 IN real_interval(a,b)` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t0 < t /\ t <= t2 ==> &0 < (w':real->real) t` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`w':real->real`; `w'':real->real`; `t0:real`; `t:real`] REAL_MVT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
        REWRITE_TAC[real_differentiable_on] THEN X_GEN_TAC `q:real` THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        EXISTS_TAC `(w'':real->real) q` THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MP_TAC(SPEC `q:real` (ASSUME `!t. t IN real_interval(a,b)
          ==> ((w:real->real) has_real_derivative w' t) (atreal t) /\
              ((w':real->real) has_real_derivative w'' t) (atreal t)`)) THEN
        ANTS_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        X_GEN_TAC `q:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        MP_TAC(SPEC `q:real` (ASSUME `!t. t IN real_interval(a,b)
          ==> ((w:real->real) has_real_derivative w' t) (atreal t) /\
              ((w':real->real) has_real_derivative w'' t) (atreal t)`)) THEN
        ANTS_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `q IN real_interval(t0,t)` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (w'':real->real) q` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `&0 < (w:real->real) t`)) (concl th))) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (w'':real->real) q * (t - t0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real->real`; `w':real->real`; `t0:real`; `t2:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[a,b]` THEN
      ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
      UNDISCH_TAC `t0 IN real_interval(a,b)` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `q:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MP_TAC(SPEC `q:real` (ASSUME `!t. t IN real_interval(a,b)
          ==> ((w:real->real) has_real_derivative w' t) (atreal t) /\
              ((w':real->real) has_real_derivative w'' t) (atreal t)`)) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `q IN real_interval(t0,t2)` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (w':real->real) q` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real->real) t2 <= w t0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `t0 IN real_interval(a,b)` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (w':real->real) q * (t2 - t0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let CMCY_BARRIER_DERIVS = prove
 (`!K t. ((\t. K * (exp(t / &2) + exp(--(t / &2)))) has_real_derivative
          K * (exp(t / &2) / &2 - exp(--(t / &2)) / &2)) (atreal t) /\
         ((\t. K * (exp(t / &2) / &2 - exp(--(t / &2)) / &2)) has_real_derivative
          K * (exp(t / &2) + exp(--(t / &2))) / &4) (atreal t)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC);;

let CMCY_MIN_LE_MEAN = prove
 (`!f a b. a < b /\ f real_continuous_on real_interval[a,b]
           ==> ?t. t IN real_interval[a,b] /\
                   f t * (b - a) <= real_integral (real_interval[a,b]) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `real_interval[a,b]`] REAL_CONTINUOUS_ATTAINS_INF) THEN
  ASM_SIMP_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_NE_EMPTY; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\x:real. (f:real->real) t`; `f:real->real`; `real_interval[a,b]`]
                REAL_INTEGRAL_LE) THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_CONST; REAL_INTEGRABLE_CONTINUOUS; REAL_INTEGRAL_CONST;
               REAL_LT_IMP_LE]);;

let CMCY_ODE_BOUND = prove
 (`!f f' f'' A l.
     &0 < l /\ &0 <= A /\
     f real_continuous_on real_interval[--(&2 * l),&2 * l] /\
     (!t. t IN real_interval(--(&2 * l),&2 * l)
          ==> (f has_real_derivative f' t) (atreal t) /\
              (f' has_real_derivative f'' t) (atreal t) /\
              f t / &4 - A <= f'' t) /\
     (!t. t IN real_interval[--(&2 * l),&2 * l] ==> &0 <= f t)
     ==> real_integral (real_interval[--l,l]) f
         <= &8 * l * A + &8 * exp(--(l / &4)) *
            real_integral (real_interval[--(&2 * l),&2 * l]) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `E = real_integral (real_interval[--(&2 * l),&2 * l]) f` THEN
  SUBGOAL_THEN `f real_integrable_on real_interval[--(&2 * l),&2 * l]` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. --(&2 * l) <= a /\ a <= b /\ b <= &2 * l
          ==> f real_continuous_on real_interval[a,b] /\
              f real_integrable_on real_interval[a,b] /\
              real_integral (real_interval[a,b]) f <= E`
  (LABEL_TAC "sub") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `real_interval[a,b] SUBSET real_interval[--(&2 * l),&2 * l]`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `f real_continuous_on real_interval[a,b]` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS] THEN
    EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS];
    ALL_TAC] THEN
  (* the end points *)
  MP_TAC(ISPECL [`f:real->real`; `&3 * l / &2`; `&2 * l`] CMCY_MIN_LE_MEAN) THEN
  USE_THEN "sub" (MP_TAC o SPECL [`&3 * l / &2`; `&2 * l`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tp:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real->real`; `--(&2 * l)`; `--(&3 * l / &2)`] CMCY_MIN_LE_MEAN) THEN
  USE_THEN "sub" (MP_TAC o SPECL [`--(&2 * l)`; `--(&3 * l / &2)`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tm:real` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  SUBGOAL_THEN `(f:real->real) tp <= (&2 * E) / l /\ f tm <= (&2 * E) / l` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the barrier *)
  ABBREV_TAC `K = (&2 * E / l) * exp(--(&3 * l / &4))` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_EXP_POS_LE; REAL_LT_IMP_LE; REAL_LE_MUL; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `K * exp(&3 * l / &4) = &2 * E / l /\
                K * exp(l / &2) = (&2 * E / l) * exp(--(l / &4))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    REWRITE_TAC[REAL_ARITH `(a * b) * c = a * (b * c):real`; GSYM REAL_EXP_ADD] THEN
    CONJ_TAC THEN AP_TERM_TAC THENL
     [REWRITE_TAC[REAL_ARITH `--x + x = &0`; REAL_EXP_0; REAL_MUL_RID];
      AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (f:real->real) t - &4 * A - K * (exp(t / &2) + exp(--(t / &2)))`;
                 `\t. (f':real->real) t - K * (exp(t / &2) / &2 - exp(--(t / &2)) / &2)`;
                 `\t. (f'':real->real) t - K * (exp(t / &2) + exp(--(t / &2))) / &4`;
                 `tm:real`; `tp:real`] CMCY_MAXPR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `!t. ((\t. K * (exp(t / &2) + exp(--(t / &2)))) has_real_derivative
                       K * (exp(t / &2) / &2 - exp(--(t / &2)) / &2)) (atreal t) /\
                      ((\t. K * (exp(t / &2) / &2 - exp(--(t / &2)) / &2))
                       has_real_derivative K * (exp(t / &2) + exp(--(t / &2))) / &4)
                      (atreal t)`
    ASSUME_TAC THENL [REWRITE_TAC[CMCY_BARRIER_DERIVS]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
        REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `real_interval[--(&2 * l),&2 * l]` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
        REWRITE_TAC[real_differentiable_on] THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC `K * (exp(x / &2) / &2 - exp(--(x / &2)) / &2)` THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        can (find_term ((=) `f'':real->real`)) (concl th) && is_forall(concl th) &&
        can (find_term ((=) `A:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `t:real` o check (fun th ->
        can (find_term ((=) `K:real`)) (concl th) && is_forall(concl th))) THEN
      CONJ_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_SUB_RZERO] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
      ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; ETA_AX];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        can (find_term ((=) `f'':real->real`)) (concl th) && is_forall(concl th) &&
        can (find_term ((=) `A:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `K * exp(&3 * l / &4) <= K * exp(--(tm / &2)) /\
                    &0 <= K * exp(tm / &2)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]];
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `K * exp(&3 * l / &4) <= K * exp(tp / &2) /\
                    &0 <= K * exp(--(tp / &2))` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]];
        ASM_REAL_ARITH_TAC]];
    DISCH_TAC] THEN
  (* integrate the bound over [-l,l] *)
  SUBGOAL_THEN
   `!t. t IN real_interval[--l,l]
        ==> (f:real->real) t <= &4 * A + &2 * ((&2 * E / l) * exp(--(l / &4)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `K * exp(t / &2) <= K * exp(l / &2) /\
                  K * exp(--(t / &2)) <= K * exp(l / &2)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "sub" (MP_TAC o SPECL [`--l:real`; `l:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`;
                 `\t:real. &4 * A + &2 * ((&2 * E / l) * exp(--(l / &4)))`;
                 `real_interval[--l,l]`] REAL_INTEGRAL_LE) THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_CONST; REAL_INTEGRAL_CONST;
               REAL_ARITH `&0 < l ==> --l <= l`] THEN
  SUBGOAL_THEN `l * (&2 * E / l) * exp(--(l / &4)) = &2 * E * exp(--(l / &4))`
  MP_TAC THENL
   [UNDISCH_TAC `&0 < l` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The equations on the cylinder.  The bound |v_tt + v_qq|^2 <= 2 B0^2 (c    *)
(* M)^2 |dv|^2 from Lap U = c sum_i B(q)(U_i, U_i) and the gradient bound;   *)
(* the conservation law (Hopf): int_q (|v_t|_H^2 - |v_q|_H^2) is constant in *)
(* t, H = G(p + c v), from the projected Euler-Lagrange equation.            *)
(* ------------------------------------------------------------------------- *)

let CMCY_W_BOUND = prove
 (`!S (G:real^K->real^K^K) s (U:real^2->real^K) p c y rho M B0 z.
     open s /\ smooth_map_on s U /\ &0 < rho /\ &0 <= c /\ &0 <= M /\ &0 <= B0 /\
     cmcy_phi y rho z IN s /\
     (!x. x IN s ==> p + c % U x IN S) /\
     (!x. x IN s
          ==> hmr_vlap U x =
              c % vsum(1..2) (\i. hmr_bq S G (p + c % U x) (partial_derivative i U x)
                                                          (partial_derivative i U x))) /\
     (!q a b. q IN S ==> norm(hmr_bq S G q a b) <= B0 * norm a * norm b) /\
     norm(cmcy_phi y rho z - y) * norm(partial_derivative 1 U (cmcy_phi y rho z)) <= M /\
     norm(cmcy_phi y rho z - y) * norm(partial_derivative 2 U (cmcy_phi y rho z)) <= M
     ==> norm(partial_derivative 1 (partial_derivative 1 (U o cmcy_phi y rho)) z +
              partial_derivative 2 (partial_derivative 2 (U o cmcy_phi y rho)) z) pow 2
         <= &2 * B0 pow 2 * (c * M) pow 2 *
            (norm(partial_derivative 1 (U o cmcy_phi y rho) z) pow 2 +
             norm(partial_derivative 2 (U o cmcy_phi y rho) z) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `y:real^2`; `rho:real`; `U:real^2->real^K`; `z:real^2`]
                CMCY_CYL_LAPLACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `y:real^2`; `rho:real`; `U:real^2->real^K`; `z:real^2`]
                CMCY_CYL_D1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`y:real^2`; `U:real^2->real^K`; `cmcy_phi y rho z`] CMCY_RD_AD_NORMS) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cmcy_phi y rho z` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `hmr_vlap:(real^2->real^K)->real^2->real^K`))
                                          (concl th))) THEN
  ASM_REWRITE_TAC[VSUM_2] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `p + c % (U:real^2->real^K)(cmcy_phi y rho z) IN S` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `x = cmcy_phi y rho z` THEN
  ABBREV_TAC `q = p + c % (U:real^2->real^K) x` THEN
  SUBGOAL_THEN `(q:real^K) IN S` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "x"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `r = norm(x - y:real^2)` THEN
  ABBREV_TAC `a1 = norm(partial_derivative 1 (U:real^2->real^K) x)` THEN
  ABBREV_TAC `a2 = norm(partial_derivative 2 (U:real^2->real^K) x)` THEN
  SUBGOAL_THEN `&0 <= r /\ &0 <= a1 /\ &0 <= a2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "a1"; "a2"] THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `gq = r pow 2 * (a1 pow 2 + a2 pow 2)` THEN
  SUBGOAL_THEN `&0 <= gq /\ gq <= &2 * M pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "gq" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `(r * a1) pow 2 <= M pow 2 /\ (r * a2) pow 2 <= M pow 2` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LE_MUL];
      REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(r pow 2 % c % (hmr_bq S G q (partial_derivative 1 (U:real^2->real^K) x)
                                    (partial_derivative 1 U x) +
                        hmr_bq S G q (partial_derivative 2 U x) (partial_derivative 2 U x)))
    <= c * B0 * gq` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_POW] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`] THEN
    EXPAND_TAC "gq" THEN
    SUBGOAL_THEN
     `norm(hmr_bq S G q (partial_derivative 1 (U:real^2->real^K) x) (partial_derivative 1 U x) +
           hmr_bq S G q (partial_derivative 2 U x) (partial_derivative 2 U x))
      <= B0 * (a1 pow 2 + a2 pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(hmr_bq S G q (partial_derivative 1 (U:real^2->real^K) x)
                                    (partial_derivative 1 U x)) +
                  norm(hmr_bq S G q (partial_derivative 2 U x) (partial_derivative 2 U x))` THEN
      REWRITE_TAC[NORM_TRIANGLE] THEN
      SUBGOAL_THEN
       `norm(hmr_bq S G q (partial_derivative 1 (U:real^2->real^K) x)
                          (partial_derivative 1 U x)) <= B0 * a1 * a1 /\
        norm(hmr_bq S G q (partial_derivative 2 (U:real^2->real^K) x)
                          (partial_derivative 2 U x)) <= B0 * a2 * a2`
      MP_TAC THENL
       [MAP_EVERY EXPAND_TAC ["a1"; "a2"] THEN CONJ_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_ABS] THEN
    SUBGOAL_THEN `abs r = r` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `r pow 2 * c * norm(hmr_bq S G q (partial_derivative 1 (U:real^2->real^K) x)
                                              (partial_derivative 1 U x) +
                                     hmr_bq S G q (partial_derivative 2 U x)
                                                  (partial_derivative 2 U x)) <=
                  r pow 2 * c * B0 * (a1 pow 2 + a2 pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c * B0 * gq) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `gq * gq <= gq * (&2 * M pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c * B0) pow 2` MP_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL) THEN
  REAL_ARITH_TAC);;

(* The derivative of a(z) . G(p + c v(z)) b(z).                              *)

let CMCY_HASD_GDOT = prove
 (`!(G:real^K->real^K^K) p c (v:real^2->real^K) (a:real^2->real^K) b z.
     v differentiable (at z) /\ a differentiable (at z) /\ b differentiable (at z) /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) differentiable (at (p + c % v z))
     ==> ((\z. lift(a z dot (G(p + c % v z) ** b z))) has_derivative
          (\w. lift(frechet_derivative a (at z) w dot (G(p + c % v z) ** b z) +
                    a z dot (matrify(frechet_derivative (vectorize o G) (at (p + c % v z))
                                       (c % frechet_derivative v (at z) w)) ** b z +
                             G(p + c % v z) ** frechet_derivative b (at z) w)))) (at z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\z. (G:real^K->real^K^K)(p + c % (v:real^2->real^K) z)`;
    `\w. frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o G)
           (at (p + c % (v:real^2->real^K) z)) (c % frechet_derivative v (at z) w)`;
    `a:real^2->real^K`; `frechet_derivative (a:real^2->real^K) (at z)`;
    `b:real^2->real^K`; `frechet_derivative (b:real^2->real^K) (at z)`; `z:real^2`]
   LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(vectorize:real^K^K->real^(K,K)finite_prod) o (\z. G(p + c % (v:real^2->real^K) z)) =
    (vectorize o G) o (\z. p + c % v z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o G)
           (at (p + c % (v:real^2->real^K) z)) (c % frechet_derivative v (at z) w)) =
    frechet_derivative (vectorize o G) (at (p + c % v z)) o
    (\w. c % frechet_derivative v (at z) w)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\z:real^2. p:real^K`; `\h:real^2. vec 0:real^K`;
                 `\z. c % (v:real^2->real^K) z`;
                 `\h. c % frechet_derivative (v:real^2->real^K) (at z) h`; `at (z:real^2)`]
                HAS_DERIVATIVE_ADD) THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[ETA_AX]);;

let CMCY_PD_GDOT = prove
 (`!(G:real^K->real^K^K) p c (v:real^2->real^K) (a:real^2->real^K) b z i.
     v differentiable (at z) /\ a differentiable (at z) /\ b differentiable (at z) /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) differentiable (at (p + c % v z))
     ==> (\z. lift(a z dot (G(p + c % v z) ** b z))) differentiable (at z) /\
         partial_derivative i (\z. lift(a z dot (G(p + c % v z) ** b z))) z =
         lift(partial_derivative i a z dot (G(p + c % v z) ** b z) +
              a z dot (mderiv G (p + c % v z) (c % partial_derivative i v z) ** b z +
                       G(p + c % v z) ** partial_derivative i b z))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMCY_HASD_GDOT) THEN CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE th]) THEN
    REWRITE_TAC[mderiv; partial_derivative]]);;

let CMCY_TAN_DOT = prove
 (`!S (G:real^K->real^K^K) d q u w.
     cm_target S G d /\ q IN S /\ hmr_tp S q ** u = u
     ==> u dot (G q ** (hmr_tp S q ** w)) = u dot (G q ** w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `(u:real^K) dot ((G:real^K->real^K^K) q ** ((mat 1 - hmr_tp S q) ** (w:real^K))) = &0`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) o
      check (fun th -> concl th = `hmr_tp S q ** (u:real^K) = u`)) THEN
    REWRITE_TAC[hmr_tp] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^K->real^K^K) q ** (w:real^K) =
                G q ** (hmr_tp S q ** w) + G q ** ((mat 1 - hmr_tp S q) ** w)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                MATRIX_VECTOR_MUL_LID] THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ASM_REWRITE_TAC[DOT_RADD; REAL_ADD_RID]]);;

(* The pointwise conservation law e_t + 2 m_theta = 0 at a point z of O.    *)

let CMCY_HOPF_PT = prove
 (`!S (G:real^K->real^K^K) d O (v:real^2->real^K) p c z.
     cm_target S G d /\ open O /\ smooth_map_on O v /\ z IN O /\ p + c % v z IN S /\
     hmr_tp S (p + c % v z) ** partial_derivative 1 v z = partial_derivative 1 v z /\
     hmr_tp S (p + c % v z) ** partial_derivative 2 v z = partial_derivative 2 v z /\
     hmr_tp S (p + c % v z) **
       ((partial_derivative 1 (partial_derivative 1 v) z +
         partial_derivative 2 (partial_derivative 2 v) z) +
        c % (christoffel G (p + c % v z) (partial_derivative 1 v z) (partial_derivative 1 v z) +
             christoffel G (p + c % v z) (partial_derivative 2 v z) (partial_derivative 2 v z))) =
     vec 0
     ==> partial_derivative 1
           (\z. lift(partial_derivative 1 v z dot (G(p + c % v z) ** partial_derivative 1 v z)) -
                lift(partial_derivative 2 v z dot (G(p + c % v z) ** partial_derivative 2 v z))) z +
         &2 % partial_derivative 2
                (\z. lift(partial_derivative 1 v z dot
                          (G(p + c % v z) ** partial_derivative 2 v z))) z =
         vec 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMR_METRIC_FIELD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `(v:real^2->real^K) differentiable (at z) /\
                partial_derivative 1 v differentiable (at z) /\
                partial_derivative 2 v differentiable (at z)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `O:real^2->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o G) differentiable
                (at (p + c % (v:real^2->real^K) z))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^K)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `p:real^K`; `c:real`; `v:real^2->real^K`;
                 `partial_derivative 1 (v:real^2->real^K)`;
                 `partial_derivative 1 (v:real^2->real^K)`; `z:real^2`; `1`] CMCY_PD_GDOT) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `p:real^K`; `c:real`; `v:real^2->real^K`;
                 `partial_derivative 2 (v:real^2->real^K)`;
                 `partial_derivative 2 (v:real^2->real^K)`; `z:real^2`; `1`] CMCY_PD_GDOT) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `p:real^K`; `c:real`; `v:real^2->real^K`;
                 `partial_derivative 1 (v:real^2->real^K)`;
                 `partial_derivative 2 (v:real^2->real^K)`; `z:real^2`; `2`] CMCY_PD_GDOT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_SUB] THEN
  SUBGOAL_THEN `partial_derivative 2 (partial_derivative 1 (v:real^2->real^K)) z =
                partial_derivative 1 (partial_derivative 2 v) z` SUBST1_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_SYM THEN EXISTS_TAC `O:real^2->bool` THEN
    ASM_REWRITE_TAC[DIMINDEX_2; ARITH] THEN ASM_MESON_TAC[smooth_map_on];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `p + c % (v:real^2->real^K) z`] LRG_MDERIV_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL] THEN
  (* the Euler-Lagrange equation against the tangent vector v_1 *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `p + c % (v:real^2->real^K) z`;
                 `partial_derivative 1 (v:real^2->real^K) z`;
                 `(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) z +
                   partial_derivative 2 (partial_derivative 2 v) z) +
                  c % (christoffel G (p + c % v z) (partial_derivative 1 v z)
                                                   (partial_derivative 1 v z) +
                       christoffel G (p + c % v z) (partial_derivative 2 v z)
                                                   (partial_derivative 2 v z))`]
                CMCY_TAN_DOT) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RADD; DOT_RMUL] THEN
  MP_TAC(ISPECL [`(:real^K)`; `G:real^K->real^K^K`; `p + c % (v:real^2->real^K) z`]
                LRG_CHRISTOFFEL_DOT) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`(:real^K)`; `G:real^K->real^K^K`; `p + c % (v:real^2->real^K) z`]
                LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[SPECL
    [`partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) z`;
     `partial_derivative 1 (v:real^2->real^K) z`] th]) THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[SPECL
    [`partial_derivative 1 (partial_derivative 2 (v:real^2->real^K)) z`;
     `partial_derivative 2 (v:real^2->real^K) z`] th]) THEN
  DISCH_TAC THEN
  REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_CMUL; GSYM LIFT_ADD; GSYM LIFT_NUM; LIFT_EQ] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `&0`)) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hopf constancy: a(t) = int_q (|v_t|_H^2 - |v_q|_H^2) is constant on [-2l, *)
(* 2l]; and the hypotheses of CMC_CYL_STATEMENT in cylinder form.            *)
(* ------------------------------------------------------------------------- *)

let CMCY_GDOT_SMOOTH = prove
 (`!O (G:real^K->real^K^K) p c (v:real^2->real^K) (a:real^2->real^K) b.
     open O /\ smooth_map_on O v /\ smooth_map_on O a /\ smooth_map_on O b /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G)
     ==> smooth_map_on O (\z. lift(a z dot (G(p + c % v z) ** b z)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`O:real^2->bool`; `\z. (G:real^K->real^K^K)(p + c % (v:real^2->real^K) z)`;
                 `b:real^2->real^K`] LRG_SMOOTH_MATVEC) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(vectorize:real^K^K->real^(K,K)finite_prod) o (\z. G(p + c % (v:real^2->real^K) z)) =
                (vectorize o G) o (\z. p + c % v z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^K)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[ETA_AX]);;

let CMCY_HOPF_CONST = prove
 (`!S (G:real^K->real^K^K) d O (v:real^2->real^K) p c l.
     cm_target S G d /\ open O /\ smooth_map_on O v /\ &0 <= l /\
     (!t q. --(&2 * l) <= t /\ t <= &2 * l ==> vector[t; q] IN O) /\
     (!t q. --(&2 * l) <= t /\ t <= &2 * l
            ==> p + c % v(vector[t; q]) IN S /\
                hmr_tp S (p + c % v(vector[t; q])) ** partial_derivative 1 v (vector[t; q]) =
                partial_derivative 1 v (vector[t; q]) /\
                hmr_tp S (p + c % v(vector[t; q])) ** partial_derivative 2 v (vector[t; q]) =
                partial_derivative 2 v (vector[t; q]) /\
                hmr_tp S (p + c % v(vector[t; q])) **
                  ((partial_derivative 1 (partial_derivative 1 v) (vector[t; q]) +
                    partial_derivative 2 (partial_derivative 2 v) (vector[t; q])) +
                   c % (christoffel G (p + c % v(vector[t; q]))
                          (partial_derivative 1 v (vector[t; q]))
                          (partial_derivative 1 v (vector[t; q])) +
                        christoffel G (p + c % v(vector[t; q]))
                          (partial_derivative 2 v (vector[t; q]))
                          (partial_derivative 2 v (vector[t; q])))) =
                vec 0) /\
     (!t. v(vector[t; &2 * pi]) = v(vector[t; &0]) /\
          partial_derivative 1 v (vector[t; &2 * pi]) = partial_derivative 1 v (vector[t; &0]) /\
          partial_derivative 2 v (vector[t; &2 * pi]) = partial_derivative 2 v (vector[t; &0]))
     ==> ?a. !t. --(&2 * l) <= t /\ t <= &2 * l
                 ==> drop(integral (interval[vec 0,lift(&2 * pi)])
                        (\q. lift(partial_derivative 1 v (vector[t; drop q]) dot
                                  (G(p + c % v(vector[t; drop q])) **
                                   partial_derivative 1 v (vector[t; drop q]))) -
                             lift(partial_derivative 2 v (vector[t; drop q]) dot
                                  (G(p + c % v(vector[t; drop q])) **
                                   partial_derivative 2 v (vector[t; drop q]))))) = a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `smooth_map_on O (partial_derivative 1 (v:real^2->real^K)) /\
                smooth_map_on O (partial_derivative 2 (v:real^2->real^K))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  ABBREV_TAC
   `ee = \z. lift(partial_derivative 1 (v:real^2->real^K) z dot
                  (G(p + c % v z) ** partial_derivative 1 v z)) -
             lift(partial_derivative 2 v z dot (G(p + c % v z) ** partial_derivative 2 v z))` THEN
  ABBREV_TAC
   `mm = \z. lift(partial_derivative 1 (v:real^2->real^K) z dot
                  (G(p + c % v z) ** partial_derivative 2 v z))` THEN
  SUBGOAL_THEN `smooth_map_on O (ee:real^2->real^1) /\ smooth_map_on O (mm:real^2->real^1)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ee"; "mm"] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC) THEN
    MATCH_MP_TAC CMCY_GDOT_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. drop(integral (interval[vec 0,lift(&2 * pi)])
                             (\q. (ee:real^2->real^1)(vector[t; drop q])))`;
                 `real_interval[--(&2 * l),&2 * l]`]
                HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`O:real^2->bool`; `ee:real^2->real^1`; `--(&2 * l)`; `&2 * l`]
                  CMCY_PARAM_DERIV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[] `x = y ==> (f has_real_derivative x) net
                                     ==> (f has_real_derivative y) net`) THEN
    (* int_q d_1 ee = -2 int_q d_2 mm = 0 *)
    SUBGOAL_THEN
     `!q. partial_derivative 1 (ee:real^2->real^1) (vector[t; drop q]) =
          --(&2) % partial_derivative 2 (mm:real^2->real^1) (vector[t; drop q])`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `O:real^2->bool`;
                     `v:real^2->real^K`; `p:real^K`; `c:real`; `vector[t; drop q]:real^2`]
                    CMCY_HOPF_PT) THEN
      MAP_EVERY EXPAND_TAC ["ee"; "mm"] THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`O:real^2->bool`; `mm:real^2->real^1`; `t:real`; `lift(&2 * pi)`]
                  CMCY_THETA_FTC) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LIFT_DROP; REAL_LE_MUL; REAL_POS; PI_POS_LE]; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `(mm:real^2->real^1)(vector[t; &2 * pi]) = mm(vector[t; &0])` SUBST1_TAC THENL
     [EXPAND_TAC "mm" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_SUB_REFL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\q. partial_derivative 2 (mm:real^2->real^1) (vector[t; drop q])`;
                   `--(&2)`; `interval[vec 0:real^1,lift(&2 * pi)]`] INTEGRAL_CMUL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[integrable_on]; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; DROP_VEC];
    REWRITE_TAC[] THEN EXPAND_TAC "ee" THEN REWRITE_TAC[]]);;

(* Periodicity in theta of v = U o Phi and of its partial derivatives.      *)

let CMCY_PERIODIC_PD = prove
 (`!(f:real^N->real^M) c.
     (!z. f(z + c) = f z) ==> !i z. partial_derivative i f (z + c) = partial_derivative i f z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative; frechet_derivative] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^M`; `f':real^N->real^M`; `c:real^N`; `z:real^N`]
                  HAS_DERIVATIVE_TRANSLATION) THEN
    ASM_REWRITE_TAC[ETA_AX];
    MP_TAC(ISPECL [`f:real^N->real^M`; `f':real^N->real^M`; `--c:real^N`; `z + c:real^N`]
                  HAS_DERIVATIVE_TRANSLATION) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(z + c) + --c:real^N = z`] THEN
    SUBGOAL_THEN `(\w. (f:real^N->real^M)(w + --c)) = f` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^N` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w + --c:real^N`) THEN
    REWRITE_TAC[VECTOR_ARITH `(w + --c) + c:real^N = w`] THEN SIMP_TAC[]]);;

let CMCY_PHI_SHIFT = prove
 (`!y rho z. cmcy_phi y rho (z + (&2 * pi) % basis 2) = cmcy_phi y rho z`,
  REWRITE_TAC[CMCY_PHI_CIRC; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; CMCY_BASIS2;
              REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID; wan_circ; SIN_PERIODIC;
              COS_PERIODIC]);;

let CMCY_V_PERIODIC = prove
 (`!y rho (U:real^2->real^K) t.
     (U o cmcy_phi y rho)(vector[t; &2 * pi]) = (U o cmcy_phi y rho)(vector[t; &0]) /\
     partial_derivative 1 (U o cmcy_phi y rho) (vector[t; &2 * pi]) =
     partial_derivative 1 (U o cmcy_phi y rho) (vector[t; &0]) /\
     partial_derivative 2 (U o cmcy_phi y rho) (vector[t; &2 * pi]) =
     partial_derivative 2 (U o cmcy_phi y rho) (vector[t; &0]) /\
     partial_derivative 1 (partial_derivative 1 (U o cmcy_phi y rho)) (vector[t; &2 * pi]) =
     partial_derivative 1 (partial_derivative 1 (U o cmcy_phi y rho)) (vector[t; &0])`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(vector[t; &2 * pi]:real^2) = vector[t; &0] + (&2 * pi) % basis 2`
  SUBST1_TAC THENL [REWRITE_TAC[CMCY_VEC2_LINES]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. ((U:real^2->real^K) o cmcy_phi y rho)(z + (&2 * pi) % basis 2) =
                    (U o cmcy_phi y rho) z` ASSUME_TAC THENL
   [REWRITE_TAC[o_THM; CMCY_PHI_SHIFT]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMCY_PERIODIC_PD) THEN
  SUBGOAL_THEN `!z. partial_derivative 1 ((U:real^2->real^K) o cmcy_phi y rho)
                      (z + (&2 * pi) % basis 2) =
                    partial_derivative 1 (U o cmcy_phi y rho) z` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMCY_PERIODIC_PD) THEN
  ASM_REWRITE_TAC[]);;

(* The hypotheses of CMC_CYL_STATEMENT give those of CMCY_HOPF_PT for       *)
(* v = U o Phi at points z with Phi z in s.                                  *)

let CMCY_V_HYPS = prove
 (`!S (G:real^K->real^K^K) d s (U:real^2->real^K) p c y rho z.
     cm_target S G d /\ open s /\ smooth_map_on s U /\ cmcy_phi y rho z IN s /\
     (!x. x IN s ==> p + c % U x IN S) /\
     (!x i. x IN s /\ 1 <= i /\ i <= 2
            ==> hmr_tp S (p + c % U x) ** partial_derivative i U x = partial_derivative i U x) /\
     (!x. x IN s
          ==> hmr_tp S (p + c % U x) **
              (hmr_vlap U x +
               c % vsum(1..2) (\i. christoffel G (p + c % U x) (partial_derivative i U x)
                                                               (partial_derivative i U x))) =
              vec 0)
     ==> p + c % (U o cmcy_phi y rho) z IN S /\
         hmr_tp S (p + c % (U o cmcy_phi y rho) z) ** partial_derivative 1 (U o cmcy_phi y rho) z =
         partial_derivative 1 (U o cmcy_phi y rho) z /\
         hmr_tp S (p + c % (U o cmcy_phi y rho) z) ** partial_derivative 2 (U o cmcy_phi y rho) z =
         partial_derivative 2 (U o cmcy_phi y rho) z /\
         hmr_tp S (p + c % (U o cmcy_phi y rho) z) **
           ((partial_derivative 1 (partial_derivative 1 (U o cmcy_phi y rho)) z +
             partial_derivative 2 (partial_derivative 2 (U o cmcy_phi y rho)) z) +
            c % (christoffel G (p + c % (U o cmcy_phi y rho) z)
                   (partial_derivative 1 (U o cmcy_phi y rho) z)
                   (partial_derivative 1 (U o cmcy_phi y rho) z) +
                 christoffel G (p + c % (U o cmcy_phi y rho) z)
                   (partial_derivative 2 (U o cmcy_phi y rho) z)
                   (partial_derivative 2 (U o cmcy_phi y rho) z))) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `y:real^2`; `rho:real`; `U:real^2->real^K`; `z:real^2`]
                CMCY_CYL_LAPLACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `y:real^2`; `rho:real`; `U:real^2->real^K`; `z:real^2`]
                CMCY_CYL_D1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(U:real^2->real^K) differentiable (at (cmcy_phi y rho z))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMR_METRIC_FIELD) THEN
  MP_TAC(ISPECL [`y:real^2`; `U:real^2->real^K`; `cmcy_phi y rho z`;
                 `christoffel G (p + c % (U:real^2->real^K)(cmcy_phi y rho z))`] CMCY_BIL_TRACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN
    EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[IN_UNIV];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[CMCY_RD_COORDS] THEN
  ABBREV_TAC `x = cmcy_phi y rho z` THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
  ASM_SIMP_TAC[ARITH; LE_REFL] THEN
  REWRITE_TAC[VECTOR_ARITH `r % a + c % r % b = r % (a + c % b):real^N`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `christoffel:(real^K->real^K^K)->real^K->real^K->real^K->real^K`))
        (concl th))) THEN
  ASM_REWRITE_TAC[VSUM_2; MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
  SIMP_TAC[VECTOR_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Ellipticity on the circle: with a = int (|v_t|_H^2 - |v_q|_H^2),          *)
(*   D(t) <= |a| / lam + (1 + Lam / lam) f(t)  and  |a| <= Lam D(t).        *)
(* ------------------------------------------------------------------------- *)

let CMCY_ELLIPTIC_ARITH = prove
 (`!lam Lam n1 n2 i1 i2.
     &0 < lam /\ lam * n1 <= i1 /\ i1 <= Lam * n1 /\ &0 <= n1 /\
     lam * n2 <= i2 /\ i2 <= Lam * n2 /\ &0 <= n2
     ==> n1 + n2 <= abs(i1 - i2) / lam + (&1 + Lam / lam) * n2 /\
         abs(i1 - i2) <= Lam * (n1 + n2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= lam * n1 /\ &0 <= lam * n2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `abs(i1 - i2) / lam + (&1 + Lam / lam) * n2 =
                  (abs(i1 - i2) + Lam * n2) / lam + n2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `n1 <= y ==> n1 + n2 <= y + n2:real`) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let CMCY_ELLIPTIC_BOUNDS = prove
 (`!(G:real^K->real^K^K) O (v:real^2->real^K) p c t lam Lam a.
     open O /\ smooth_map_on O v /\ (!q. vector[t; q] IN O) /\ &0 < lam /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
     (!z w. lam * norm w pow 2 <= w dot (G z ** w) /\ w dot (G z ** w) <= Lam * norm w pow 2) /\
     drop(integral (interval[vec 0,lift(&2 * pi)])
        (\q. lift(partial_derivative 1 v (vector[t; drop q]) dot
                  (G(p + c % v(vector[t; drop q])) ** partial_derivative 1 v (vector[t; drop q]))) -
             lift(partial_derivative 2 v (vector[t; drop q]) dot
                  (G(p + c % v(vector[t; drop q])) **
                   partial_derivative 2 v (vector[t; drop q]))))) = a
     ==> cmcy_dd v t <= abs a / lam + (&1 + Lam / lam) * cmcy_f v t /\
         abs a <= Lam * cmcy_dd v t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on O (partial_derivative 1 (v:real^2->real^K)) /\
                smooth_map_on O (partial_derivative 2 (v:real^2->real^K))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(h:real^2->real^1). smooth_map_on O h
        ==> (\q. h(vector[t; drop q])) integrable_on interval[vec 0,lift(&2 * pi)]`
  (LABEL_TAC "lint") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMCY_LINE_INT_SMOOTH THEN
    EXISTS_TAC `O:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. (\q. lift(partial_derivative i (v:real^2->real^K) (vector[t; drop q]) dot
                    (G(p + c % v(vector[t; drop q])) ** partial_derivative j v (vector[t; drop q]))))
          integrable_on interval[vec 0,lift(&2 * pi)] /\
          (\q. lift(norm(partial_derivative i (v:real^2->real^K) (vector[t; drop q])) pow 2))
          integrable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THENL
     [USE_THEN "lint" (MP_TAC o SPEC
       `\z. lift(partial_derivative i (v:real^2->real^K) z dot
                 (G(p + c % v z) ** partial_derivative j v z))`) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC CMCY_GDOT_SMOOTH THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
      USE_THEN "lint" (MP_TAC o SPEC
       `\z. lift(norm(partial_derivative i (v:real^2->real^K) z) pow 2)`) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_NORM_POW2_OPEN; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. lam * drop(integral (interval[vec 0,lift(&2 * pi)])
          (\q. lift(norm(partial_derivative i (v:real^2->real^K) (vector[t; drop q])) pow 2))) <=
        drop(integral (interval[vec 0,lift(&2 * pi)])
          (\q. lift(partial_derivative i v (vector[t; drop q]) dot
                    (G(p + c % v(vector[t; drop q])) ** partial_derivative i v (vector[t; drop q]))))) /\
        drop(integral (interval[vec 0,lift(&2 * pi)])
          (\q. lift(partial_derivative i v (vector[t; drop q]) dot
                    (G(p + c % v(vector[t; drop q])) ** partial_derivative i v (vector[t; drop q]))))) <=
        Lam * drop(integral (interval[vec 0,lift(&2 * pi)])
          (\q. lift(norm(partial_derivative i (v:real^2->real^K) (vector[t; drop q])) pow 2))) /\
        &0 <= drop(integral (interval[vec 0,lift(&2 * pi)])
          (\q. lift(norm(partial_derivative i (v:real^2->real^K) (vector[t; drop q])) pow 2)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM DROP_CMUL; GSYM INTEGRAL_CMUL] THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[INTEGRABLE_CMUL; DROP_CMUL; LIFT_DROP];
      ASM_SIMP_TAC[GSYM DROP_CMUL; GSYM INTEGRAL_CMUL] THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[INTEGRABLE_CMUL; DROP_CMUL; LIFT_DROP];
      MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `a = drop(integral (interval[vec 0,lift(&2 * pi)])
          (\q. lift(partial_derivative 1 (v:real^2->real^K) (vector[t; drop q]) dot
                    (G(p + c % v(vector[t; drop q])) ** partial_derivative 1 v (vector[t; drop q]))))) -
        drop(integral (interval[vec 0,lift(&2 * pi)])
          (\q. lift(partial_derivative 2 (v:real^2->real^K) (vector[t; drop q]) dot
                    (G(p + c % v(vector[t; drop q])) ** partial_derivative 2 v (vector[t; drop q])))))`
  SUBST1_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[GSYM DROP_SUB] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmcy_dd (v:real^2->real^K) t =
    drop(integral (interval[vec 0,lift(&2 * pi)])
          (\q. lift(norm(partial_derivative 1 (v:real^2->real^K) (vector[t; drop q])) pow 2))) +
    cmcy_f v t`
  SUBST1_TAC THENL
   [REWRITE_TAC[cmcy_dd; cmcy_f; LIFT_ADD; GSYM DROP_ADD] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_ADD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cmcy_f] THEN MATCH_MP_TAC CMCY_ELLIPTIC_ARITH THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The cylinder estimate: continuity and derivatives of the circle           *)
(* integrals, f'' >= f / 4 - A on the strip, and the ODE comparison.         *)
(* ------------------------------------------------------------------------- *)

let CMCY_DERIV_INTERIOR = prove
 (`!f f' c d t.
     (f has_real_derivative f') (atreal t within real_interval[c,d]) /\
     t IN real_interval(c,d)
     ==> (f has_real_derivative f') (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f has_real_derivative f') (atreal t within real_interval(c,d))` MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[c,d]` THEN
    ASM_REWRITE_TAC[REAL_INTERVAL_OPEN_SUBSET_CLOSED];
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN; REAL_OPEN_REAL_INTERVAL]]);;

let CMCY_PARAM_CONT = prove
 (`!O (h:real^2->real^1) c d.
     open O /\ smooth_map_on O h /\ c <= d /\
     (!s q. c <= s /\ s <= d ==> vector[s; q] IN O)
     ==> (\s. drop(integral (interval[vec 0,lift(&2 * pi)]) (\q. h(vector[s; drop q]))))
         real_continuous_on real_interval[c,d]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL THEN
  EXISTS_TAC `drop(integral (interval[vec 0,lift(&2 * pi)])
                (\q. partial_derivative 1 (h:real^2->real^1) (vector[x; drop q])))` THEN
  MP_TAC(ISPECL [`O:real^2->bool`; `h:real^2->real^1`; `c:real`; `d:real`]
    CMCY_PARAM_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let CMCY_PARAM_DERIV_OPEN = prove
 (`!O (h:real^2->real^1) c d.
     open O /\ smooth_map_on O h /\ c <= d /\
     (!s q. c <= s /\ s <= d ==> vector[s; q] IN O)
     ==> !t. t IN real_interval(c,d)
             ==> ((\s. drop(integral (interval[vec 0,lift(&2 * pi)])
                                     (\q. h(vector[s; drop q]))))
                  has_real_derivative
                  drop(integral (interval[vec 0,lift(&2 * pi)])
                         (\q. partial_derivative 1 h (vector[t; drop q]))))
                 (atreal t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMCY_DERIV_INTERIOR THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`O:real^2->bool`; `h:real^2->real^1`; `c:real`; `d:real`]
    CMCY_PARAM_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `t IN real_interval(c,d)` THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let CMCY_F_LE_DD = prove
 (`!O (v:real^2->real^K) t.
     open O /\ smooth_map_on O v /\ (!q. vector[t; q] IN O)
     ==> &0 <= cmcy_f v t /\ cmcy_f v t <= cmcy_dd v t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. (\q. lift(norm(partial_derivative i (v:real^2->real^K) (vector[t; drop q])) pow 2))
        integrable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`O:real^2->bool`;
                   `\z. lift(norm(partial_derivative i (v:real^2->real^K) z) pow 2)`;
                   `t:real`; `vec 0:real^1`; `lift(&2 * pi)`] CMCY_LINE_INT_SMOOTH) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_NORM_POW2_OPEN; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[cmcy_f; cmcy_dd] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_ADDL; REAL_LE_POW_2] THEN
    REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]]);;

let CMCY_W_INT = prove
 (`!O (v:real^2->real^K) t K0.
     open O /\ smooth_map_on O v /\ (!q. vector[t; q] IN O) /\
     (!q. norm(partial_derivative 1 (partial_derivative 1 v) (vector[t; q]) +
               partial_derivative 2 (partial_derivative 2 v) (vector[t; q])) pow 2
          <= K0 * (norm(partial_derivative 1 v (vector[t; q])) pow 2 +
                   norm(partial_derivative 2 v (vector[t; q])) pow 2))
     ==> drop(integral (interval[vec 0,lift(&2 * pi)])
                (\q. lift(norm(partial_derivative 1 (partial_derivative 1 v) (vector[t; drop q]) +
                               partial_derivative 2 (partial_derivative 2 v) (vector[t; drop q]))
                          pow 2)))
         <= K0 * cmcy_dd v t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!(h:real^2->real^1). smooth_map_on O h
        ==> (\q. h(vector[t; drop q])) integrable_on interval[vec 0,lift(&2 * pi)]`
  (LABEL_TAC "lint") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMCY_LINE_INT_SMOOTH THEN
    EXISTS_TAC `O:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\q. lift(norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K))
                     (vector[t; drop q]) +
                   partial_derivative 2 (partial_derivative 2 v) (vector[t; drop q])) pow 2))
    integrable_on interval[vec 0,lift(&2 * pi)] /\
    (\q. lift(norm(partial_derivative 1 (v:real^2->real^K) (vector[t; drop q])) pow 2 +
              norm(partial_derivative 2 v (vector[t; drop q])) pow 2))
    integrable_on interval[vec 0,lift(&2 * pi)]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "lint" (MP_TAC o SPEC
       `\z. lift(norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) z +
                      partial_derivative 2 (partial_derivative 2 v) z) pow 2)`) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_ADD_OPEN; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
      USE_THEN "lint" (MP_TAC o SPEC
       `\z. lift(norm(partial_derivative 1 (v:real^2->real^K) z) pow 2 +
                 norm(partial_derivative 2 v z) pow 2)`) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_NORM_POW2_OPEN; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX]];
    ALL_TAC] THEN
  REWRITE_TAC[cmcy_dd] THEN
  ASM_SIMP_TAC[GSYM DROP_CMUL; GSYM INTEGRAL_CMUL] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; DROP_CMUL; LIFT_DROP]);;

let CMCY_F2_ARITH = prove
 (`!f w dd f2 K0 A0 R.
     &0 <= K0 /\ &0 <= f /\ K0 * R <= &3 / &4 /\
     f - w <= f2 /\ w <= K0 * dd /\ dd <= A0 + R * f
     ==> f / &4 - K0 * A0 <= f2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `K0 * dd <= K0 * (A0 + R * f)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(K0 * R) * f <= (&3 / &4) * f` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMCY_CYL_CORE = prove
 (`!O (v:real^2->real^K) l K0 lam Lam a.
     open O /\ smooth_map_on O v /\ &0 < l /\ &0 < lam /\ &0 <= K0 /\
     K0 * (&1 + Lam / lam) <= &3 / &4 /\
     (!t q. --(&2 * l) <= t /\ t <= &2 * l ==> vector[t; q] IN O) /\
     (!t. v(vector[t; &2 * pi]) = v(vector[t; &0]) /\
          partial_derivative 2 v (vector[t; &2 * pi]) = partial_derivative 2 v (vector[t; &0]) /\
          partial_derivative 1 (partial_derivative 1 v) (vector[t; &2 * pi]) =
          partial_derivative 1 (partial_derivative 1 v) (vector[t; &0])) /\
     (!t q. --(&2 * l) <= t /\ t <= &2 * l
            ==> norm(partial_derivative 1 (partial_derivative 1 v) (vector[t; q]) +
                     partial_derivative 2 (partial_derivative 2 v) (vector[t; q])) pow 2
                <= K0 * (norm(partial_derivative 1 v (vector[t; q])) pow 2 +
                         norm(partial_derivative 2 v (vector[t; q])) pow 2)) /\
     (!t. --(&2 * l) <= t /\ t <= &2 * l
          ==> cmcy_dd v t <= abs a / lam + (&1 + Lam / lam) * cmcy_f v t /\
              abs a <= Lam * cmcy_dd v t)
     ==> real_integral (real_interval[--l,l]) (cmcy_f v) <=
         &8 * l * (K0 * abs a / lam) +
         &8 * exp(--(l / &4)) *
         real_integral (real_interval[--(&2 * l),&2 * l]) (cmcy_dd v) /\
         &4 * l * abs a <= Lam * real_integral (real_interval[--(&2 * l),&2 * l]) (cmcy_dd v) /\
         &0 <= real_integral (real_interval[--(&2 * l),&2 * l]) (cmcy_dd v) /\
         cmcy_f v real_integrable_on real_interval[--l,l] /\
         cmcy_dd v real_integrable_on real_interval[--(&2 * l),&2 * l]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `--(&2 * l) <= &2 * l` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. --(&2 * l) <= t /\ t <= &2 * l
        ==> cmcy_dd (v:real^2->real^K) t <= abs a / lam + (&1 + Lam / lam) * cmcy_f v t /\
            abs a <= Lam * cmcy_dd v t`
  (LABEL_TAC "ell") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on O (\z. lift(norm(partial_derivative 2 (v:real^2->real^K) z) pow 2)) /\
    smooth_map_on O (\z. lift(norm(partial_derivative 1 (v:real^2->real^K) z) pow 2 +
                              norm(partial_derivative 2 v z) pow 2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_NORM_POW2_OPEN; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
      REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_NORM_POW2_OPEN; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on O
      (partial_derivative 1 (\z. lift(norm(partial_derivative 2 (v:real^2->real^K) z) pow 2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cmcy_f (v:real^2->real^K) real_continuous_on real_interval[--(&2 * l),&2 * l] /\
    cmcy_dd (v:real^2->real^K) real_continuous_on real_interval[--(&2 * l),&2 * l]`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `cmcy_f (v:real^2->real^K) =
      (\s. drop(integral (interval[vec 0,lift(&2 * pi)])
                  (\q. (\z. lift(norm(partial_derivative 2 v z) pow 2)) (vector[s; drop q])))) /\
      cmcy_dd (v:real^2->real^K) =
      (\s. drop(integral (interval[vec 0,lift(&2 * pi)])
                  (\q. (\z. lift(norm(partial_derivative 1 v z) pow 2 +
                                 norm(partial_derivative 2 v z) pow 2)) (vector[s; drop q]))))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[FUN_EQ_THM; cmcy_f; cmcy_dd]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC CMCY_PARAM_CONT THEN EXISTS_TAC `O:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[--(&2 * l),&2 * l]
        ==> &0 <= cmcy_f (v:real^2->real^K) t /\ cmcy_f v t <= cmcy_dd v t`
  (LABEL_TAC "fdd") THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`O:real^2->bool`; `v:real^2->real^K`; `t:real`] CMCY_F_LE_DD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval(--(&2 * l),&2 * l)
        ==> (cmcy_f (v:real^2->real^K) has_real_derivative
             drop(integral (interval[vec 0,lift(&2 * pi)])
                    (\q. partial_derivative 1 (\z. lift(norm(partial_derivative 2 v z) pow 2))
                           (vector[t; drop q])))) (atreal t) /\
            ((\s. drop(integral (interval[vec 0,lift(&2 * pi)])
                    (\q. partial_derivative 1 (\z. lift(norm(partial_derivative 2 v z) pow 2))
                           (vector[s; drop q])))) has_real_derivative
             drop(integral (interval[vec 0,lift(&2 * pi)])
                    (\q. partial_derivative 1
                           (partial_derivative 1 (\z. lift(norm(partial_derivative 2 v z) pow 2)))
                           (vector[t; drop q])))) (atreal t)`
  (LABEL_TAC "deriv") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `cmcy_f (v:real^2->real^K) =
        (\s. drop(integral (interval[vec 0,lift(&2 * pi)])
                  (\q. (\z. lift(norm(partial_derivative 2 v z) pow 2)) (vector[s; drop q]))))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; cmcy_f]; ALL_TAC] THEN
      MP_TAC(ISPECL [`O:real^2->bool`;
                     `\z. lift(norm(partial_derivative 2 (v:real^2->real^K) z) pow 2)`;
                     `--(&2 * l)`; `&2 * l`] CMCY_PARAM_DERIV_OPEN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`O:real^2->bool`;
                     `partial_derivative 1
                        (\z. lift(norm(partial_derivative 2 (v:real^2->real^K) z) pow 2))`;
                     `--(&2 * l)`; `&2 * l`] CMCY_PARAM_DERIV_OPEN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval(--(&2 * l),&2 * l)
        ==> cmcy_f (v:real^2->real^K) t / &4 - K0 * abs a / lam <=
            drop(integral (interval[vec 0,lift(&2 * pi)])
                   (\q. partial_derivative 1
                          (partial_derivative 1 (\z. lift(norm(partial_derivative 2 v z) pow 2)))
                          (vector[t; drop q])))`
  (LABEL_TAC "f2") THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `--(&2 * l) <= t /\ t <= &2 * l` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `!q. vector[t; q] IN (O:real^2->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`O:real^2->bool`; `v:real^2->real^K`; `t:real`] CMCY_F_LE_DD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`O:real^2->bool`; `v:real^2->real^K`; `t:real`] CMCY_F2_LOWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`O:real^2->bool`; `v:real^2->real^K`; `t:real`; `K0:real`] CMCY_W_INT) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    USE_THEN "ell" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `--(&2 * l) <= t`) (ASSUME `t <= &2 * l`))) THEN
    STRIP_TAC THEN
    MATCH_MP_TAC CMCY_F2_ARITH THEN
    EXISTS_TAC
     `drop(integral (interval[vec 0,lift(&2 * pi)])
        (\q. lift(norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K))
                         (vector[t; drop q]) +
                       partial_derivative 2 (partial_derivative 2 v) (vector[t; drop q]))
                  pow 2)))` THEN
    EXISTS_TAC `cmcy_dd (v:real^2->real^K) t` THEN
    EXISTS_TAC `&1 + Lam / lam` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
    [`cmcy_f (v:real^2->real^K)`;
     `\t. drop(integral (interval[vec 0,lift(&2 * pi)])
                (\q. partial_derivative 1
                       (\z. lift(norm(partial_derivative 2 (v:real^2->real^K) z) pow 2))
                       (vector[t; drop q])))`;
     `\t. drop(integral (interval[vec 0,lift(&2 * pi)])
                (\q. partial_derivative 1
                       (partial_derivative 1
                          (\z. lift(norm(partial_derivative 2 (v:real^2->real^K) z) pow 2)))
                       (vector[t; drop q])))`;
     `K0 * abs a / lam`; `l:real`] CMCY_ODE_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_ABS_POS; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "deriv" (MP_TAC o C MATCH_MP
        (ASSUME `t IN real_interval(--(&2 * l),&2 * l)`)) THEN
      USE_THEN "f2" (MP_TAC o C MATCH_MP
        (ASSUME `t IN real_interval(--(&2 * l),&2 * l)`)) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      USE_THEN "fdd" (MP_TAC o C MATCH_MP
        (ASSUME `t IN real_interval[--(&2 * l),&2 * l]`)) THEN REAL_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `cmcy_f (v:real^2->real^K) real_integrable_on real_interval[--(&2 * l),&2 * l] /\
    cmcy_dd (v:real^2->real^K) real_integrable_on real_interval[--(&2 * l),&2 * l] /\
    cmcy_f (v:real^2->real^K) real_integrable_on real_interval[--l,l]`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[--(&2 * l),&2 * l]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&8 * l * (K0 * abs a / lam) +
      &8 * exp(--(l / &4)) *
      real_integral (real_interval[--(&2 * l),&2 * l]) (cmcy_f (v:real^2->real^K))` THEN
    ASM_REWRITE_TAC[REAL_LE_LADD] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "fdd" (MP_TAC o C MATCH_MP
      (ASSUME `t IN real_interval[--(&2 * l),&2 * l]`)) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[--(&2 * l),&2 * l]) (\t. abs a)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL] THEN
      MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_INTEGRABLE_CONST];
        MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[ETA_AX];
        REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
        USE_THEN "ell" (MP_TAC o C MATCH_MP
          (ASSUME `--(&2 * l) <= x /\ x <= &2 * l`)) THEN
        REAL_ARITH_TAC]];
    MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "fdd" (MP_TAC o C MATCH_MP
      (ASSUME `t IN real_interval[--(&2 * l),&2 * l]`)) THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Assembly: the constants l and g, the instance estimate, and the headline  *)
(* theorem CMC_CYL.                                                          *)
(* ------------------------------------------------------------------------- *)

let CMCY_CONST_CHOICE = prove
 (`!B lam Lam delta.
     &0 <= B /\ &0 < lam /\ lam <= Lam /\ &0 < delta
     ==> ?l g. &1 <= l /\ &0 < g /\ exp(--(l / &4)) <= delta / &16 /\
               (&2 * B pow 2 * g pow 2) * (&1 + Lam / lam) <= &3 / &4 /\
               &2 * (&2 * B pow 2 * g pow 2) * Lam / lam <= delta / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Lam / lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (B + &1) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `P = (B + &1) pow 2 * (&1 + Lam / lam)` THEN
  ABBREV_TAC `Q = (B + &1) pow 2 * Lam / lam` THEN
  SUBGOAL_THEN `&0 < P /\ &0 < Q` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `B pow 2 <= (B + &1) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &3 / (&8 * P) /\ &0 < delta / (&8 * Q)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `max (&1) (&4 * log(&16 / delta))` THEN
  EXISTS_TAC `min (&1) (min (&3 / (&8 * P)) (delta / (&8 * Q)))` THEN
  ABBREV_TAC `l = max (&1) (&4 * log(&16 / delta))` THEN
  ABBREV_TAC `g = min (&1) (min (&3 / (&8 * P)) (delta / (&8 * Q)))` THEN
  SUBGOAL_THEN `&1 <= l /\ log(&16 / delta) <= l / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < g /\ g <= &1 /\ g <= &3 / (&8 * P) /\ g <= delta / (&8 * Q)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `g pow 2 <= g` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * B pow 2 * g pow 2 <= &2 * (B + &1) pow 2 * g` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `&16 / delta <= exp(l / &4)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log(&16 / delta))` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[EXP_LOG; REAL_LT_DIV; REAL_ARITH `&0 < &16`; REAL_LE_REFL];
        ASM_REWRITE_TAC[REAL_EXP_MONO_LE]];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_NEG] THEN
    SUBGOAL_THEN `delta / &16 = inv(&16 / delta)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INV_DIV]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &16`];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * (B + &1) pow 2 * g) * (&1 + Lam / lam)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(&2 * (B + &1) pow 2 * g) * (&1 + Lam / lam) = (&2 * P) * g`
      SUBST1_TAC THENL [EXPAND_TAC "P" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&3 / &4 = (&2 * P) * (&3 / (&8 * P))` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < P` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (&2 * (B + &1) pow 2 * g) * Lam / lam` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&2 * (&2 * (B + &1) pow 2 * g) * Lam / lam = (&4 * Q) * g`
      SUBST1_TAC THENL [EXPAND_TAC "Q" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `delta / &2 = (&4 * Q) * (delta / (&8 * Q))` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]);;

let CMCY_FINAL_ARITH = prove
 (`!X E l K0 a lam Lam delta.
     &0 < lam /\ &0 <= K0 /\ &0 <= E /\
     X <= &8 * l * (K0 * abs a / lam) + &8 * exp(--(l / &4)) * E /\
     &4 * l * abs a <= Lam * E /\
     &2 * K0 * Lam / lam <= delta / &2 /\ exp(--(l / &4)) <= delta / &16
     ==> X <= delta * E`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&8 * l * (K0 * abs a / lam) = (&2 * K0 / lam) * (&4 * l * abs a)`
  SUBST_ALL_TAC THENL
   [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * K0 / lam) * (&4 * l * abs a) <= (&2 * K0 / lam) * (Lam * E)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * K0 / lam) * (Lam * E) = (&2 * K0 * Lam / lam) * E`
  SUBST_ALL_TAC THENL
   [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * K0 * Lam / lam) * E <= (delta / &2) * E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&8 * exp(--(l / &4)) * E <= &8 * (delta / &16) * E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMCY_WB_ARITH = prove
 (`!B0 c M g w X.
     &0 <= c /\ &0 <= M /\ c * M <= g /\ &0 <= X /\
     w <= &2 * B0 pow 2 * (c * M) pow 2 * X
     ==> w <= (&2 * B0 pow 2 * g pow 2) * X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c * M) pow 2 <= g pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * B0 pow 2) * (c * M) pow 2 * X <= (&2 * B0 pow 2) * g pow 2 * X`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    UNDISCH_TAC `w <= &2 * B0 pow 2 * (c * M) pow 2 * X` THEN REAL_ARITH_TAC]);;

let CMCY_INSTANCE = prove
 (`!S (G:real^K->real^K^K) d B0 lam Lam l g delta s (U:real^2->real^K) p c y rho M.
     cm_target S G d /\ &0 <= B0 /\
     (!q a b. q IN S ==> norm(hmr_bq S G q a b) <= B0 * norm a * norm b) /\
     &0 < lam /\
     (!z w. lam * norm w pow 2 <= w dot (G z ** w) /\
            w dot (G z ** w) <= Lam * norm w pow 2) /\
     &1 <= l /\ exp(--(l / &4)) <= delta / &16 /\
     (&2 * B0 pow 2 * g pow 2) * (&1 + Lam / lam) <= &3 / &4 /\
     &2 * (&2 * B0 pow 2 * g pow 2) * Lam / lam <= delta / &2 /\
     open s /\ &0 < rho /\ &0 <= c /\ &0 <= M /\ c * M <= g /\
     {x:real^2 | rho * exp(--(&2 * l)) <= norm(x - y) /\
                 norm(x - y) <= rho * exp(&2 * l)} SUBSET s /\
     smooth_map_on s U /\
     (!x. x IN s ==> p + c % U x IN S) /\
     (!x i. x IN s /\ 1 <= i /\ i <= 2
            ==> hmr_tp S (p + c % U x) ** partial_derivative i U x =
                partial_derivative i U x) /\
     (!x. x IN s
          ==> hmr_tp S (p + c % U x) **
              (hmr_vlap U x +
               c % vsum(1..2)
                     (\i. christoffel G (p + c % U x)
                            (partial_derivative i U x)
                            (partial_derivative i U x))) = vec 0) /\
     (!x. x IN s
          ==> hmr_vlap U x =
              c % vsum(1..2)
                    (\i. hmr_bq S G (p + c % U x)
                           (partial_derivative i U x)
                           (partial_derivative i U x))) /\
     (!x. rho * exp(--(&2 * l)) <= norm(x - y) /\
          norm(x - y) <= rho * exp(&2 * l)
          ==> norm(x - y) * norm(partial_derivative 1 U x) <= M /\
              norm(x - y) * norm(partial_derivative 2 U x) <= M)
     ==> drop(integral (cmc_ann y (rho * exp(--l)) (rho * exp l))
                (\x. lift(norm(cmc_angd y x (partial_derivative 1 U x)
                                           (partial_derivative 2 U x)) pow 2)))
         <= delta *
            drop(integral (cmc_ann y (rho * exp(--(&2 * l))) (rho * exp(&2 * l)))
                   (\x. lift(norm(partial_derivative 1 U x) pow 2 +
                             norm(partial_derivative 2 U x) pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `&0 < l /\ &0 <= l` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * B0 pow 2 * g pow 2` ASSUME_TAC THENL
   [SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^2 | cmcy_phi y rho z IN s}` ASSUME_TAC THENL
   [MATCH_MP_TAC CMCY_CYL_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on {z:real^2 | cmcy_phi y rho z IN s} ((U:real^2->real^K) o cmcy_phi y rho)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMCY_CYL_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t q. --(&2 * l) <= t /\ t <= &2 * l
          ==> cmcy_phi y rho (vector[t; q]) IN
              {x:real^2 | rho * exp(--(&2 * l)) <= norm(x - y) /\
                          norm(x - y) <= rho * exp(&2 * l)}`
  (LABEL_TAC "ann") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`y:real^2`; `rho:real`; `--(&2 * l)`; `&2 * l`; `vector[t; q]:real^2`]
      CMCY_CANN_PHI) THEN
    ASM_SIMP_TAC[VECTOR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t q. --(&2 * l) <= t /\ t <= &2 * l
          ==> vector[t; q] IN {z:real^2 | cmcy_phi y rho z IN s}`
  (LABEL_TAC "strip") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    USE_THEN "ann" (MP_TAC o SPEC `q:real` o C MATCH_MP
      (CONJ (ASSUME `--(&2 * l) <= t`) (ASSUME `t <= &2 * l`))) THEN
    UNDISCH_TAC
     `{x:real^2 | rho * exp(--(&2 * l)) <= norm(x - y) /\
                  norm(x - y) <= rho * exp(&2 * l)} SUBSET s` THEN
    REWRITE_TAC[SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t q. --(&2 * l) <= t /\ t <= &2 * l
          ==> norm(cmcy_phi y rho (vector[t; q]) - y) *
              norm(partial_derivative 1 (U:real^2->real^K) (cmcy_phi y rho (vector[t; q])))
              <= M /\
              norm(cmcy_phi y rho (vector[t; q]) - y) *
              norm(partial_derivative 2 (U:real^2->real^K) (cmcy_phi y rho (vector[t; q])))
              <= M`
  (LABEL_TAC "mb") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    USE_THEN "ann" (MP_TAC o SPEC `q:real` o C MATCH_MP
      (ASSUME `--(&2 * l) <= t /\ t <= &2 * l`)) THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `{z:real^2 | cmcy_phi y rho z IN s}`; `(U:real^2->real^K) o cmcy_phi y rho`;
                 `p:real^K`; `c:real`; `l:real`] CMCY_HOPF_CONST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CMCY_V_PERIODIC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CMCY_V_HYPS THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `s:real^2->bool`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "strip" (MP_TAC o C MATCH_MP
      (ASSUME `--(&2 * l) <= t /\ t <= &2 * l`)) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(ACCEPT_TAC o SPEC `q:real`);
    DISCH_THEN(X_CHOOSE_THEN `a:real` (LABEL_TAC "hopf"))] THEN
  SUBGOAL_THEN
   `!t. --(&2 * l) <= t /\ t <= &2 * l
        ==> cmcy_dd ((U:real^2->real^K) o cmcy_phi y rho) t <=
            abs a / lam + (&1 + Lam / lam) * cmcy_f (U o cmcy_phi y rho) t /\
            abs a <= Lam * cmcy_dd (U o cmcy_phi y rho) t`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMCY_ELLIPTIC_BOUNDS THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `{z:real^2 | cmcy_phi y rho z IN s}`;
                          `p:real^K`; `c:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "strip" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "hopf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t q. --(&2 * l) <= t /\ t <= &2 * l
          ==> norm(partial_derivative 1 (partial_derivative 1 ((U:real^2->real^K) o cmcy_phi y rho))
                     (vector[t; q]) +
                   partial_derivative 2 (partial_derivative 2 (U o cmcy_phi y rho))
                     (vector[t; q])) pow 2
              <= (&2 * B0 pow 2 * g pow 2) *
                 (norm(partial_derivative 1 (U o cmcy_phi y rho) (vector[t; q])) pow 2 +
                  norm(partial_derivative 2 (U o cmcy_phi y rho) (vector[t; q])) pow 2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMCY_WB_ARITH THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `M:real`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC CMCY_W_BOUND THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `s:real^2->bool`;
                            `p:real^K`] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "mb" (MP_TAC o SPEC `q:real` o C MATCH_MP
        (CONJ (ASSUME `--(&2 * l) <= t`) (ASSUME `t <= &2 * l`))) THEN
      USE_THEN "strip" (MP_TAC o SPEC `q:real` o C MATCH_MP
        (CONJ (ASSUME `--(&2 * l) <= t`) (ASSUME `t <= &2 * l`))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{z:real^2 | cmcy_phi y rho z IN s}`; `(U:real^2->real^K) o cmcy_phi y rho`;
                 `l:real`; `&2 * B0 pow 2 * g pow 2`; `lam:real`; `Lam:real`; `a:real`]
    CMCY_CYL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CMCY_V_PERIODIC]; STRIP_TAC] THEN
  SUBGOAL_THEN `!f:real->real. lift o f o drop = (\t. lift(f(drop t)))` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (cmc_ann y (rho * exp(--l)) (rho * exp l))
           (\x. lift(norm(cmc_angd y x (partial_derivative 1 U x)
                                      (partial_derivative 2 U x)) pow 2))) =
    real_integral (real_interval[--l,l]) (cmcy_f ((U:real^2->real^K) o cmcy_phi y rho)) /\
    drop(integral (cmc_ann y (rho * exp(--(&2 * l))) (rho * exp(&2 * l)))
           (\x. lift(norm(partial_derivative 1 U x) pow 2 +
                     norm(partial_derivative 2 U x) pow 2))) =
    real_integral (real_interval[--(&2 * l),&2 * l])
      (cmcy_dd ((U:real^2->real^K) o cmcy_phi y rho))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL; IMAGE_LIFT_REAL_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMCY_ANG_TO_CYL THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `{x:real^2 | rho * exp(--(&2 * l)) <= norm(x - y) /\
                              norm(x - y) <= rho * exp(&2 * l)}` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      SUBGOAL_THEN `rho * exp(--(&2 * l)) <= rho * exp(--l) /\
                    rho * exp l <= rho * exp(&2 * l)` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC CMCY_GRAD_TO_CYL THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CMCY_FINAL_ARITH THEN
  MAP_EVERY EXISTS_TAC [`l:real`; `&2 * B0 pow 2 * g pow 2`; `a:real`; `lam:real`; `Lam:real`] THEN
  ASM_REWRITE_TAC[]);;

let CMC_CYL = prove
 (`!kk:K->bool. CMC_CYL_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CMC_CYL_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  X_GEN_TAC `delta:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_BQ_FAMILY) THEN
  MP_TAC(ISPECL [`cm_tube (S:real^K->bool) d`; `S:real^K->bool`;
                 `hmr_bq (S:real^K->bool) G`] HMR_BILFAM_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B0:real` (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?lam Lam. &0 < lam /\ lam <= Lam /\
              !z w. lam * norm w pow 2 <= w dot ((G:real^K->real^K^K) z ** w) /\
                    w dot (G z ** w) <= Lam * norm w pow 2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `cm_target (S:real^K->bool) G d` THEN REWRITE_TAC[cm_target] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`lam:real`; `Lam:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`B0:real`; `lam:real`; `Lam:real`; `delta:real`] CMCY_CONST_CHOICE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` (X_CHOOSE_THEN `g:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`l:real`; `g:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `U:real^2->real^K`; `p:real^K`; `c:real`;
                       `y:real^2`; `rho:real`; `M:real`] THEN
  STRIP_TAC THEN MATCH_MP_TAC CMCY_INSTANCE THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `B0:real`;
                        `lam:real`; `Lam:real`; `g:real`; `s:real^2->bool`; `p:real^K`;
                        `c:real`; `M:real`] THEN
  ASM_REWRITE_TAC[]);;

