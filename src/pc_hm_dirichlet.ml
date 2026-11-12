(* ========================================================================= *)
(* Unit pc_hm_dirichlet: the chain unit for CM_CHAIN_HM_DIRICHLET_STATEMENT  *)
(* (Colding-Minicozzi 2008, Cor 3.3-3.4, stated in pc_cm_stmts).  On top of  *)
(* pc_hm_dexist (existence, uniqueness, harmonic representative) and         *)
(* pc_hm_dbdry (continuity up to the boundary, the quantitative boundary     *)
(* estimate): the competitor Pi o (w2 + (u1 - u2)) through a global          *)
(* extension Pg of the closest-point map (statement HMD_PG_STATEMENT, proved *)
(* as HMR_PI_GLOBAL in pc_hm_reg_cov), the energy estimate (3.6), the        *)
(* continuity of u |-> H(u) in C^0 /\ W^{1,2}, and the headline              *)
(* CM_CHAIN_HM_DIRICHLET.  HMD_REPLACEMENT_REDUCED discharges the hypotheses *)
(* WAN_RELLICH0, WAN_GDIR_LSC and CM_EPS_REG, which are theorems of other    *)
(* units.                                                                    *)
(* ========================================================================= *)

needs "src/pc_hm_dbdry.ml";;
needs "src/pc_hm_reg_cov.ml";;
needs "src/pc_wan_sob2r.ml";;
needs "src/pc_hm_reg_eps.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The global extension Pg of the closest-point map (data hmd_pgdata;        *)
(* HMD_PG_STATEMENT is the statement of HMR_PI_GLOBAL) and its first         *)
(* consequences: Pg is the identity on S, maps the d1-tube into S, is        *)
(* Lipschitz, C^1 with bounded derivative, and its derivative on S is the    *)
(* tangential projection P = jacobian(closest_point S).  The projection is   *)
(* G-orthogonal (cm_target's P G (I - P) = 0), so it does not increase the   *)
(* G-length.                                                                 *)
(* ------------------------------------------------------------------------- *)

let hmd_pgdata = new_definition
 `hmd_pgdata (S:real^K->bool) d d1 B (Pg:real^K->real^K) <=>
    &0 < d1 /\ d1 < d /\ &0 <= B /\ smooth_map_on (:real^K) Pg /\
    (!z. z IN cm_tube S d1 ==> Pg z = closest_point S z) /\
    (!y v. norm(frechet_derivative Pg (at y) v) <= B * norm v) /\
    (!y z v. norm(frechet_derivative Pg (at y) v - frechet_derivative Pg (at z) v)
             <= B * norm(y - z) * norm v)`;;

let HMD_PG_STATEMENT = new_definition
 `HMD_PG_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
      cm_target S G d ==> ?d1 B (Pg:real^K->real^K). hmd_pgdata S d d1 B Pg`;;

let HMD_PG_TUBE = prove
 (`!(S:real^K->bool) d1 y Z. y IN S /\ norm Z < d1 ==> y + Z IN cm_tube S d1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN
  EXISTS_TAC `y:real^K` THEN ASM_REWRITE_TAC[dist; VECTOR_ARITH `(y + z) - y:real^N = z`]);;

let HMD_PG_HASDER = prove
 (`!(S:real^K->bool) d d1 B (Pg:real^K->real^K).
     hmd_pgdata S d d1 B Pg
     ==> !y. (Pg has_derivative frechet_derivative Pg (at y)) (at y)`,
  REWRITE_TAC[hmd_pgdata] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HMD_SMOOTH_HAS_DERIVATIVE THEN EXISTS_TAC `(:real^K)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let HMD_PG_ONORM = prove
 (`!(S:real^K->bool) d d1 B (Pg:real^K->real^K).
     hmd_pgdata S d d1 B Pg ==> !y. onorm(frechet_derivative Pg (at y)) <= B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `y:real^K` o MATCH_MP HMD_PG_HASDER) THEN
  SUBGOAL_THEN `linear(frechet_derivative (Pg:real^K->real^K) (at y))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
    ASM_MESON_TAC[];
    ASM_SIMP_TAC[ONORM_LE_EQ] THEN ASM_MESON_TAC[hmd_pgdata]]);;

let HMD_PG_LIP = prove
 (`!(S:real^K->bool) d d1 B (Pg:real^K->real^K).
     hmd_pgdata S d d1 B Pg ==> !y z. norm(Pg y - Pg z) <= B * norm(y - z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Pg:real^K->real^K`; `\y. frechet_derivative (Pg:real^K->real^K) (at y)`;
                 `(:real^K)`; `B:real`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP HMD_PG_HASDER);
      FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP HMD_PG_ONORM)];
    SIMP_TAC[]]);;

let HMD_PG_FACTS = prove
 (`!S (G:real^K->real^K^K) d d1 B (Pg:real^K->real^K).
     cm_target S G d /\ hmd_pgdata S d d1 B Pg
     ==> (!y. y IN S ==> Pg y = y) /\
         (!y Z. y IN S /\ norm Z < d1 ==> Pg(y + Z) IN S) /\
         (!y z. norm(Pg y - Pg z) <= B * norm(y - z)) /\
         (!y. (Pg has_derivative frechet_derivative Pg (at y)) (at y)) /\
         (!y v. y IN S
                ==> frechet_derivative Pg (at y) v = jacobian (closest_point S) (at y) ** v) /\
         continuously_differentiable 1 (:real^K) Pg /\
         (!y. onorm(frechet_derivative Pg (at y)) <= B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMD_PG_HASDER) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMD_PG_ONORM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMD_PG_LIP) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `hmd_pgdata S d d1 B (Pg:real^K->real^K)` THEN REWRITE_TAC[hmd_pgdata] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `!y. y IN S ==> (Pg:real^K->real^K) y = y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^K) IN cm_tube S d1` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `d1:real`; `y:real^K`; `vec 0:real^K`] HMD_PG_TUBE) THEN
      ASM_REWRITE_TAC[NORM_0; VECTOR_ADD_RID];
      ASM_SIMP_TAC[CLOSEST_POINT_SELF]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(Pg:real^K->real^K)(y + Z) = closest_point S (y + Z)` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC HMD_PG_TUBE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[smooth_map_on]] THEN
  MAP_EVERY X_GEN_TAC [`y:real^K`; `v:real^K`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^K) IN cm_tube S d` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(closest_point (S:real^K->bool) has_derivative
     frechet_derivative (closest_point S) (at y)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_SMOOTH_HAS_DERIVATIVE THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (Pg:real^K->real^K) (at y) =
    frechet_derivative (closest_point (S:real^K->bool)) (at y)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`closest_point (S:real^K->bool)`; `d1:real`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x':real^K` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `closest_point:(real^K->bool)->real^K->real^K`)) (concl th) &&
      can (find_term ((=) `d1:real`)) (concl th))) THEN
    SUBGOAL_THEN `x' = y + (x' - y:real^K)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HMD_PG_TUBE THEN ASM_REWRITE_TAC[GSYM dist];
    ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN
  SUBGOAL_THEN `linear(frechet_derivative (closest_point (S:real^K->bool)) (at y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
    ASM_MESON_TAC[];
    ASM_SIMP_TAC[MATRIX_WORKS]]);;

(* The tangential projection does not increase the G-length on S.            *)

let HMD_GPROJ = prove
 (`!S (G:real^K->real^K^K) d y V.
     cm_target S G d /\ y IN S
     ==> (jacobian (closest_point S) (at y) ** V) dot
         (G y ** (jacobian (closest_point S) (at y) ** V)) <= V dot (G y ** V)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  ABBREV_TAC `P = jacobian (closest_point S) (at (y:real^K))` THEN
  SUBGOAL_THEN `(V:real^K) = (P:real^K^K) ** V + (mat 1 - P) ** V` SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^K^K) ** ((P:real^K^K) ** (V:real^K) + (mat 1 - P) ** V) = P ** V`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_ASSOC;
                MATRIX_SUB_LDISTRIB; MATRIX_MUL_RID] THEN
    SUBGOAL_THEN `(P:real^K^K) ** P = P` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_SUB_REFL; MATRIX_VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_LADD; DOT_RADD] THEN
  SUBGOAL_THEN `((P:real^K^K) ** (V:real^K)) dot ((G:real^K->real^K^K) y ** ((mat 1 - P) ** V)) = &0 /\
                ((mat 1 - P) ** V) dot ((G:real^K->real^K^K) y ** ((P:real^K^K) ** V)) = &0`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [EXPAND_TAC "P" THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`(G:real^K->real^K^K) y`; `(mat 1 - (P:real^K^K)) ** (V:real^K)`;
                     `(P:real^K^K) ** (V:real^K)`] HMC_SYM_DOT) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; REAL_ADD_LID] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a <= a + b`) THEN ASM_REWRITE_TAC[]);;

(* Perturbation of a quadratic form.                                          *)

let HMD_QF_PERTURB = prove
 (`!(M:real^K^K) A R L.
     (!xi. norm(M ** xi) <= L * norm xi)
     ==> (A + R) dot (M ** (A + R))
         <= A dot (M ** A) + &2 * L * norm A * norm R + L * norm R pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!X Y:real^K. abs(X dot ((M:real^K^K) ** Y)) <= L * norm X * norm Y`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(X:real^K) * norm((M:real^K^K) ** Y)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `L * x * y:real = x * (L * y)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_LADD; DOT_RADD] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`A:real^K`; `R:real^K`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`R:real^K`; `A:real^K`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`R:real^K`; `R:real^K`]) THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The pointwise energy density of the competitor Pg(w + z): with X a        *)
(* partial of w (values in S), Y one of z and |z| <= d1 / 2,                  *)
(*   |DPg(w + z)(X + Y)|^2_{G(Pg(w+z))} <= |X|^2_{G(w)}                      *)
(*                    + KK (|z| |X|^2 + |X| |Y| + |Y|^2).                    *)
(* The real-arithmetic core is HMD_PW_REAL.                                  *)
(* ------------------------------------------------------------------------- *)

let HMD_PW_REAL = prove
 (`!t0 a1 a0 q0 a x rr yv zz Lam1 C3 B d1.
     &0 <= a /\ a <= x /\ &0 <= rr /\ rr <= B * zz * x + B * yv /\
     &0 <= zz /\ zz <= d1 / &2 /\ &0 <= yv /\
     &0 <= Lam1 /\ &0 <= C3 /\ &0 <= B /\ &0 <= d1 /\
     t0 <= a1 + &2 * Lam1 * a * rr + Lam1 * rr pow 2 /\
     a1 <= a0 + C3 * (B * zz) * a pow 2 /\ a0 <= q0
     ==> t0 <= q0 + (C3 * B + &4 * Lam1 * B + Lam1 * B pow 2 * d1 + &2 * Lam1 * B pow 2) *
                    (zz * x pow 2 + x * yv + yv pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C3 * (B * zz) * a pow 2 <= C3 * (B * zz) * x pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_MUL];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * Lam1 * a * rr <= &2 * Lam1 * x * (B * zz * x + B * yv)` ASSUME_TAC THENL
   [SUBGOAL_THEN `a * rr <= x * (B * zz * x + B * yv)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * Lam1) * (a * rr) <= (&2 * Lam1) * (x * (B * zz * x + B * yv))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Lam1 * rr pow 2 <= Lam1 * (B * zz * x + B * yv) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Lam1 * (B * zz * x + B * yv) pow 2 <=
    Lam1 * (&2 * (B * zz * x) pow 2 + &2 * (B * yv) pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `B * zz * x - B * yv` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Lam1 * &2 * (B * zz * x) pow 2 <= Lam1 * B pow 2 * d1 * (zz * x pow 2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `Lam1 * &2 * (B * zz * x) pow 2 = (Lam1 * B pow 2 * x pow 2) * (&2 * zz * zz) /\
                  Lam1 * B pow 2 * d1 * (zz * x pow 2) = (Lam1 * B pow 2 * x pow 2) * (d1 * zz)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `KK = C3 * B + &4 * Lam1 * B + Lam1 * B pow 2 * d1 + &2 * Lam1 * B pow 2` THEN
  SUBGOAL_THEN `&0 <= C3 * B /\ &0 <= Lam1 * B /\ &0 <= Lam1 * B pow 2 * d1 /\
                &0 <= Lam1 * B pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= zz * x pow 2 /\ &0 <= x * yv /\ &0 <= yv pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (KK - (C3 * B + &2 * Lam1 * B + Lam1 * B pow 2 * d1)) * (zz * x pow 2) /\
    &0 <= (KK - &2 * Lam1 * B) * (x * yv) /\
    &0 <= (KK - &2 * Lam1 * B pow 2) * yv pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "KK" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `t0 <= a1 + &2 * Lam1 * a * rr + Lam1 * rr pow 2` THEN
  UNDISCH_TAC `a1 <= a0 + C3 * (B * zz) * a pow 2` THEN UNDISCH_TAC `a0 <= q0` THEN
  UNDISCH_TAC `C3 * B + &4 * Lam1 * B + Lam1 * B pow 2 * d1 + &2 * Lam1 * B pow 2 = KK` THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The pointwise estimate for the competitor density.                        *)
(* ------------------------------------------------------------------------- *)

let HMD_PW_COMPOSITE = prove
 (`!S (G:real^K->real^K^K) d d1 B (Pg:real^K->real^K).
     cm_target S G d /\ hmd_pgdata S d d1 B Pg
     ==> ?KK. &0 <= KK /\
         !y Z X Y. y IN S /\ norm Z <= d1 / &2
           ==> (frechet_derivative Pg (at (y + Z)) (X + Y)) dot
               (G(Pg(y + Z)) ** frechet_derivative Pg (at (y + Z)) (X + Y))
               <= X dot (G y ** X) +
                  KK * (norm Z * norm X pow 2 + norm X * norm Y + norm Y pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`] HMD_PG_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_CONSTS) THEN
  UNDISCH_TAC `hmd_pgdata S d d1 B (Pg:real^K->real^K)` THEN
  REWRITE_TAC[hmd_pgdata] THEN STRIP_TAC THEN
  EXISTS_TAC `C3 * B + &4 * Lam1 * B + Lam1 * B pow 2 * d1 + &2 * Lam1 * B pow 2` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^K`; `Z:real^K`; `X:real^K`; `Y:real^K`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(Z:real^K) < d1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(Pg:real^K->real^K)(y + Z) IN S` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Q = frechet_derivative (Pg:real^K->real^K) (at (y + Z))` THEN
  ABBREV_TAC `A = jacobian (closest_point S) (at (y:real^K)) ** (X:real^K)` THEN
  SUBGOAL_THEN `(Q:real^K->real^K) (X + Y) = A + (Q (X + Y) - A)` SUBST1_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `linear(Q:real^K->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(A:real^K) <= norm(X:real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC HMC_PROJ_NORM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((Q:real^K->real^K) (X + Y) - A) <=
                B * norm(Z:real^K) * norm(X:real^K) + B * norm(Y:real^K)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_ADD] THEN
    SUBGOAL_THEN `(A:real^K) = frechet_derivative (Pg:real^K->real^K) (at y) X` SUBST1_TAC THENL
     [EXPAND_TAC "A" THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a - c:real^K) <= u /\ norm(b:real^K) <= v ==> norm((a + b) - c) <= u + v`) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y + Z:real^K`; `y:real^K`; `X:real^K`] o
        check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `( - ):real^K->real^K->real^K`)) (concl th) &&
          length(fst(strip_forall(concl th))) = 3)) THEN
      REWRITE_TAC[VECTOR_ARITH `(y + z) - y:real^K = z`; REAL_MUL_ASSOC];
      EXPAND_TAC "Q" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((Pg:real^K->real^K)(y + Z) - y) <= B * norm(Z:real^K)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(Pg:real^K->real^K) y = y` (fun th -> GEN_REWRITE_TAC
      (LAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y + Z:real^K`; `y:real^K`] o
      check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 2 &&
        can (find_term ((=) `B:real`)) (concl th) &&
        not(can (find_term ((=) `frechet_derivative:(real^K->real^K)->(real^K)net->real^K->real^K`))
                (concl th)))) THEN
    REWRITE_TAC[VECTOR_ARITH `(y + z) - y:real^K = z`];
    ALL_TAC] THEN
  MATCH_MP_TAC HMD_PW_REAL THEN
  MAP_EVERY EXISTS_TAC
   [`(A:real^K) dot ((G:real^K->real^K^K)((Pg:real^K->real^K)(y + Z)) ** A)`;
    `(A:real^K) dot ((G:real^K->real^K^K) y ** A)`;
    `norm(A:real^K)`; `norm((Q:real^K->real^K) (X + Y) - A)`] THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC HMD_QF_PERTURB THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `(A:real^K) dot ((G:real^K->real^K^K)((Pg:real^K->real^K)(y + Z)) ** A) =
      A dot (G y ** A) + A dot ((G(Pg(y + Z)) - G y) ** A)`
    SUBST1_TAC THENL
     [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RSUB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> a + x <= a + y`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(A:real^K) *
                norm(((G:real^K->real^K^K)((Pg:real^K->real^K)(y + Z)) - G y) ** A)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(A:real^K) *
                (C3 * norm((Pg:real^K->real^K)(y + Z) - y) * norm(A:real^K))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `C3:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= C3 * norm(A:real^K) * norm(A:real^K)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE]; ALL_TAC] THEN
    MP_TAC(MATCH_MP REAL_LE_LMUL (CONJ
      (ASSUME `&0 <= C3 * norm(A:real^K) * norm(A:real^K)`)
      (ASSUME `norm((Pg:real^K->real^K)(y + Z) - y) <= B * norm(Z:real^K)`))) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    EXPAND_TAC "A" THEN MATCH_MP_TAC HMD_GPROJ THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The energy of the competitor Pg(w + z) (CM (3.8) in the G form):          *)
(*   gdir(Pg(w + z)) <= gdir(w) + KK (delta dir(w)                            *)
(*                       + sqrt(dir w) sqrt(dir z) + dir(z))                   *)
(* for w in W^{1,2} with values in S a.e. and |z| <= delta <= d1 / 2, via    *)
(* the chain rule WAN_CHAIN_W12, the pointwise estimate HMD_PW_COMPOSITE,    *)
(* Hoelder and the two-term Cauchy-Schwarz inequality.                       *)
(* ------------------------------------------------------------------------- *)

let HMD_CS2 = prove
 (`!a1 a2 b1 b2. &0 <= a1 /\ &0 <= a2 /\ &0 <= b1 /\ &0 <= b2
                 ==> a1 * b1 + a2 * b2 <= sqrt(a1 pow 2 + a2 pow 2) * sqrt(b1 pow 2 + b2 pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SQRT_MUL] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  MP_TAC(SPEC `a1 * b2 - a2 * b1` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let HMD_INTEGRAL_LIN4 = prove
 (`!s (q:real^2->real) a b c k dl.
     (\x. lift(q x)) integrable_on s /\ (\x. lift(a x)) integrable_on s /\
     (\x. lift(b x)) integrable_on s /\ (\x. lift(c x)) integrable_on s
     ==> drop(integral s (\x. lift(q x) + k % (dl % lift(a x) + lift(b x) + lift(c x)))) =
         drop(integral s (\x. lift(q x))) +
         k * (dl * drop(integral s (\x. lift(a x))) + drop(integral s (\x. lift(b x))) +
              drop(integral s (\x. lift(c x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((b:real^2->real) x) + lift(c x)) integrable_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. dl % lift((a:real^2->real) x)) integrable_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. dl % lift((a:real^2->real) x) + lift(b x) + lift(c x)) integrable_on s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. k % (dl % lift((a:real^2->real) x) + lift(b x) + lift(c x)))
                integrable_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; DROP_ADD; DROP_CMUL]);;

(* One partial: the a.e. pointwise bound integrated.                         *)

let HMD_COMPETITOR_PARTIAL = prove
 (`!S (G:real^K->real^K^K) d d1 B (Pg:real^K->real^K) KK s (w:real^2->real^K) z
    delta ZZ i.
     cm_target S G d /\ hmd_pgdata S d d1 B Pg /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
     &0 <= KK /\
     (!y Z X Y. y IN S /\ norm Z <= d1 / &2
        ==> (frechet_derivative Pg (at (y + Z)) (X + Y)) dot
            (G(Pg(y + Z)) ** frechet_derivative Pg (at (y + Z)) (X + Y))
            <= X dot (G y ** X) +
               KK * (norm Z * norm X pow 2 + norm X * norm Y + norm Y pow 2)) /\
     open s /\ bounded s /\ wan_w12 s w /\ wan_w12 s z /\
     negligible ZZ /\ (!x. x IN s DIFF ZZ ==> w x IN S) /\
     (!x. x IN s ==> norm(z x) <= delta) /\ delta <= d1 / &2 /\ 1 <= i /\ i <= 2
     ==> wan_w12 s (\x. Pg(w x + z x)) /\
         drop(integral s (\x. lift(wan_wd s i (\x. Pg(w x + z x)) x dot
                                   (G(Pg(w x + z x)) ** wan_wd s i (\x. Pg(w x + z x)) x))))
         <= drop(integral s (\x. lift(wan_wd s i w x dot (G(w x) ** wan_wd s i w x)))) +
            KK * (delta * drop(integral s (\x. lift(norm(wan_wd s i w x) pow 2))) +
                  drop(integral s (\x. lift(norm(wan_wd s i w x) * norm(wan_wd s i z x)))) +
                  drop(integral s (\x. lift(norm(wan_wd s i z x) pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`] HMD_PG_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  SUBGOAL_THEN `!z xi. abs(xi dot ((G:real^K->real^K^K) z ** xi)) <= Lam * norm xi pow 2`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`zz:real^K`; `xi:real^K`] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPECL [`zz:real^K`; `xi:real^K`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `lam:real`)) (concl th))) THEN
    SUBGOAL_THEN `&0 <= lam * norm(xi:real^K) pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `w:real^2->real^K`; `z:real^2->real^K`] WAN_W12_ADD_WD) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
  UNDISCH_TAC `WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K)` THEN
  REWRITE_TAC[WAN_CHAIN_W12_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^2->bool`; `\x. (w:real^2->real^K) x + z x`;
                             `Pg:real^K->real^K`]) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN ANTS_TAC THENL
   [EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the a.e. identities for the weak partials *)
  SUBGOAL_THEN
   `negligible {x | x IN s /\
       ~(wan_wd s i (\x. (Pg:real^K->real^K)(w x + z x)) x =
         frechet_derivative Pg (at (w x + z x))
           (wan_wd s i (\x. (w:real^2->real^K) x + z x) x))}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `\x. (Pg:real^K->real^K)((w:real^2->real^K) x + (z:real^2->real^K) x)`;
                   `\x. frechet_derivative (Pg:real^K->real^K) (at (w x + z x))
                          (wan_wd s i (\x. (w:real^2->real^K) x + z x) x)`]
                  WAN_WD_UNIQUE) THEN
    ASM_SIMP_TAC[DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `negligible {x | x IN s /\
       ~(wan_wd s i (\x. (w:real^2->real^K) x + z x) x =
         wan_wd s i w x + wan_wd s i z x)}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `\x. (w:real^2->real^K) x + z x`;
                   `\x. wan_wd s i (w:real^2->real^K) x + wan_wd s i z x`]
                  WAN_WD_UNIQUE) THEN
    ASM_SIMP_TAC[DIMINDEX_2] THEN ANTS_TAC THENL
     [MATCH_MP_TAC WAN_W12_ADD THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* integrability *)
  SUBGOAL_THEN
   `(\x. lift(wan_wd s i (w:real^2->real^K) x dot
              ((G:real^K->real^K^K)(w x) ** wan_wd s i w x)))
    integrable_on s /\
    (\x. lift(wan_wd s i (\x. (Pg:real^K->real^K)(w x + z x)) x dot
              ((G:real^K->real^K^K)(Pg(w x + z x)) **
               wan_wd s i (\x. Pg(w x + z x)) x))) integrable_on s /\
    (\x. lift(norm(wan_wd s i (w:real^2->real^K) x) pow 2)) integrable_on s /\
    (\x. lift(norm(wan_wd s i (z:real^2->real^K) x) pow 2)) integrable_on s /\
    (\x. lift(norm(wan_wd s i (w:real^2->real^K) x) * norm(wan_wd s i z x))) integrable_on s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HMD_GDIR_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[DIMINDEX_2];
      MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`;
                     `\x. (Pg:real^K->real^K)((w:real^2->real^K) x + (z:real^2->real^K) x)`; `Lam:real`; `i:num`]
                    HMD_GDIR_INTEGRABLE) THEN
      ASM_REWRITE_TAC[DIMINDEX_2];
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2; ETA_AX];
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2; ETA_AX];
      MP_TAC(ISPECL [`s:real^2->bool`; `&2`; `&2`; `wan_wd s i (w:real^2->real^K)`;
                     `wan_wd s i (z:real^2->real^K)`] HOELDER_INEQUALITY_FULL) THEN
      ANTS_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  (* the integral comparison *)
  ABBREV_TAC
   `NN = ZZ UNION
         {x | x IN s /\
              ~(wan_wd s i (\x. (Pg:real^K->real^K)(w x + z x)) x =
                frechet_derivative Pg (at (w x + z x))
                  (wan_wd s i (\x. (w:real^2->real^K) x + z x) x))} UNION
         {x | x IN s /\
              ~(wan_wd s i (\x. (w:real^2->real^K) x + z x) x =
                wan_wd s i w x + wan_wd s i z x)}` THEN
  SUBGOAL_THEN `negligible(NN:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "NN" THEN ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ]; ALL_TAC] THEN
  ABBREV_TAC
   `gg = \x. lift(wan_wd s i w x dot ((G:real^K->real^K^K)(w x) ** wan_wd s i w x)) +
             KK % (delta % lift(norm(wan_wd s i (w:real^2->real^K) x) pow 2) +
                   lift(norm(wan_wd s i w x) * norm(wan_wd s i (z:real^2->real^K) x)) +
                   lift(norm(wan_wd s i z x) pow 2))` THEN
  SUBGOAL_THEN `(gg:real^2->real^1) integrable_on s` ASSUME_TAC THENL
   [EXPAND_TAC "gg" THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s DIFF NN
        ==> drop(lift(wan_wd s i (\x. (Pg:real^K->real^K)(w x + z x)) x dot
                      ((G:real^K->real^K^K)(Pg(w x + z x)) **
                       wan_wd s i (\x. Pg(w x + z x)) x)))
            <= drop((gg:real^2->real^1) x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `~(x IN ZZ) /\
      wan_wd s i (\x. (Pg:real^K->real^K)((w:real^2->real^K) x + (z:real^2->real^K) x)) x =
      frechet_derivative Pg (at (w x + z x)) (wan_wd s i (\x. w x + z x) x) /\
      wan_wd s i (\x. (w:real^2->real^K) x + z x) x = wan_wd s i w x + wan_wd s i z x`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((x:real^2) IN NN)` THEN EXPAND_TAC "NN" THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "gg" THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `wan_wd s i w x dot ((G:real^K->real^K^K)(w x) ** wan_wd s i w x) +
      KK * (norm((z:real^2->real^K) x) * norm(wan_wd s i (w:real^2->real^K) x) pow 2 +
            norm(wan_wd s i w x) * norm(wan_wd s i z x) + norm(wan_wd s i z x) pow 2)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `KK:real`)) (concl th))) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `delta:real` THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a + b <= a + c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `drop(integral s (gg:real^2->real^1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN EXISTS_TAC `NN:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `gg:real^2->real^1`)) THEN
  MP_TAC(ISPECL
   [`s:real^2->bool`;
    `\x. wan_wd s i (w:real^2->real^K) x dot ((G:real^K->real^K^K)(w x) ** wan_wd s i w x)`;
    `\x. norm(wan_wd s i (w:real^2->real^K) x) pow 2`;
    `\x. norm(wan_wd s i (w:real^2->real^K) x) * norm(wan_wd s i (z:real^2->real^K) x)`;
    `\x. norm(wan_wd s i (z:real^2->real^K) x) pow 2`; `KK:real`; `delta:real`]
   HMD_INTEGRAL_LIN4) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Summing over the two partials: the competitor energy bound.               *)
(* ------------------------------------------------------------------------- *)

let HMD_COMPETITOR_ENERGY = prove
 (`!S (G:real^K->real^K^K) d d1 B (Pg:real^K->real^K) KK s (w:real^2->real^K) z delta ZZ.
     cm_target S G d /\ hmd_pgdata S d d1 B Pg /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
     &0 <= KK /\
     (!y Z X Y. y IN S /\ norm Z <= d1 / &2
        ==> (frechet_derivative Pg (at (y + Z)) (X + Y)) dot
            (G(Pg(y + Z)) ** frechet_derivative Pg (at (y + Z)) (X + Y))
            <= X dot (G y ** X) +
               KK * (norm Z * norm X pow 2 + norm X * norm Y + norm Y pow 2)) /\
     open s /\ bounded s /\ wan_w12 s w /\ wan_w12 s z /\
     negligible ZZ /\ (!x. x IN s DIFF ZZ ==> w x IN S) /\
     (!x. x IN s ==> norm(z x) <= delta) /\ delta <= d1 / &2
     ==> wan_w12 s (\x. Pg(w x + z x)) /\
         wan_gdir s G (\x. Pg(w x + z x)) <=
         wan_gdir s G w +
         KK * (delta * wan_dir s w + sqrt(wan_dir s w) * sqrt(wan_dir s z) + wan_dir s z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`; `KK:real`; `s:real^2->bool`; `w:real^2->real^K`;
                 `z:real^2->real^K`; `delta:real`; `ZZ:real^2->bool`]
                HMD_COMPETITOR_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `1`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
  REWRITE_TAC[ARITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  (* Hoelder for the mixed terms *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> drop(integral s (\x. lift(norm(wan_wd s i (w:real^2->real^K) x) *
                                      norm(wan_wd s i (z:real^2->real^K) x))))
            <= lnorm s (&2) (wan_wd s i w) * lnorm s (&2) (wan_wd s i z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HOELDER_INEQUALITY THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(u:real^2->real^K) i. wan_w12 s u /\ 1 <= i /\ i <= 2
        ==> drop(integral s (\x. lift(norm(wan_wd s i u x) pow 2))) =
            lnorm s (&2) (wan_wd s i u) pow 2 /\
            &0 <= lnorm s (&2) (wan_wd s i u)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_SOB_LNORM2_SQ;
      MATCH_MP_TAC LNORM_POS_LE] THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_dir s (w:real^2->real^K) =
    lnorm s (&2) (wan_wd s 1 w) pow 2 + lnorm s (&2) (wan_wd s 2 w) pow 2 /\
    wan_dir s (z:real^2->real^K) =
    lnorm s (&2) (wan_wd s 1 z) pow 2 + lnorm s (&2) (wan_wd s 2 z) pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_dir; DIMINDEX_2; SUM_2] THEN ASM_SIMP_TAC[ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral s (\x. lift(norm(wan_wd s 1 (w:real^2->real^K) x) *
                              norm(wan_wd s 1 (z:real^2->real^K) x)))) +
    drop(integral s (\x. lift(norm(wan_wd s 2 w x) * norm(wan_wd s 2 z x))))
    <= sqrt(wan_dir s w) * sqrt(wan_dir s z)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lnorm s (&2) (wan_wd s 1 (w:real^2->real^K)) *
                lnorm s (&2) (wan_wd s 1 (z:real^2->real^K)) +
                lnorm s (&2) (wan_wd s 2 w) * lnorm s (&2) (wan_wd s 2 z)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `( * ):real->real->real`)) (concl th) &&
        can (find_term ((=) `lnorm:(real^2->bool)->real->(real^2->real^K)->real`)) (concl th) &&
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
      ARITH_TAC;
      MATCH_MP_TAC HMD_CS2 THEN ASM_MESON_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 2 <= 2`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `KK * (drop(integral s (\x. lift(norm(wan_wd s 1 (w:real^2->real^K) x) *
                                    norm(wan_wd s 1 (z:real^2->real^K) x)))) +
          drop(integral s (\x. lift(norm(wan_wd s 2 w x) * norm(wan_wd s 2 z x))))) <=
    KK * (sqrt(wan_dir s w) * sqrt(wan_dir s z))`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`sqrt(wan_dir s (w:real^2->real^K)) * sqrt(wan_dir s (z:real^2->real^K))`,
           `mm:real`) THEN
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[wan_gdir; wan_dir; DIMINDEX_2; SUM_2] THEN
  UNDISCH_TAC
   `KK * (drop(integral s (\x. lift(norm(wan_wd s 1 (w:real^2->real^K) x) *
                                    norm(wan_wd s 1 (z:real^2->real^K) x)))) +
          drop(integral s (\x. lift(norm(wan_wd s 2 w x) * norm(wan_wd s 2 z x))))) <=
    KK * mm` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_forall(concl th)) &&
    can (find_term ((=) `KK:real`)) (concl th) &&
    can (find_term ((=) `G:real^K->real^K^K`)) (concl th)))) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The context hmd_ctx (the hypotheses used, for one target and one          *)
(* energy threshold e) and the solution of the Dirichlet problem: for u in  *)
(* C^0 /\ W^{1,2}(cball, S) of energy <= e there is a unique (a.e.) energy  *)
(* minimizer w with the boundary values of u; it is harmonic inside,        *)
(* continuous on the closed disc and equal to u on the circle (CM Cor 3.4,   *)
(* first sentence).  Any continuous such minimizer equals w on the closed   *)
(* disc.                                                                      *)
(* ------------------------------------------------------------------------- *)

let hmd_ctx = new_definition
 `hmd_ctx (S:real^K->bool) (G:real^K->real^K^K) d e <=>
    cm_target S G d /\ &0 < e /\
    (?c. hmd_convex S G e c) /\ (?C. hmd_epsreg S G e C) /\
    WAN_RELLICH0_STATEMENT (:2) (:K) /\ WAN_GDIR_LSC_STATEMENT (:2) (:K) /\
    WAN_W120_CONT_STATEMENT (:2) (:K) /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
    CM_MINIMIZER_SMOOTH_STATEMENT (:K) /\ HMD_PG_STATEMENT (:K)`;;

let HMD_CMAP_WMAP = prove
 (`!(S:real^K->bool) s (u:real^2->real^K). cm_cmap S s u ==> cm_wmap S s u`,
  REWRITE_TAC[cm_cmap; cm_wmap] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `{}:real^2->bool` THEN REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
  ASM_MESON_TAC[SUBSET; CLOSURE_SUBSET]);;

let HMD_CMAP_CBALL = prove
 (`!(S:real^K->bool) (a:real^2) r (u:real^2->real^K).
     &0 < r
     ==> (cm_cmap S (ball(a,r)) u <=>
          wan_w12 (ball(a,r)) u /\ u continuous_on cball(a,r) /\
          !x. x IN cball(a,r) ==> u x IN S)`,
  SIMP_TAC[cm_cmap; CLOSURE_BALL]);;

let HMD_SOLVE = prove
 (`!S (G:real^K->real^K^K) d e (a:real^2) r (u:real^2->real^K).
     hmd_ctx S G d e /\ &0 < r /\ cm_cmap S (ball(a,r)) u /\ wan_gdir (ball(a,r)) G u <= e
     ==> ?w. cm_minimizer S G (ball(a,r)) w /\ wan_w120 (ball(a,r)) (\x. w x - u x) /\
             cm_cmap S (ball(a,r)) w /\ cm_harmonic S G (ball(a,r)) w /\
             (!x. x IN sphere(a,r) ==> w x = u x) /\
             wan_gdir (ball(a,r)) G w <= wan_gdir (ball(a,r)) G u /\
             (!w'. cm_minimizer S G (ball(a,r)) w' /\
                   wan_w120 (ball(a,r)) (\x. w' x - u x)
                   ==> negligible {x | x IN ball(a,r) /\ ~(w' x = w x)})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hmd_ctx] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `c:real`;
                 `a:real^2`; `r:real`; `u:real^2->real^K`] HMD_DEXIST) THEN
  ASM_SIMP_TAC[HMD_CMAP_WMAP] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `w:real^2->real^K` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN sphere(a,r) ==> (w:real^2->real^K) x = u x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^2) IN sphere(a,r)` THEN
    REWRITE_TAC[IN_SPHERE; IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[HMD_CMAP_CBALL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HMD_BDRY_CONT THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`;
                          `C:num->real`; `u:real^2->real^K`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^2) IN ball(a,r)` THENL
     [ASM_MESON_TAC[cm_harmonic];
      SUBGOAL_THEN `(x:real^2) IN sphere(a,r)` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^2) IN cball(a,r)` THEN UNDISCH_TAC `~((x:real^2) IN ball(a,r))` THEN
        REWRITE_TAC[IN_BALL; IN_CBALL; IN_SPHERE] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `cm_cmap S (ball(a,r)) (u:real^2->real^K)` THEN
      ASM_SIMP_TAC[HMD_CMAP_CBALL] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^2) IN sphere(a,r)` THEN
      REWRITE_TAC[IN_SPHERE; IN_CBALL] THEN REAL_ARITH_TAC]]);;

(* A minimizer that is continuous on the closed disc and has the boundary   *)
(* values of u on the circle is the solution, on the whole closed disc.     *)

let HMD_SOLVE_UNIQUE_CONT = prove
 (`!S (G:real^K->real^K^K) d e (a:real^2) r (u:real^2->real^K) w w'.
     hmd_ctx S G d e /\ &0 < r /\ cm_cmap S (ball(a,r)) u /\
     wan_gdir (ball(a,r)) G u <= e /\
     cm_minimizer S G (ball(a,r)) w /\ wan_w120 (ball(a,r)) (\x. w x - u x) /\
     cm_cmap S (ball(a,r)) w /\ (!x. x IN sphere(a,r) ==> w x = u x) /\
     (!w''. cm_minimizer S G (ball(a,r)) w'' /\ wan_w120 (ball(a,r)) (\x. w'' x - u x)
            ==> negligible {x | x IN ball(a,r) /\ ~(w'' x = w x)}) /\
     cm_minimizer S G (ball(a,r)) w' /\ cm_cmap S (ball(a,r)) w' /\
     (!x. x IN sphere(a,r) ==> w' x = u x)
     ==> wan_w120 (ball(a,r)) (\x. w' x - u x) /\ !x. x IN cball(a,r) ==> w' x = w x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w120 (ball(a,r)) (\x. (w':real^2->real^K) x - u x)` ASSUME_TAC THENL
   [UNDISCH_TAC `hmd_ctx (S:real^K->bool) G d e` THEN REWRITE_TAC[hmd_ctx; WAN_W120_CONT_STATEMENT] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_MESON_TAC[HMD_CMAP_CBALL];
      ASM_SIMP_TAC[VECTOR_SUB_REFL];
      MATCH_MP_TAC WAN_W12_SUB THEN ASM_MESON_TAC[cm_cmap]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^2) IN ball(a,r)` THENL
   [MP_TAC(ISPECL [`ball(a:real^2,r)`; `w':real^2->real^K`; `w:real^2->real^K`]
                  HMD_CONT_AE_EQ) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[HMD_CMAP_CBALL; CONTINUOUS_ON_SUBSET; BALL_SUBSET_CBALL];
        ASM_MESON_TAC[HMD_CMAP_CBALL; CONTINUOUS_ON_SUBSET; BALL_SUBSET_CBALL];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[]];
    SUBGOAL_THEN `(x:real^2) IN sphere(a,r)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN cball(a,r)` THEN UNDISCH_TAC `~((x:real^2) IN ball(a,r))` THEN
      REWRITE_TAC[IN_BALL; IN_CBALL; IN_SPHERE] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The energy estimate (3.6) (CM Cor 3.4, Step 1).  One side: the            *)
(* competitor v1 = Pg(w2 + (u1 - u2)) has the boundary values of u1 and      *)
(* energy at most E(w2) + (KK/lam) delta E + (3 KK / sqrt lam) sqrt(dir z)   *)
(* sqrt E; minimality of w1 does the rest.                                   *)
(* ------------------------------------------------------------------------- *)

let HMD_DIR_SUB_LE = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     open s /\ wan_w12 s u /\ wan_w12 s v
     ==> wan_dir s (\x. u x - v x) <= &2 * wan_dir s u + &2 * wan_dir s v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `v:real^N->real^K`] WAN_DIR_NEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `\x. --((v:real^N->real^K) x)`]
                WAN_DIR_ADD_LE) THEN
  ASM_REWRITE_TAC[GSYM VECTOR_SUB]);;

let HMD_EST_REAL = prove
 (`!gv gw KK dl dw dz E lam.
     &0 <= KK /\ &0 <= dl /\ &0 < lam /\ &0 <= dw /\ &0 <= dz /\ &0 <= E /\
     gv <= gw + KK * (dl * dw + sqrt dw * sqrt dz + dz) /\
     dw <= E / lam /\ dz <= &4 * E / lam
     ==> gv / &2 <= gw / &2 + KK / lam * dl * E + &3 * KK / sqrt lam * sqrt dz * sqrt E`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt lam` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt dw <= sqrt E / sqrt lam` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM SQRT_DIV; REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt dz <= &2 * sqrt E / sqrt lam` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * sqrt E / sqrt lam = sqrt(&4 * E / lam)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[SQRT_DIV; SQRT_MUL; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `sqrt(&4) = &2` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        REWRITE_TAC[real_div; REAL_MUL_ASSOC]];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dz = sqrt dz * sqrt dz` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt dz /\ &0 <= sqrt dw /\ &0 <= sqrt E` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `q = sqrt E / sqrt lam` THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `KK / lam * dl * E = KK * dl * (E / lam) /\
                &3 * KK / sqrt lam * sqrt dz * sqrt E = &3 * KK * sqrt dz * q`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [EXPAND_TAC "q" THEN CONJ_TAC THEN
    UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `&0 < sqrt lam` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `KK * dl * dw <= KK * dl * (E / lam)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `KK * sqrt dw * sqrt dz <= KK * sqrt dz * q` ASSUME_TAC THENL
   [SUBGOAL_THEN `(KK * sqrt dz) * sqrt dw <= (KK * sqrt dz) * q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `KK * dz <= KK * sqrt dz * (&2 * q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [th]) o
      check (fun th -> concl th = `dz = sqrt dz * sqrt dz`)) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sqrt dz <= &2 * sqrt E / sqrt lam` THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= KK * dl * (E / lam) /\ &0 <= KK * sqrt dz * q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* One side of (3.6): the competitor Pg(w2 + (u1 - u2)) for w1.              *)
(* ------------------------------------------------------------------------- *)

let HMD_ONE_SIDE = prove
 (`!S (G:real^K->real^K^K) d d1 B (Pg:real^K->real^K) KK lam (a:real^2) r
    (u1:real^2->real^K) u2 w1 w2 E delta.
     cm_target S G d /\ hmd_pgdata S d d1 B Pg /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
     WAN_W120_CONT_STATEMENT (:2) (:K) /\
     &0 <= KK /\
     (!y Z X Y. y IN S /\ norm Z <= d1 / &2
        ==> (frechet_derivative Pg (at (y + Z)) (X + Y)) dot
            (G(Pg(y + Z)) ** frechet_derivative Pg (at (y + Z)) (X + Y))
            <= X dot (G y ** X) +
               KK * (norm Z * norm X pow 2 + norm X * norm Y + norm Y pow 2)) /\
     &0 < lam /\ (!z xi. lam * norm xi pow 2 <= xi dot (G z ** xi)) /\
     &0 < r /\ cm_cmap S (ball(a,r)) u1 /\ cm_cmap S (ball(a,r)) u2 /\
     wan_gdir (ball(a,r)) G u1 <= E /\ wan_gdir (ball(a,r)) G u2 <= E /\
     cm_minimizer S G (ball(a,r)) w1 /\ cm_cmap S (ball(a,r)) w1 /\
     (!x. x IN sphere(a,r) ==> w1 x = u1 x) /\
     cm_cmap S (ball(a,r)) w2 /\ (!x. x IN sphere(a,r) ==> w2 x = u2 x) /\
     wan_gdir (ball(a,r)) G w2 <= E /\
     &0 <= delta /\ (!x. x IN cball(a,r) ==> norm(u1 x - u2 x) <= delta) /\
     delta <= d1 / &2
     ==> cm_gen G (ball(a,r)) w1 <=
         cm_gen G (ball(a,r)) w2 + KK / lam * delta * E +
         &3 * KK / sqrt lam * sqrt(wan_dir (ball(a,r)) (\x. u1 x - u2 x)) * sqrt E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`] HMD_PG_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < d1` ASSUME_TAC THENL [ASM_MESON_TAC[hmd_pgdata]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) `cm_cmap:(real^K->bool)->(real^2->bool)->(real^2->real^K)->bool`))
           (concl th)
    then SIMP_RULE[ASSUME `&0 < r`; HMD_CMAP_CBALL] th else th) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  ABBREV_TAC `z = \x. (u1:real^2->real^K) x - u2 x` THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (z:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2->real^K) continuous_on cball(a,r)` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(a,r) ==> norm((z:real^2->real^K) x) <= delta` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`; `KK:real`; `ball(a:real^2,r)`; `w2:real^2->real^K`;
                 `z:real^2->real^K`; `delta:real`; `{}:real^2->bool`] HMD_COMPETITOR_ENERGY) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL; NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `v1 = \x. (Pg:real^K->real^K)(w2 x + (z:real^2->real^K) x)` THEN
  STRIP_TAC THEN
  (* v1 is an admissible competitor for w1 *)
  SUBGOAL_THEN `!x. x IN cball(a,r) ==> norm((z:real^2->real^K) x) < d1` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `delta:real` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cm_wmap S (ball(a,r)) (v1:real^2->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[cm_wmap] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `{}:real^2->bool` THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    EXPAND_TAC "v1" THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN cball(a,r)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w120 (ball(a,r)) (\x. (v1:real^2->real^K) x - w1 x)` ASSUME_TAC THENL
   [UNDISCH_TAC `WAN_W120_CONT_STATEMENT (:2) (:K)` THEN
    REWRITE_TAC[WAN_W120_CONT_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "v1" THEN
      SUBGOAL_THEN `(\x. (Pg:real^K->real^K)((w2:real^2->real^K) x + (z:real^2->real^K) x)) =
                    Pg o (\x. w2 x + z x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
        REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXPAND_TAC "v1" THEN EXPAND_TAC "z" THEN
      REWRITE_TAC[] THEN ASM_SIMP_TAC[VECTOR_ARITH `w + u1 - w:real^N = u1`] THEN
      SUBGOAL_THEN `(x:real^2) IN cball(a,r)` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^2) IN sphere(a,r)` THEN
        REWRITE_TAC[IN_SPHERE; IN_CBALL] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(u1:real^2->real^K) x IN S` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[VECTOR_SUB_REFL];
      MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `cm_gen G (ball(a,r)) (w1:real^2->real^K) <= cm_gen G (ball(a,r)) v1`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cm_minimizer S G (ball(a,r)) (w1:real^2->real^K)` THEN
    REWRITE_TAC[cm_minimizer] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the numerical estimate *)
  SUBGOAL_THEN `!z xi. lam * norm xi pow 2 <= xi dot ((G:real^K->real^K^K) z ** xi) /\
                       xi dot (G z ** xi) <= Lam * norm xi pow 2`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:real^2->real^K. wan_w12 (ball(a,r)) u
       ==> lam * wan_dir (ball(a,r)) u <= wan_gdir (ball(a,r)) G u /\
           &0 <= wan_dir (ball(a,r)) u /\ &0 <= wan_gdir (ball(a,r)) G u`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^2->real^K` THEN DISCH_TAC THEN ASM_SIMP_TAC[WAN_DIR_POS] THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `G:real^K->real^K^K`; `u:real^2->real^K`;
                   `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
    ASM_SIMP_TAC[OPEN_BALL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME t))))
   [`wan_w12 (ball(a,r)) (w2:real^2->real^K)`; `wan_w12 (ball(a,r)) (u1:real^2->real^K)`;
    `wan_w12 (ball(a,r)) (u2:real^2->real^K)`; `wan_w12 (ball(a,r)) (z:real^2->real^K)`] THEN
  SUBGOAL_THEN `wan_dir (ball(a,r)) (u1:real^2->real^K) <= E / lam /\
                wan_dir (ball(a,r)) (u2:real^2->real^K) <= E / lam`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(a,r)) (z:real^2->real^K) <= &4 * E / lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * wan_dir (ball(a,r)) (u1:real^2->real^K) + &2 * wan_dir (ball(a,r)) (u2:real^2->real^K)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "z" THEN MATCH_MP_TAC HMD_DIR_SUB_LE THEN ASM_REWRITE_TAC[OPEN_BALL];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(a,r)) (w2:real^2->real^K) <= E / lam` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cm_gen G (ball(a,r)) (v1:real^2->real^K)` THEN
  ASM_REWRITE_TAC[cm_gen] THEN
  MATCH_MP_TAC HMD_EST_REAL THEN
  EXISTS_TAC `wan_dir (ball(a,r)) (w2:real^2->real^K)` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The energy estimate (3.6) in the form of CM_REPLACEMENT_STATEMENT,        *)
(* third part: both sides of HMD_ONE_SIDE when sup |u1 - u2| <= d1 / 2, and   *)
(* the trivial bound E / 2 otherwise.                                        *)
(* ------------------------------------------------------------------------- *)

let HMD_SUP_FACTS = prove
 (`!(S:real^K->bool) (a:real^2) r (u1:real^2->real^K) u2.
     compact S /\ &0 < r /\ (!x. x IN cball(a,r) ==> u1 x IN S /\ u2 x IN S)
     ==> &0 <= sup {norm(u1 x - u2 x) | x IN cball(a,r)} /\
         !x. x IN cball(a,r) ==> norm(u1 x - u2 x) <= sup {norm(u1 x - u2 x) | x IN cball(a,r)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `{norm((u1:real^2->real^K) x - u2 x) | x IN cball(a:real^2,r)}` SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; FORALL_IN_GSPEC; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`norm((u1:real^2->real^K) a - u2 a)`; `a:real^2`] THEN
      REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `&2 * M` THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `u2:real^2->real^K`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC(NORM_ARITH `norm(a:real^K) <= M /\ norm(b:real^K) <= M
                               ==> norm(a - b) <= &2 * M`) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((u1:real^2->real^K) a - u2 a)` THEN
  REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC);;

let HMD_ENERGY_EST = prove
 (`!S (G:real^K->real^K^K) d e.
     hmd_ctx S G d e
     ==> ?C. &0 < C /\
             !(a:real^2) r (u1:real^2->real^K) u2 w1 w2 E.
               &0 < r /\
               cm_cmap S (ball(a,r)) u1 /\ cm_cmap S (ball(a,r)) u2 /\
               wan_gdir (ball(a,r)) G u1 <= E /\ wan_gdir (ball(a,r)) G u2 <= E /\ E <= e /\
               cm_minimizer S G (ball(a,r)) w1 /\ wan_w120 (ball(a,r)) (\x. w1 x - u1 x) /\
               cm_minimizer S G (ball(a,r)) w2 /\ wan_w120 (ball(a,r)) (\x. w2 x - u2 x)
               ==> abs(cm_gen G (ball(a,r)) w1 - cm_gen G (ball(a,r)) w2)
                   <= C * sup {norm(u1 x - u2 x) | x IN cball(a,r)} * E +
                      C * sqrt(wan_dir (ball(a,r)) (\x. u1 x - u2 x)) * sqrt E`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [hmd_ctx]) THEN
  UNDISCH_TAC `HMD_PG_STATEMENT (:K)` THEN REWRITE_TAC[HMD_PG_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `Pg:real^K->real^K` ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`] HMD_PW_COMPOSITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `KK:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  SUBGOAL_THEN `&0 < d1` ASSUME_TAC THENL [ASM_MESON_TAC[hmd_pgdata]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt lam` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  EXISTS_TAC `KK / lam + &3 * KK / sqrt lam + inv d1 + &1` THEN
  SUBGOAL_THEN `&0 <= KK / lam /\ &0 <= &3 * KK / sqrt lam /\ &0 <= inv d1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u1:real^2->real^K`; `u2:real^2->real^K`;
                       `w1:real^2->real^K`; `w2:real^2->real^K`; `E:real`] THEN
  STRIP_TAC THEN
  (* the representatives *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `a:real^2`;
                 `r:real`; `u1:real^2->real^K`] HMD_SOLVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^2->real^K` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `a:real^2`;
                 `r:real`; `u2:real^2->real^K`] HMD_SOLVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:real^2->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cm_gen G (ball(a,r)) (w1:real^2->real^K) = cm_gen G (ball(a,r)) v1 /\
                cm_gen G (ball(a,r)) (w2:real^2->real^K) = cm_gen G (ball(a,r)) v2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC HMD_GEN_AE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* the sup *)
  ABBREV_TAC `delta = sup {norm((u1:real^2->real^K) x - u2 x) | x IN cball(a:real^2,r)}` THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `a:real^2`; `r:real`; `u1:real^2->real^K`;
                 `u2:real^2->real^K`] HMD_SUP_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
    ASM_MESON_TAC[HMD_CMAP_CBALL];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ABBREV_TAC `dz = wan_dir (ball(a,r)) (\x. (u1:real^2->real^K) x - u2 x)` THEN
  SUBGOAL_THEN `wan_dir (ball(a,r)) (\x. (u2:real^2->real^K) x - u1 x) = dz` ASSUME_TAC THENL
   [EXPAND_TAC "dz" THEN MATCH_MP_TAC HMC_DIR_SYM THEN REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC WAN_W12_SUB THEN ASM_MESON_TAC[cm_cmap];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN cball(a,r) ==> norm((u2:real^2->real^K) x - u1 x) <= delta`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z xi. lam * norm xi pow 2 <= xi dot ((G:real^K->real^K^K) z ** xi)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^2->real^K. wan_w12 (ball(a,r)) v ==> &0 <= wan_gdir (ball(a,r)) G v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `G:real^K->real^K^K`; `v:real^2->real^K`;
                   `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
    ASM_SIMP_TAC[OPEN_BALL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (v1:real^2->real^K) /\
                wan_w12 (ball(a,r)) (v2:real^2->real^K) /\
                wan_w12 (ball(a,r)) (u1:real^2->real^K) /\
                wan_w12 (ball(a,r)) (u2:real^2->real^K)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_cmap]; ALL_TAC] THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP th (ASSUME t))))
   [`wan_w12 (ball(a,r)) (v1:real^2->real^K)`; `wan_w12 (ball(a,r)) (v2:real^2->real^K)`;
    `wan_w12 (ball(a,r)) (u1:real^2->real^K)`] THEN
  SUBGOAL_THEN `&0 <= dz` ASSUME_TAC THENL
   [EXPAND_TAC "dz" THEN MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cm_gen G (ball(a,r)) (v1:real^2->real^K) /\
                &0 <= cm_gen G (ball(a,r)) (v2:real^2->real^K) /\
                cm_gen G (ball(a,r)) (v1:real^2->real^K) <= E / &2 /\
                cm_gen G (ball(a,r)) (v2:real^2->real^K) <= E / &2 /\
                &0 <= E /\ wan_gdir (ball(a,r)) G (v1:real^2->real^K) <= E /\
                wan_gdir (ball(a,r)) G (v2:real^2->real^K) <= E`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[cm_gen] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `delta <= d1 / &2` THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                   `Pg:real^K->real^K`; `KK:real`; `lam:real`; `a:real^2`; `r:real`;
                   `u1:real^2->real^K`; `u2:real^2->real^K`; `v1:real^2->real^K`;
                   `v2:real^2->real^K`; `E:real`; `delta:real`] HMD_ONE_SIDE) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                   `Pg:real^K->real^K`; `KK:real`; `lam:real`; `a:real^2`; `r:real`;
                   `u2:real^2->real^K`; `u1:real^2->real^K`; `v2:real^2->real^K`;
                   `v1:real^2->real^K`; `E:real`; `delta:real`] HMD_ONE_SIDE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= delta * E /\ &0 <= sqrt dz * sqrt E` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= ((KK / lam + &3 * KK / sqrt lam + inv d1 + &1) - KK / lam) * (delta * E) /\
      &0 <= ((KK / lam + &3 * KK / sqrt lam + inv d1 + &1) - &3 * KK / sqrt lam) *
            (sqrt dz * sqrt E)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 <= delta * E /\ &0 <= sqrt dz * sqrt E` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `E / &2 <= inv d1 * delta * E` ASSUME_TAC THENL
     [SUBGOAL_THEN `inv(&2) <= inv d1 * delta` MP_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        DISCH_TAC] THEN
      SUBGOAL_THEN `inv(&2) * E <= (inv d1 * delta) * E` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= ((KK / lam + &3 * KK / sqrt lam + inv d1 + &1) - inv d1) * (delta * E) /\
      &0 <= (KK / lam + &3 * KK / sqrt lam + inv d1 + &1) * (sqrt dz * sqrt E)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* W^{1,2} continuity of the competitor: for w with values in S a.e.         *)
(* and |z| <= delta <= d1 / 2,                                                *)
(*   dir(Pg(w + z) - w) <= 2 B^2 delta^2 dir(w) + 2 B^2 dir(z).               *)
(* ------------------------------------------------------------------------- *)

let HMD_COMPOSITE_DIFF_PT = prove
 (`!(Q:real^K->real^K) Q0 (X:real^K) Y (Z:real^K) B delta.
     linear Q /\ &0 <= B /\ norm Z <= delta /\
     (!v. norm(Q v) <= B * norm v) /\ (!v. norm(Q v - Q0 v) <= B * norm Z * norm v) /\
     X = Q0 X
     ==> norm(Q (X + Y) - X) pow 2
         <= &2 * B pow 2 * delta pow 2 * norm X pow 2 + &2 * B pow 2 * norm Y pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
  ASM_SIMP_TAC[LINEAR_ADD] THEN
  SUBGOAL_THEN `norm(((Q:real^K->real^K) X + Q Y) - Q0 X) <= B * delta * norm X + B * norm Y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(a - c:real^K) <= u /\ norm(b:real^K) <= v ==> norm((a + b) - c) <= u + v`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B * norm(Z:real^K) * norm(X:real^K)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B * delta * norm(X:real^K) /\ &0 <= B * norm(Y:real^K)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(Z:real^K)` THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(B * delta * norm(X:real^K) + B * norm(Y:real^K)) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  MP_TAC(SPEC `B * delta * norm(X:real^K) - B * norm(Y:real^K)` REAL_LE_POW_2) THEN
  REAL_ARITH_TAC);;

let HMD_COMPOSITE_DIFF = prove
 (`!S (G:real^K->real^K^K) d d1 B (Pg:real^K->real^K) s (w:real^2->real^K) z delta ZZ.
     cm_target S G d /\ hmd_pgdata S d d1 B Pg /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
     open s /\ bounded s /\ wan_w12 s w /\ wan_w12 s z /\
     negligible ZZ /\ (!x. x IN s DIFF ZZ ==> w x IN S) /\
     (!x. x IN s ==> norm(z x) <= delta)
     ==> wan_w12 s (\x. Pg(w x + z x) - w x) /\
         wan_dir s (\x. Pg(w x + z x) - w x)
         <= &2 * B pow 2 * delta pow 2 * wan_dir s w + &2 * B pow 2 * wan_dir s z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`] HMD_PG_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= B /\
                (!y v. norm(frechet_derivative (Pg:real^K->real^K) (at y) v) <= B * norm v) /\
                (!y z v. norm(frechet_derivative (Pg:real^K->real^K) (at y) v -
                              frechet_derivative Pg (at z) v) <= B * norm(y - z) * norm v)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[hmd_pgdata]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `w:real^2->real^K`; `z:real^2->real^K`] WAN_W12_ADD_WD) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
  UNDISCH_TAC `WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K)` THEN
  REWRITE_TAC[WAN_CHAIN_W12_STATEMENT] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real^2->bool`; `\x. (w:real^2->real^K) x + z x`;
                              `Pg:real^K->real^K`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^2->bool`; `w:real^2->real^K`; `Pg:real^K->real^K`]) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN
  ANTS_TAC THENL [EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  ANTS_TAC THENL [EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 s (\x. (Pg:real^K->real^K)((w:real^2->real^K) x + (z:real^2->real^K) x) - w x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* Pg o w = w a.e. *)
  SUBGOAL_THEN `negligible {x | x IN s /\
                  ~((Pg:real^K->real^K)((w:real^2->real^K) x) = w x)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `ZZ:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
    MATCH_MP_TAC(TAUT `(a /\ ~c ==> b) ==> a /\ ~b ==> c`) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `(Pg:real^K->real^K)`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 1 &&
      can (find_term ((=) `S:real^K->bool`)) (concl th))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> drop(integral s (\x. lift(norm(wan_wd s i
                (\x. (Pg:real^K->real^K)(w x + z x) - w x) x) pow 2))) <=
            &2 * B pow 2 * delta pow 2 *
            drop(integral s (\x. lift(norm(wan_wd s i (w:real^2->real^K) x) pow 2))) +
            &2 * B pow 2 *
            drop(integral s (\x. lift(norm(wan_wd s i (z:real^2->real^K) x) pow 2)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `wan_wd s i (\x. (Pg:real^K->real^K)((w:real^2->real^K) x)) = wan_wd s i w`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HMD_WD_AE THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC
     `NN = {x | x IN s /\
                ~(wan_wd s i (\x. (Pg:real^K->real^K)(w x + z x) - w x) x =
                  wan_wd s i (\x. Pg(w x + z x)) x - wan_wd s i w x)} UNION
           {x | x IN s /\
                ~(wan_wd s i (\x. (Pg:real^K->real^K)(w x + z x)) x =
                  frechet_derivative Pg (at (w x + z x))
                    (wan_wd s i (\x. (w:real^2->real^K) x + z x) x))} UNION
           {x | x IN s /\
                ~(wan_wd s i (\x. (w:real^2->real^K) x + z x) x =
                  wan_wd s i w x + wan_wd s i z x)} UNION
           {x | x IN s /\
                ~(wan_wd s i (\x. (Pg:real^K->real^K)((w:real^2->real^K) x)) x =
                  frechet_derivative Pg (at (w x)) (wan_wd s i w x))}` THEN
    SUBGOAL_THEN `negligible(NN:real^2->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "NN" THEN REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC WAN_WD_UNIQUE THEN ASM_SIMP_TAC[DIMINDEX_2] THEN
      TRY(MATCH_MP_TAC WAN_W12_SUB_WD THEN ASM_REWRITE_TAC[ETA_AX] THEN NO_TAC) THEN
      TRY(MATCH_MP_TAC WAN_W12_ADD THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      MP_TAC(ISPECL [`s:real^2->bool`; `\x. (Pg:real^K->real^K)((w:real^2->real^K) x + z x)`;
                     `w:real^2->real^K`] WAN_W12_SUB_WD) THEN
      ASM_SIMP_TAC[DIMINDEX_2; ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral s (\x. (&2 * B pow 2 * delta pow 2) %
                          lift(norm(wan_wd s i (w:real^2->real^K) x) pow 2) +
                          (&2 * B pow 2) % lift(norm(wan_wd s i (z:real^2->real^K) x) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN EXISTS_TAC `NN:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
        ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2; ETA_AX];
        MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
        MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
        ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2; ETA_AX];
        ALL_TAC] THEN
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      UNDISCH_TAC `~((x:real^2) IN NN)` THEN EXPAND_TAC "NN" THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP; GSYM REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN
       `linear(frechet_derivative (Pg:real^K->real^K) (at ((w:real^2->real^K) x + z x)))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `frechet_derivative (Pg:real^K->real^K) (at ((w:real^2->real^K) x + z x))` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!v. norm(frechet_derivative (Pg:real^K->real^K) (at ((w:real^2->real^K) x + z x)) v -
                 frechet_derivative Pg (at (w x)) v) <= B * norm((z:real^2->real^K) x) * norm v`
      ASSUME_TAC THENL
       [X_GEN_TAC `v:real^K` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`(w:real^2->real^K) x + z x`; `(w:real^2->real^K) x`;
                                      `v:real^K`] o
          check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3 &&
            can (find_term ((=) `B:real`)) (concl th))) THEN
        REWRITE_TAC[VECTOR_ARITH `(w + z) - w:real^N = z`];
        ALL_TAC] THEN
      MATCH_MP_TAC HMD_COMPOSITE_DIFF_PT THEN
      MAP_EVERY EXISTS_TAC
       [`frechet_derivative (Pg:real^K->real^K) (at ((w:real^2->real^K) x))`;
        `(z:real^2->real^K) x`] THEN
      ASM_SIMP_TAC[ETA_AX] THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x. lift(norm(wan_wd s i (w:real^2->real^K) x) pow 2)) integrable_on s /\
                  (\x. lift(norm(wan_wd s i (z:real^2->real^K) x) pow 2)) integrable_on s`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
      ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2; ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. (&2 * B pow 2 * delta pow 2) %
           lift(norm(wan_wd s i (w:real^2->real^K) x) pow 2)) integrable_on s /\
      (\x. (&2 * B pow 2) % lift(norm(wan_wd s i (z:real^2->real^K) x) pow 2)) integrable_on s`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; DROP_ADD; DROP_CMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[wan_dir; DIMINDEX_2; SUM_2] THEN
  FIRST_ASSUM(MP_TAC o SPEC `1`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
  REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* CM Cor 3.4, Step 2, preliminaries.  A continuous minimizer with the       *)
(* boundary values of u is the solution of HMD_SOLVE: it is harmonic, has    *)
(* w - u in W_0 and energy at most that of u.  The competitor               *)
(* Pg(w2 + (u1 - u2)) is admissible for u1.                                   *)
(* ------------------------------------------------------------------------- *)

let HMD_REP = prove
 (`!S (G:real^K->real^K^K) d e (a:real^2) r (u:real^2->real^K) w.
     hmd_ctx S G d e /\ &0 < r /\ cm_cmap S (ball(a,r)) u /\ wan_gdir (ball(a,r)) G u <= e /\
     cm_minimizer S G (ball(a,r)) w /\ cm_cmap S (ball(a,r)) w /\
     (!x. x IN sphere(a,r) ==> w x = u x)
     ==> wan_w120 (ball(a,r)) (\x. w x - u x) /\ cm_harmonic S G (ball(a,r)) w /\
         wan_w12 (ball(a,r)) w /\ wan_gdir (ball(a,r)) G w <= wan_gdir (ball(a,r)) G u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `a:real^2`;
                 `r:real`; `u:real^2->real^K`] HMD_SOLVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2->real^K` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `a:real^2`;
                 `r:real`; `u:real^2->real^K`; `v:real^2->real^K`; `w:real^2->real^K`]
                HMD_SOLVE_UNIQUE_CONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN ball(a,r) ==> (v:real^2->real^K) x = w x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HMD_HARMONIC_CONG THEN EXISTS_TAC `v:real^2->real^K` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[cm_cmap];
    SUBGOAL_THEN `wan_gdir (ball(a,r)) G (w:real^2->real^K) = wan_gdir (ball(a,r)) G v`
    SUBST1_TAC THENL
     [MATCH_MP_TAC HMD_GDIR_AE THEN MATCH_MP_TAC HMD_EQ_IMP_NULL THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

let HMD_COMPETITOR_ADM = prove
 (`!S (G:real^K->real^K^K) d d1 B (Pg:real^K->real^K) (a:real^2) r
    (u1:real^2->real^K) u2 w2 delta.
     cm_target S G d /\ hmd_pgdata S d d1 B Pg /\
     WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\ WAN_W120_CONT_STATEMENT (:2) (:K) /\
     &0 < r /\ cm_cmap S (ball(a,r)) u1 /\ cm_cmap S (ball(a,r)) u2 /\
     cm_cmap S (ball(a,r)) w2 /\ (!x. x IN sphere(a,r) ==> w2 x = u2 x) /\
     (!x. x IN cball(a,r) ==> norm(u1 x - u2 x) <= delta) /\ delta <= d1 / &2
     ==> wan_w12 (ball(a,r)) (\x. Pg(w2 x + (u1 x - u2 x))) /\
         cm_wmap S (ball(a,r)) (\x. Pg(w2 x + (u1 x - u2 x))) /\
         wan_w120 (ball(a,r)) (\x. Pg(w2 x + (u1 x - u2 x)) - u1 x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`] HMD_PG_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < d1` ASSUME_TAC THENL [ASM_MESON_TAC[hmd_pgdata]; ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) `cm_cmap:(real^K->bool)->(real^2->bool)->(real^2->real^K)->bool`))
           (concl th)
    then SIMP_RULE[ASSUME `&0 < r`; HMD_CMAP_CBALL] th else th) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (\x. (w2:real^2->real^K) x + (u1 x - u2 x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_W12_SUB THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_w12 (ball(a,r)) (\x. (Pg:real^K->real^K)((w2:real^2->real^K) x + (u1 x - u2 x)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K)` THEN
    REWRITE_TAC[WAN_CHAIN_W12_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`ball(a:real^2,r)`;
                               `\x. (w2:real^2->real^K) x + (u1 x - u2 x)`;
                               `Pg:real^K->real^K`]) THEN
    ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN
    ANTS_TAC THENL [EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN cball(a,r) ==> norm((u1:real^2->real^K) x - u2 x) < d1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `delta:real` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[cm_wmap] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `{}:real^2->bool` THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN cball(a,r)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `WAN_W120_CONT_STATEMENT (:2) (:K)` THEN
  REWRITE_TAC[WAN_W120_CONT_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\x. (Pg:real^K->real^K)((w2:real^2->real^K) x + (u1 x - u2 x))) =
                  Pg o (\x. w2 x + (u1 x - u2 x))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[VECTOR_ARITH `w + (u1 - w):real^N = u1`] THEN
    SUBGOAL_THEN `(x:real^2) IN cball(a,r)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN sphere(a,r)` THEN
      REWRITE_TAC[IN_SPHERE; IN_CBALL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(u1:real^2->real^K) x IN S` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL];
    MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* CM Cor 3.4, Step 2: the W^{1,2} estimate.  For two solutions w1, w0       *)
(* with boundary values u1, u0 and sup |u1 - u0| <= delta <= d1 / 2,         *)
(*   dir(w1 - w0) <= A (delta + sqrt dir(u1 - u0) + dir(u1 - u0)).          *)
(* The competitor V = Pg(w0 + (u1 - u0)) is admissible for u1; its energy   *)
(* is close to that of w0 (HMD_COMPETITOR_ENERGY), hence to that of w1      *)
(* (HMD_ONE_SIDE); convexity at w1 bounds dir(V - w1), and                  *)
(* HMD_COMPOSITE_DIFF bounds dir(V - w0).                                    *)
(* ------------------------------------------------------------------------- *)

let HMD_LIN3_BOUND = prove
 (`!a1 a2 a3 X Y Z t.
     &0 <= a1 /\ &0 <= a2 /\ &0 <= a3 /\ &0 <= X /\ &0 <= Y /\ &0 <= Z /\
     t <= a1 * X + a2 * Y + a3 * Z
     ==> t <= (a1 + a2 + a3 + &1) * (X + Y + Z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= a1 * Y /\ &0 <= a1 * Z /\ &0 <= a2 * X /\ &0 <= a2 * Z /\
                &0 <= a3 * X /\ &0 <= a3 * Y`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let HMD_DIR_PAIR_REAL = prove
 (`!gv g1 g0 c KK lam e B d1 delta dw0 dz dvw1 dvw0 d10.
     &0 < c /\ &0 <= KK /\ &0 < lam /\ &0 <= e /\ &0 <= B /\ &0 <= delta /\
     delta <= d1 / &2 /\ &0 <= dw0 /\ dw0 <= e / lam /\ &0 <= dz /\
     gv <= g0 + KK * (delta * dw0 + sqrt dw0 * sqrt dz + dz) /\
     g0 / &2 <= g1 / &2 + KK / lam * delta * e + &3 * KK / sqrt lam * sqrt dz * sqrt e /\
     c * dvw1 <= gv - g1 /\
     dvw0 <= &2 * B pow 2 * delta pow 2 * dw0 + &2 * B pow 2 * dz /\
     d10 <= &2 * dvw1 + &2 * dvw0
     ==> d10 <= ((&6 * KK * (e / lam) / c + &2 * B pow 2 * d1 * (e / lam)) +
                 &14 * KK * (sqrt e / sqrt lam) / c + (&2 * KK / c + &4 * B pow 2) + &1) *
                (delta + sqrt dz + dz)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt lam` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e / lam /\ &0 <= sqrt e / sqrt lam /\ &0 <= sqrt dz /\ &0 <= sqrt dw0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt dw0 <= sqrt e / sqrt lam` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM SQRT_DIV; REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `KK * delta * dw0 <= KK * delta * (e / lam)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `KK * sqrt dw0 * sqrt dz <= KK * (sqrt e / sqrt lam) * sqrt dz` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `gv - g1 <= &3 * KK * (e / lam) * delta + &7 * KK * (sqrt e / sqrt lam) * sqrt dz +
               KK * dz`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `dvw1 <= (&3 * KK * (e / lam) * delta + &7 * KK * (sqrt e / sqrt lam) * sqrt dz +
             KK * dz) / c`
  ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `delta pow 2 * dw0 <= delta * (d1 / &2) * (e / lam)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * B pow 2 * delta pow 2 * dw0 <=
                &2 * B pow 2 * (delta * (d1 / &2) * (e / lam))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= KK / c /\ &0 <= B pow 2 /\ &0 <= d1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `d10 <= (&6 * KK * (e / lam) / c + &2 * B pow 2 * d1 * (e / lam)) * delta +
           (&14 * KK * (sqrt e / sqrt lam) / c) * sqrt dz +
           (&2 * KK / c + &4 * B pow 2) * dz`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HMD_LIN3_BOUND THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POS]);;

let HMD_DIR_PAIR = prove
 (`!S (G:real^K->real^K^K) d e.
     hmd_ctx S G d e
     ==> ?A D0. &0 < A /\ &0 < D0 /\
           !(a:real^2) r (u1:real^2->real^K) w1 u0 w0 delta.
             &0 < r /\
             cm_cmap S (ball(a,r)) u1 /\ wan_gdir (ball(a,r)) G u1 <= e /\
             cm_minimizer S G (ball(a,r)) w1 /\ cm_cmap S (ball(a,r)) w1 /\
             (!x. x IN sphere(a,r) ==> w1 x = u1 x) /\
             cm_cmap S (ball(a,r)) u0 /\ wan_gdir (ball(a,r)) G u0 <= e /\
             cm_minimizer S G (ball(a,r)) w0 /\ cm_cmap S (ball(a,r)) w0 /\
             (!x. x IN sphere(a,r) ==> w0 x = u0 x) /\
             &0 <= delta /\ delta <= D0 /\
             (!x. x IN cball(a,r) ==> norm(u1 x - u0 x) <= delta)
             ==> wan_dir (ball(a,r)) (\x. w1 x - w0 x)
                 <= A * (delta + sqrt(wan_dir (ball(a,r)) (\x. u1 x - u0 x)) +
                         wan_dir (ball(a,r)) (\x. u1 x - u0 x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [hmd_ctx]) THEN
  UNDISCH_TAC `HMD_PG_STATEMENT (:K)` THEN REWRITE_TAC[HMD_PG_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `Pg:real^K->real^K` ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`] HMD_PW_COMPOSITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `KK:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  SUBGOAL_THEN `&0 < d1 /\ &0 <= B` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[hmd_pgdata]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_MESON_TAC[hmd_convex]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!z xi. lam * norm xi pow 2 <= xi dot ((G:real^K->real^K^K) z ** xi)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(&6 * KK * (e / lam) / c + &2 * B pow 2 * d1 * (e / lam)) +
              &14 * KK * (sqrt e / sqrt lam) / c + (&2 * KK / c + &4 * B pow 2) + &1` THEN
  EXISTS_TAC `d1 / &2` THEN
  SUBGOAL_THEN `&0 <= &6 * KK * (e / lam) / c + &2 * B pow 2 * d1 * (e / lam) /\
                &0 <= &14 * KK * (sqrt e / sqrt lam) / c /\ &0 <= &2 * KK / c + &4 * B pow 2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= e / lam /\ &0 <= sqrt e / sqrt lam /\ &0 <= B pow 2 /\ &0 <= d1`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; SQRT_POS_LE; REAL_LT_IMP_LE; REAL_LE_POW_2]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POS];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u1:real^2->real^K`; `w1:real^2->real^K`;
                       `u0:real^2->real^K`; `w0:real^2->real^K`; `delta:real`] THEN
  STRIP_TAC THEN
  (* the representations *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `a:real^2`;
                 `r:real`; `u1:real^2->real^K`; `w1:real^2->real^K`] HMD_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `a:real^2`;
                 `r:real`; `u0:real^2->real^K`; `w0:real^2->real^K`] HMD_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v:real^2->real^K. cm_cmap S (ball(a,r)) v
       ==> wan_w12 (ball(a,r)) v /\ v continuous_on cball(a,r) /\
           !x. x IN cball(a,r) ==> v x IN S`
  (fun th -> MAP_EVERY (fun t -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME t)))
     [`cm_cmap S (ball(a,r)) (u1:real^2->real^K)`; `cm_cmap S (ball(a,r)) (u0:real^2->real^K)`;
      `cm_cmap S (ball(a,r)) (w0:real^2->real^K)`]) THENL
   [ASM_SIMP_TAC[HMD_CMAP_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(a,r) ==> x IN cball(a:real^2,r)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUBSET; BALL_SUBSET_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(a,r) ==> (w0:real^2->real^K) x IN S` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(a,r) ==> norm((u1:real^2->real^K) x - u0 x) <= delta`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN cball(a,r) ==> norm((u0:real^2->real^K) x - u1 x) <= delta`
  ASSUME_TAC THENL [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(a,r)) G (w1:real^2->real^K) <= e` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (\x. (u1:real^2->real^K) x - u0 x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cm_wmap S (ball(a,r)) (w1:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_CMAP_WMAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the competitor V = Pg(w0 + (u1 - u0)) *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`; `a:real^2`; `r:real`; `u1:real^2->real^K`;
                 `u0:real^2->real^K`; `w0:real^2->real^K`; `delta:real`] HMD_COMPETITOR_ADM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`; `KK:real`; `ball(a:real^2,r)`; `w0:real^2->real^K`;
                 `\x. (u1:real^2->real^K) x - u0 x`; `delta:real`; `{}:real^2->bool`]
                HMD_COMPETITOR_ENERGY) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL; NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`; `KK:real`; `lam:real`; `a:real^2`; `r:real`;
                 `u0:real^2->real^K`; `u1:real^2->real^K`; `w0:real^2->real^K`;
                 `w1:real^2->real^K`; `e:real`; `delta:real`] HMD_ONE_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[cm_gen] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`; `ball(a:real^2,r)`; `w0:real^2->real^K`;
                 `\x. (u1:real^2->real^K) x - u0 x`; `delta:real`; `{}:real^2->bool`]
                HMD_COMPOSITE_DIFF) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL; NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN STRIP_TAC THEN
  (* convexity at w1 *)
  SUBGOAL_THEN
   `wan_w120 (ball(a,r))
      (\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x)) - w1 x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^2,r)`;
                   `\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x)) - u1 x`;
                   `\x. (w1:real^2->real^K) x - u1 x`] WAN_W120_SUB) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [hmd_convex] o
    check (fun th -> can (find_term ((=) `hmd_convex:(real^K->bool)->(real^K->real^K^K)->real->real->bool`)) (concl th))) THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^2`; `r:real`;
    `\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x))`; `w1:real^2->real^K`] o
    CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the triangle inequality *)
  SUBGOAL_THEN
   `wan_dir (ball(a,r)) (\x. (w1:real^2->real^K) x - w0 x) <=
    &2 * wan_dir (ball(a,r))
           (\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x)) - w1 x) +
    &2 * wan_dir (ball(a,r))
           (\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x)) - w0 x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `wan_w12 (ball(a,r))
        (\x. (w1:real^2->real^K) x - (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x)))`
    ASSUME_TAC THENL [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`;
                   `\x. (w1:real^2->real^K) x -
                        (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x))`;
                   `\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x)) - w0 x`]
                  WAN_DIR_ADD_LE) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    REWRITE_TAC[VECTOR_ARITH `(w1 - p) + (p - w0):real^N = w1 - w0`] THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`;
                   `\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x))`;
                   `w1:real^2->real^K`] HMC_DIR_SYM) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  (* dir(u0 - u1) = dir(u1 - u0), bounds for w0 *)
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `u1:real^2->real^K`; `u0:real^2->real^K`] HMC_DIR_SYM) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `wan_dir (ball(a,r)) (\x. (u0:real^2->real^K) x - u1 x) =
     wan_dir (ball(a,r)) (\x. u1 x - u0 x)`]) THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `G:real^K->real^K^K`; `w0:real^2->real^K`;
                 `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
  ASM_SIMP_TAC[OPEN_BALL; REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_dir (ball(a,r)) (w0:real^2->real^K) <= e / lam` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= wan_dir (ball(a,r)) (w0:real^2->real^K) /\
                &0 <= wan_dir (ball(a,r)) (\x. (u1:real^2->real^K) x - u0 x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HMD_DIR_PAIR_REAL THEN
  MAP_EVERY EXISTS_TAC
   [`wan_gdir (ball(a,r)) G (\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x)))`;
    `wan_gdir (ball(a,r)) G (w1:real^2->real^K)`; `wan_gdir (ball(a,r)) G (w0:real^2->real^K)`;
    `wan_dir (ball(a,r)) (w0:real^2->real^K)`;
    `wan_dir (ball(a,r))
       (\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x)) - w1 x)`;
    `wan_dir (ball(a,r))
       (\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + (u1 x - u0 x)) - w0 x)`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* CM Cor 3.4, Step 2: tools for the uniform convergence inside.             *)
(* A Lipschitz bound for harmonic maps of small energy on cball(a, r - t)   *)
(* (epsilon-regularity), Lipschitz plus small L^2 norm gives a small sup,   *)
(* the L^2 norm of w1 - w0 by Poincare, and the monotonicity of dir in the  *)
(* domain.                                                                    *)
(* ------------------------------------------------------------------------- *)

let HMD_LIP_INTERIOR = prove
 (`!S (G:real^K->real^K^K) d e0 C (a:real^2) r (w:real^2->real^K) t E.
     cm_target S G d /\ hmd_epsreg S G e0 C /\ &0 < t /\ t < r /\
     cm_harmonic S G (ball(a,r)) w /\ wan_w12 (ball(a,r)) w /\
     wan_gdir (ball(a,r)) G w <= e0 /\ wan_gdir (ball(a,r)) G w <= E
     ==> !x y. x IN cball(a,r - t) /\ y IN cball(a,r - t)
               ==> norm(w x - w y) <= &2 * (C 1 * sqrt E / t) * norm(x - y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HMD_SEGMENT_MVT THEN EXISTS_TAC `ball(a:real^2,r)` THEN
  REWRITE_TAC[OPEN_BALL] THEN
  SUBGOAL_THEN `cball(a:real^2,r - t) SUBSET ball(a,r)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^2,y] SUBSET cball(a,r - t)` ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_CBALL]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[cm_harmonic];
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:real^2`; `i:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^2) IN cball(a,r - t)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `C:num->real`;
                 `ball(a:real^2,r)`; `ball(a:real^2,r)`; `w:real^2->real^K`; `z:real^2`;
                 `t:real`; `i:num`] HMD_GRAD_AT_CENTER) THEN
  ASM_REWRITE_TAC[OPEN_BALL; SUBSET_REFL] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `q:real^2` THEN
    UNDISCH_TAC `(z:real^2) IN cball(a,r - t)` THEN REWRITE_TAC[IN_CBALL] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `C 1 * sqrt E / t = (C 1 * sqrt E) / t` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C 1 * sqrt(wan_gdir (ball(a:real^2,r)) G (w:real^2->real^K))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_MONO_LE] THEN
  ASM_MESON_TAC[hmd_epsreg; REAL_LT_IMP_LE]);;

let HMD_DIR_SUBSET_LE = prove
 (`!(s:real^N->bool) t (u:real^N->real^K).
     open t /\ t SUBSET s /\ wan_w12 s u ==> wan_dir t u <= wan_dir s u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `u:real^N->real^K`; `i:num`]
                WAN_WD_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `i:num`; `u:real^N->real^K`] WAN_WD_WORKS) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`] WAN_WD_WORKS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_wd s i (u:real^N->real^K) IN lspace t (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM WAN_SOB_LNORM2_SQ; ETA_AX] THEN
  SUBGOAL_THEN `lnorm t (&2) (wan_wd t i (u:real^N->real^K)) = lnorm t (&2) (wan_wd s i u)`
  SUBST1_TAC THENL [MATCH_MP_TAC HMD_LNORM_AE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[LNORM_POS_LE] THEN
  MATCH_MP_TAC HMD_LNORM_SUBSET THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; REAL_POS]);;

let HMD_LIP_L2 = prove
 (`!(f:real^2->real^K) (a:real^2) r t L eps x0.
     &0 < t /\ &0 < L /\ &0 < eps /\
     (!x y. x IN cball(a,r - t) /\ y IN cball(a,r - t)
            ==> norm(f x - f y) <= L * norm(x - y)) /\
     f IN lspace (ball(a,r)) (&2) /\ x0 IN cball(a,r - &2 * t) /\ eps <= norm(f x0)
     ==> (eps / &2) pow 2 * measure(ball(x0,min t (eps / (&2 * L))))
         <= drop(integral (ball(a,r)) (\x. lift(norm(f x) pow 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < min t (eps / (&2 * L)) /\ min t (eps / (&2 * L)) <= t /\
                L * min t (eps / (&2 * L)) <= eps / &2` MP_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * eps / (&2 * L)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC `rho = min t (eps / (&2 * L))` THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball(x0:real^2,rho) SUBSET cball(a,r - t) /\ ball(x0,rho) SUBSET ball(a,r)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^2) IN cball(a,r - &2 * t)` THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN DISCH_TAC THEN CONJ_TAC THEN
    X_GEN_TAC `y:real^2` THEN UNDISCH_TAC `rho <= t` THEN UNDISCH_TAC `&0 < t` THEN
    UNDISCH_TAC `dist(a:real^2,x0) <= r - &2 * t` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(x0:real^2,rho) ==> (eps / &2) pow 2 <= norm((f:real^2->real^K) y) pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm((f:real^2->real^K) y - f x0) <= L * norm(y - x0)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x0:real^2) IN cball(a,r - &2 * t)` THEN REWRITE_TAC[IN_CBALL] THEN
      UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `L * norm(y - x0:real^2) <= L * rho` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      UNDISCH_TAC `(y:real^2) IN ball(x0,rho)` THEN REWRITE_TAC[IN_BALL] THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm((f:real^2->real^K) y - f x0) <= eps / &2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `norm((f:real^2->real^K) y - f x0) <= eps / &2` THEN
    UNDISCH_TAC `eps <= norm((f:real^2->real^K) x0)` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((f:real^2->real^K) x) pow 2)) integrable_on ball(a,r) /\
    (\x. lift(norm((f:real^2->real^K) x) pow 2)) integrable_on ball(x0,rho)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (ball(x0:real^2,rho)) (\x. lift(norm((f:real^2->real^K) x) pow 2)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2]] THEN
  SUBGOAL_THEN `(eps / &2) pow 2 * measure(ball(x0:real^2,rho)) =
                drop(integral (ball(x0,rho)) (\x:real^2. lift((eps / &2) pow 2)))`
  SUBST1_TAC THENL
   [SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[LIFT_DROP; INTEGRABLE_ON_CONST; MEASURABLE_BALL]);;

let HMD_L2_DIFF = prove
 (`!(a:real^2) r (u1:real^2->real^K) w1 u0 w0 delta.
     &0 < r /\ wan_w12 (ball(a,r)) u1 /\ wan_w12 (ball(a,r)) u0 /\
     wan_w12 (ball(a,r)) w1 /\ wan_w12 (ball(a,r)) w0 /\
     wan_w120 (ball(a,r)) (\x. w1 x - u1 x) /\ wan_w120 (ball(a,r)) (\x. w0 x - u0 x) /\
     (!x. x IN ball(a,r) ==> norm(u1 x - u0 x) <= delta)
     ==> drop(integral (ball(a,r)) (\x. lift(norm(w1 x - w0 x) pow 2)))
         <= &16 * r pow 2 * (wan_dir (ball(a,r)) (\x. w1 x - w0 x) +
                             wan_dir (ball(a,r)) (\x. u1 x - u0 x)) +
            &2 * measure(ball(a,r)) * delta pow 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = \x. ((w1:real^2->real^K) x - u1 x) - (w0 x - u0 x)` THEN
  SUBGOAL_THEN `wan_w120 (ball(a,r)) (g:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC WAN_W120_SUB THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (\x. (w1:real^2->real^K) x - w0 x) /\
                wan_w12 (ball(a,r)) (\x. (u1:real^2->real^K) x - u0 x)`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (w1:real^2->real^K) x - w0 x) IN lspace (ball(a,r)) (&2) /\
                (\x. (u1:real^2->real^K) x - u0 x) IN lspace (ball(a,r)) (&2) /\
                (g:real^2->real^K) IN lspace (ball(a,r)) (&2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[wan_w12; wan_w120]; ALL_TAC] THEN
  SUBGOAL_THEN `lnorm (ball(a,r)) (&2) (g:real^2->real^K) pow 2 <=
                &4 * r pow 2 * wan_dir (ball(a,r)) g` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_POINCARE0) THEN REWRITE_TAC[WAN_POINCARE0_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `a:real^2` THEN
    ASM_REWRITE_TAC[OPEN_BALL; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(a,r)) (g:real^2->real^K) <=
                &2 * wan_dir (ball(a,r)) (\x. (w1:real^2->real^K) x - w0 x) +
                &2 * wan_dir (ball(a,r)) (\x. (u1:real^2->real^K) x - u0 x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `g = (\x. ((w1:real^2->real^K) x - w0 x) - (u1 x - u0 x))` SUBST1_TAC THENL
     [EXPAND_TAC "g" THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HMD_DIR_SUB_LE THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnorm (ball(a,r)) (&2) (\x. (w1:real^2->real^K) x - w0 x) <=
    lnorm (ball(a,r)) (&2) (g:real^2->real^K) + lnorm (ball(a,r)) (&2) (\x. (u1:real^2->real^K) x - u0 x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^2,r)`; `&2`; `g:real^2->real^K`;
                   `\x. (u1:real^2->real^K) x - u0 x`] LNORM_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> y <= z ==> x <= z`) THEN AP_TERM_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnorm (ball(a,r)) (&2) (\x. (u1:real^2->real^K) x - u0 x) pow 2 <=
    measure(ball(a:real^2,r)) * delta pow 2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. (u1:real^2->real^K) x - u0 x`; `ball(a:real^2,r)`] WAN_SOB_LNORM2_SQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (ball(a:real^2,r)) (\x:real^2. lift(delta pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL];
        REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        ASM_SIMP_TAC[NORM_POS_LE]];
      SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (w1:real^2->real^K) x - w0 x`; `ball(a:real^2,r)`] WAN_SOB_LNORM2_SQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(lnorm (ball(a,r)) (&2) (g:real^2->real^K) +
               lnorm (ball(a,r)) (&2) (\x. (u1:real^2->real^K) x - u0 x)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[LNORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 * wan_dir (ball(a,r)) (g:real^2->real^K) <=
                r pow 2 * (&2 * wan_dir (ball(a,r)) (\x. (w1:real^2->real^K) x - w0 x) +
                           &2 * wan_dir (ball(a,r)) (\x. (u1:real^2->real^K) x - u0 x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  MP_TAC(SPEC `lnorm (ball(a,r)) (&2) (g:real^2->real^K) -
               lnorm (ball(a,r)) (&2) (\x. (u1:real^2->real^K) x - u0 x)` REAL_LE_POW_2) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* CM Cor 3.4, Step 2: the uniform estimate near the circle.  The            *)
(* boundary estimate HMD_QBE as a predicate, the local energy of w1 near    *)
(* the circle in terms of that of w0 and dir(w1 - w0), and the pointwise    *)
(* bound |w1 - w0| <= eps / 2 + 3 delta on the annulus of width 2 t.        *)
(* ------------------------------------------------------------------------- *)

let hmd_qbe = new_definition
 `hmd_qbe (S:real^K->bool) (G:real^K->real^K^K) e0 CQ <=>
    !(a:real^2) r (u:real^2->real^K) w x1 t eta.
       &0 < r /\ cm_cmap S (ball(a,r)) u /\ cm_harmonic S G (ball(a,r)) w /\
       wan_w12 (ball(a,r)) w /\ wan_gdir (ball(a,r)) G w <= e0 /\
       wan_w120 (ball(a,r)) (\x. w x - u x) /\
       x1 IN sphere(a,r) /\ &0 < t /\ &2 * t < r /\
       (!p. p IN cball(a,r) /\ norm(p - x1) <= t ==> norm(u p - u x1) <= eta)
       ==> norm(w(x1 + (t / r) % (a - x1)) - u x1)
           <= CQ * sqrt(wan_gdir (ball(a,r) INTER ball(x1,&2 * t)) G w) + eta`;;

let HMD_QBE_EX = prove
 (`!S (G:real^K->real^K^K) d e0 C.
     cm_target S G d /\ hmd_epsreg S G e0 C ==> ?CQ. &0 < CQ /\ hmd_qbe S G e0 CQ`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP HMD_QBE) THEN
  REWRITE_TAC[hmd_qbe] THEN DISCH_THEN ACCEPT_TAC);;

let HMD_LOCAL_ENERGY = prove
 (`!(G:real^K->real^K^K) (B:real^2->bool) D (w1:real^2->real^K) w0 lam Lam.
     open B /\ open D /\ D SUBSET B /\ wan_w12 B w1 /\ wan_w12 B w0 /\
     &0 < lam /\ &0 <= Lam /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z xi. lam * norm xi pow 2 <= xi dot (G z ** xi) /\
             xi dot (G z ** xi) <= Lam * norm xi pow 2)
     ==> wan_gdir D G w1
         <= &2 * Lam / lam * wan_gdir D G w0 + &2 * Lam * wan_dir B (\x. w1 x - w0 x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 B (\x. (w1:real^2->real^K) x - w0 x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 D (w1:real^2->real^K) /\ wan_w12 D (w0:real^2->real^K) /\
                wan_w12 D (\x. (w1:real^2->real^K) x - w0 x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC WAN_W12_SUBSET THEN
    EXISTS_TAC `B:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`D:real^2->bool`; `G:real^K->real^K^K`; `w1:real^2->real^K`; `lam:real`;
                 `Lam:real`] HMD_GDIR_BOUNDS) THEN
  MP_TAC(ISPECL [`D:real^2->bool`; `G:real^K->real^K^K`; `w0:real^2->real^K`; `lam:real`;
                 `Lam:real`] HMD_GDIR_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`D:real^2->bool`; `w0:real^2->real^K`; `\x. (w1:real^2->real^K) x - w0 x`]
                WAN_DIR_ADD_LE) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `w0 + (w1 - w0):real^N = w1`; ETA_AX] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `D:real^2->bool`; `\x. (w1:real^2->real^K) x - w0 x`]
                HMD_DIR_SUBSET_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `wan_dir D (w0:real^2->real^K) <= wan_gdir D G w0 / lam` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `Lam * wan_dir D (w1:real^2->real^K) <=
    Lam * (&2 * wan_gdir D G w0 / lam + &2 * wan_dir B (\x. w1 x - w0 x))`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let HMD_NEAR_BDRY = prove
 (`!S (G:real^K->real^K^K) e CQ lam Lam (a:real^2) r (u1:real^2->real^K) w1 u0 w0
    t delta eps T0.
     hmd_qbe S G e CQ /\ &0 < CQ /\ &0 < lam /\ &0 <= Lam /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z xi. lam * norm xi pow 2 <= xi dot (G z ** xi) /\
             xi dot (G z ** xi) <= Lam * norm xi pow 2) /\
     &0 < r /\ &0 < t /\ &4 * t < r /\ &0 < eps /\
     cm_cmap S (ball(a,r)) u1 /\ cm_harmonic S G (ball(a,r)) w1 /\ wan_w12 (ball(a,r)) w1 /\
     wan_gdir (ball(a,r)) G w1 <= e /\ wan_w120 (ball(a,r)) (\x. w1 x - u1 x) /\
     (!x. x IN sphere(a,r) ==> w1 x = u1 x) /\
     cm_cmap S (ball(a,r)) u0 /\ cm_harmonic S G (ball(a,r)) w0 /\ wan_w12 (ball(a,r)) w0 /\
     wan_gdir (ball(a,r)) G w0 <= e /\ wan_w120 (ball(a,r)) (\x. w0 x - u0 x) /\
     (!x. x IN sphere(a,r) ==> w0 x = u0 x) /\
     (!x. x IN cball(a,r) ==> norm(u1 x - u0 x) <= delta) /\
     (!p q. p IN cball(a,r) /\ q IN cball(a,r) /\ norm(p - q) <= &2 * t
            ==> norm(u0 p - u0 q) <= eps / &8) /\
     (!x0 rho'. &0 < rho' /\ rho' <= &4 * t
                ==> wan_gdir (ball(a,r) INTER ball(x0,rho')) G w0 <= T0) /\
     CQ * sqrt T0 <= eps / &8 /\
     CQ * sqrt(&2 * Lam / lam * T0 + &2 * Lam * wan_dir (ball(a,r)) (\x. w1 x - w0 x))
     <= eps / &8
     ==> !x. x IN cball(a,r) /\ r - &2 * t <= norm(x - a)
             ==> norm(w1 x - w0 x) <= eps / &2 + &3 * delta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((u1:real^2->real^K) x - u0 x)` THEN
    ASM_SIMP_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^2) IN sphere(a,r)` THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `delta:real` THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^2 = a)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `r - &2 * t <= norm(a - a:real^2)` THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN ball(a,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `~((x:real^2) IN sphere(a,r))` THEN UNDISCH_TAC `(x:real^2) IN cball(a,r)` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL; IN_SPHERE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x - a:real^2) < r` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN ball(a,r)` THEN REWRITE_TAC[IN_BALL] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `x:real^2`] HMD_NORMAL_REP) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `x1 = a + (r / norm(x - a)) % (x - a:real^2)` THEN
  ABBREV_TAC `s = r - norm(x - a:real^2)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s /\ s <= &2 * t /\ &2 * s < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x1:real^2) IN cball(a,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x1:real^2) IN sphere(a,r)` THEN REWRITE_TAC[IN_SPHERE; IN_CBALL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `x:real^2`)) THEN
  SUBGOAL_THEN `!p. p IN cball(a,r) /\ norm(p - x1) <= s
                    ==> norm((u0:real^2->real^K) p - u0 x1) <= eps / &8`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^2` THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `eps / &8`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* QBE for w1 and for w0 at x1 *)
  FIRST_ASSUM(MP_TAC o SPECL [`a:real^2`; `r:real`; `u1:real^2->real^K`; `w1:real^2->real^K`;
                              `x1:real^2`; `s:real`; `&2 * delta + eps / &8`] o
              GEN_REWRITE_RULE I [hmd_qbe]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm((u1:real^2->real^K) p - u0 p) <= delta /\
                  norm((u1:real^2->real^K) x1 - u0 x1) <= delta /\
                  norm((u0:real^2->real^K) p - u0 x1) <= eps / &8`
    MP_TAC THENL [ASM_SIMP_TAC[]; CONV_TAC NORM_ARITH];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`a:real^2`; `r:real`; `u0:real^2->real^K`; `w0:real^2->real^K`;
                              `x1:real^2`; `s:real`; `eps / &8`] o
              GEN_REWRITE_RULE I [hmd_qbe]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  (* the local energies *)
  SUBGOAL_THEN `wan_gdir (ball(a,r) INTER ball(x1,&2 * s)) G (w0:real^2->real^K) <= T0`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `T0:real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `ball(a:real^2,r)`; `ball(a:real^2,r) INTER ball(x1,&2 * s)`;
                 `w1:real^2->real^K`; `w0:real^2->real^K`; `lam:real`; `Lam:real`]
                HMD_LOCAL_ENERGY) THEN
  ASM_SIMP_TAC[OPEN_BALL; OPEN_INTER; INTER_SUBSET] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 * Lam / lam * wan_gdir (ball(a,r) INTER ball(x1,&2 * s)) G (w0:real^2->real^K)
                <= &2 * Lam / lam * T0` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CQ * sqrt(wan_gdir (ball(a,r) INTER ball(x1,&2 * s)) G (w0:real^2->real^K)) <= eps / &8 /\
    CQ * sqrt(wan_gdir (ball(a,r) INTER ball(x1,&2 * s)) G (w1:real^2->real^K)) <= eps / &8`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `CQ * sqrt T0`; EXISTS_TAC
       `CQ * sqrt(&2 * Lam / lam * T0 +
                  &2 * Lam * wan_dir (ball(a,r)) (\x. (w1:real^2->real^K) x - w0 x))`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_MONO_LE] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((u1:real^2->real^K) x1 - u0 x1) <= delta` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((w1:real^2->real^K) x - w0 x) <=
                norm(w1 x - (u1:real^2->real^K) (x1:real^2)) +
                norm(u1 x1 - (u0:real^2->real^K) x1) + norm(w0 x - u0 x1)`
  ASSUME_TAC THENL [CONV_TAC NORM_ARITH; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* CM Cor 3.4, Step 2: the interior uniform estimate for a pair, and a       *)
(* choice of a small eta.  Inside cball(a, r - 2 t) both solutions are      *)
(* uniformly Lipschitz (HMD_LIP_INTERIOR), so a value |w1 - w0| >= eps      *)
(* forces a definite amount of L^2 norm (HMD_LIP_L2), which HMD_L2_DIFF     *)
(* excludes.                                                                  *)
(* ------------------------------------------------------------------------- *)

let HMD_SMALL_ETA = prove
 (`!A dd. &0 < A /\ &0 < dd
          ==> ?eta. &0 < eta /\ eta <= &1 /\
                    !delta dz. &0 <= delta /\ delta <= eta /\ &0 <= dz /\ dz <= eta
                               ==> A * (delta + sqrt dz + dz) < dd`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = dd / (&4 * A)` THEN
  SUBGOAL_THEN `&0 < q /\ A * q = dd / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < A` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1) (q pow 2)` THEN
  SUBGOAL_THEN `&0 < q pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `min (&1) (q pow 2) <= q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MIN_LE] THEN ASM_CASES_TAC `&1 <= q` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt dz <= q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(q pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `min (&1) (q pow 2)` THEN
      ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `A * delta <= A * q /\ A * sqrt dz <= A * q /\ A * dz <= A * q`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let HMD_INTERIOR_PAIR = prove
 (`!S (G:real^K->real^K^K) d e C (a:real^2) r (u1:real^2->real^K) w1 u0 w0 t L eps delta.
     cm_target S G d /\ hmd_epsreg S G e C /\ &0 < e /\ &0 < t /\ &2 * t < r /\ &0 < eps /\
     &0 < L /\ &4 * (C 1 * sqrt e / t) <= L /\ delta <= &1 /\
     wan_w12 (ball(a,r)) u1 /\ wan_w12 (ball(a,r)) u0 /\
     cm_harmonic S G (ball(a,r)) w1 /\ wan_w12 (ball(a,r)) w1 /\
     wan_gdir (ball(a,r)) G w1 <= e /\
     cm_harmonic S G (ball(a,r)) w0 /\ wan_w12 (ball(a,r)) w0 /\
     wan_gdir (ball(a,r)) G w0 <= e /\
     wan_w120 (ball(a,r)) (\x. w1 x - u1 x) /\ wan_w120 (ball(a,r)) (\x. w0 x - u0 x) /\
     (!x. x IN ball(a,r) ==> norm(u1 x - u0 x) <= delta) /\
     &16 * r pow 2 * (wan_dir (ball(a,r)) (\x. w1 x - w0 x) +
                      wan_dir (ball(a,r)) (\x. u1 x - u0 x)) +
     &2 * measure(ball(a,r)) * delta
     < (eps / &2) pow 2 * measure(ball(vec 0:real^2,min t (eps / (&2 * L))))
     ==> !x. x IN cball(a,r - &2 * t) ==> norm(w1 x - w0 x) < eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `eps <= norm((w1:real^2->real^K) x - w0 x)` THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((u1:real^2->real^K) a - u0 a)` THEN
    REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `C:num->real`;
                 `a:real^2`; `r:real`; `w1:real^2->real^K`; `t:real`; `e:real`]
                HMD_LIP_INTERIOR) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `C:num->real`;
                 `a:real^2`; `r:real`; `w0:real^2->real^K`; `t:real`; `e:real`]
                HMD_LIP_INTERIOR) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`\x. (w1:real^2->real^K) x - w0 x`; `a:real^2`; `r:real`; `t:real`; `L:real`;
                 `eps:real`; `x:real^2`] HMD_LIP_L2) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`p:real^2`; `q:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `norm((w1:real^2->real^K) p - w1 q) <= &2 * (C 1 * sqrt e / t) * norm(p - q) /\
        norm((w0:real^2->real^K) p - w0 q) <= &2 * (C 1 * sqrt e / t) * norm(p - q)`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `norm(((w1:real^2->real^K) p - w0 p) - (w1 q - w0 q)) <=
                    norm(w1 p - w1 q) + norm(w0 p - w0 q)` ASSUME_TAC THENL
       [CONV_TAC NORM_ARITH; ALL_TAC] THEN
      SUBGOAL_THEN `&4 * (C 1 * sqrt e / t) * norm(p - q:real^2) <= L * norm(p - q)`
      ASSUME_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC; NORM_POS_LE];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`ball(a:real^2,r)`; `w1:real^2->real^K`; `w0:real^2->real^K`]
                    WAN_W12_SUB) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[wan_w12]];
    ALL_TAC] THEN
  SUBST1_TAC(ISPECL [`x:real^2`; `vec 0:real^2`; `min t (eps / (&2 * L))`]
                    HMD_MEASURE_BALL_TRANSLATE) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `u1:real^2->real^K`; `w1:real^2->real^K`;
                 `u0:real^2->real^K`; `w0:real^2->real^K`; `delta:real`] HMD_L2_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `measure(ball(a:real^2,r)) * delta pow 2 <= measure(ball(a:real^2,r)) * delta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[MEASURE_POS_LE; MEASURABLE_BALL] THEN
    REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* CM Cor 3.4, Step 2 for a pair: for fixed (u0, w0) and eps > 0 there       *)
(* is eta > 0 such that sup |u1 - u0| <= eta and dir(u1 - u0) <= eta give   *)
(* sup |w1 - w0| < eps on the closed disc and dir(w1 - w0) < eps.          *)
(* ------------------------------------------------------------------------- *)

let HMD_UNIF_PAIR = prove
 (`!S (G:real^K->real^K^K) d e.
     hmd_ctx S G d e
     ==> !(a:real^2) r (u0:real^2->real^K) w0.
           &0 < r /\ cm_cmap S (ball(a,r)) u0 /\ wan_gdir (ball(a,r)) G u0 <= e /\
           cm_minimizer S G (ball(a,r)) w0 /\ cm_cmap S (ball(a,r)) w0 /\
           (!x. x IN sphere(a,r) ==> w0 x = u0 x)
           ==> !eps. &0 < eps
                     ==> ?eta. &0 < eta /\
                           !u1 w1. cm_cmap S (ball(a,r)) u1 /\
                                   wan_gdir (ball(a,r)) G u1 <= e /\
                                   cm_minimizer S G (ball(a,r)) w1 /\
                                   cm_cmap S (ball(a,r)) w1 /\
                                   (!x. x IN sphere(a,r) ==> w1 x = u1 x) /\
                                   (!x. x IN cball(a,r) ==> norm(u1 x - u0 x) <= eta) /\
                                   wan_dir (ball(a,r)) (\x. u1 x - u0 x) <= eta
                                   ==> (!x. x IN cball(a,r) ==> norm(w1 x - w0 x) < eps) /\
                                       wan_dir (ball(a,r)) (\x. w1 x - w0 x) < eps`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HMD_DIR_PAIR) THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real` (X_CHOOSE_THEN `D0:real` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [hmd_ctx]) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `C:num->real`]
                HMD_QBE_EX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `CQ:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  SUBGOAL_THEN `&0 <= Lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C 1` ASSUME_TAC THENL [ASM_MESON_TAC[hmd_epsreg]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u0:real^2->real^K`; `w0:real^2->real^K`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `a:real^2`;
                 `r:real`; `u0:real^2->real^K`; `w0:real^2->real^K`] HMD_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (u0:real^2->real^K) /\
                (u0:real^2->real^K) continuous_on cball(a,r)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `cm_cmap S (ball(a,r)) (u0:real^2->real^K)` THEN
    ASM_SIMP_TAC[HMD_CMAP_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(a,r)) G (w0:real^2->real^K) <= e` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  (* the modulus of continuity of u0 *)
  MP_TAC(ISPECL [`u0:real^2->real^K`; `cball(a:real^2,r)`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `eps / &8`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `du:real` STRIP_ASSUME_TAC) THEN
  (* the energy thresholds near the circle *)
  SUBGOAL_THEN `&0 <= Lam / lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < (eps / (&8 * CQ)) pow 2 /\
    CQ * sqrt((eps / (&8 * CQ)) pow 2) = eps / &8 /\
    &0 < (eps / (&8 * CQ)) pow 2 / (&2 * (&2 * Lam / lam + &1)) /\
    (&2 * Lam / lam + &1) * ((eps / (&8 * CQ)) pow 2 / (&2 * (&2 * Lam / lam + &1))) =
    (eps / (&8 * CQ)) pow 2 / &2`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 < eps / (&8 * CQ)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (eps / (&8 * CQ)) pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < CQ` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < &2 * Lam / lam + &1` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  ABBREV_TAC `TT = (eps / (&8 * CQ)) pow 2` THEN
  ABBREV_TAC `T0 = TT / (&2 * (&2 * Lam / lam + &1))` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &2 * Lam / lam * T0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * Lam / lam * T0 <= TT / &2 /\ T0 <= TT` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `ball(a:real^2,r)`;
                 `w0:real^2->real^K`; `T0:real`] HMD_ENERGY_UNIF_SMALL) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL [ASM_MESON_TAC[cm_harmonic]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho0:real` STRIP_ASSUME_TAC) THEN
  (* the width t of the annulus *)
  SUBGOAL_THEN
   `&0 < min (du / &4) (min (rho0 / &4) (r / &8)) /\
    &2 * min (du / &4) (min (rho0 / &4) (r / &8)) < du /\
    &4 * min (du / &4) (min (rho0 / &4) (r / &8)) <= rho0 /\
    &4 * min (du / &4) (min (rho0 / &4) (r / &8)) < r`
  MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = min (du / &4) (min (rho0 / &4) (r / &8))` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p q. p IN cball(a,r) /\ q IN cball(a,r) /\ norm(p - q) <= &2 * t
                      ==> norm((u0:real^2->real^K) p - u0 q) <= eps / &8`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`q:real^2`; `p:real^2`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `du:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[dist] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x0 rho'. &0 < rho' /\ rho' <= &4 * t
                          ==> wan_gdir (ball(a,r) INTER ball(x0,rho')) G
                                       (w0:real^2->real^K) <= T0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `rho0:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the interior constants *)
  SUBGOAL_THEN `&0 <= C 1 * sqrt e / t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_DIV; SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * (C 1 * sqrt e / t) + &1 /\
                &4 * (C 1 * sqrt e / t) <= &4 * (C 1 * sqrt e / t) + &1`
  MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = &4 * (C 1 * sqrt e / t) + &1` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < measure(ball(vec 0:real^2,min t (eps / (&2 * L))))` MP_TAC THENL
   [REWRITE_TAC[MEASURE_BALL_POS; REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m0 = measure(ball(vec 0:real^2,min t (eps / (&2 * L))))` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (eps / &2) pow 2 * m0` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `T2 = (eps / &2) pow 2 * m0` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= measure(ball(a:real^2,r))` MP_TAC THENL
   [SIMP_TAC[MEASURE_POS_LE; MEASURABLE_BALL]; ALL_TAC] THEN
  ABBREV_TAC `M = measure(ball(a:real^2,r))` THEN DISCH_TAC THEN
  (* the quotients *)
  SUBGOAL_THEN
   `&0 <= TT / (&4 * Lam + &1) /\ (&4 * Lam + &1) * (TT / (&4 * Lam + &1)) = TT /\
    &0 <= T2 / (&64 * r pow 2 + &1) /\
    (&64 * r pow 2 + &1) * (T2 / (&64 * r pow 2 + &1)) = T2 /\
    &0 <= T2 / (&8 * M + &1) /\ (&8 * M + &1) * (T2 / (&8 * M + &1)) = T2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &4 * Lam + &1 /\ &0 < &64 * r pow 2 + &1 /\ &0 < &8 * M + &1`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < min (eps / &2) (min (TT / (&4 * Lam + &1)) (T2 / (&64 * r pow 2 + &1))) /\
    min (eps / &2) (min (TT / (&4 * Lam + &1)) (T2 / (&64 * r pow 2 + &1))) <= eps / &2 /\
    min (eps / &2) (min (TT / (&4 * Lam + &1)) (T2 / (&64 * r pow 2 + &1)))
    <= TT / (&4 * Lam + &1) /\
    min (eps / &2) (min (TT / (&4 * Lam + &1)) (T2 / (&64 * r pow 2 + &1)))
    <= T2 / (&64 * r pow 2 + &1)`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 < TT / (&4 * Lam + &1) /\ &0 < T2 / (&64 * r pow 2 + &1)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
      MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `ddT = min (eps / &2) (min (TT / (&4 * Lam + &1)) (T2 / (&64 * r pow 2 + &1)))` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`A:real`; `ddT:real`] HMD_SMALL_ETA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `&0 < min eta1 (min D0 (min (eps / &8) (min (T2 / (&64 * r pow 2 + &1))
                                               (T2 / (&8 * M + &1))))) /\
    min eta1 (min D0 (min (eps / &8) (min (T2 / (&64 * r pow 2 + &1))
                                          (T2 / (&8 * M + &1))))) <= eta1 /\
    min eta1 (min D0 (min (eps / &8) (min (T2 / (&64 * r pow 2 + &1))
                                          (T2 / (&8 * M + &1))))) <= D0 /\
    min eta1 (min D0 (min (eps / &8) (min (T2 / (&64 * r pow 2 + &1))
                                          (T2 / (&8 * M + &1))))) <= eps / &8 /\
    min eta1 (min D0 (min (eps / &8) (min (T2 / (&64 * r pow 2 + &1))
                                          (T2 / (&8 * M + &1))))) <= T2 / (&64 * r pow 2 + &1) /\
    min eta1 (min D0 (min (eps / &8) (min (T2 / (&64 * r pow 2 + &1))
                                          (T2 / (&8 * M + &1))))) <= T2 / (&8 * M + &1)`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 < T2 / (&64 * r pow 2 + &1) /\ &0 < T2 / (&8 * M + &1)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
      MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `eta0 = min eta1 (min D0 (min (eps / &8) (min (T2 / (&64 * r pow 2 + &1))
                                                          (T2 / (&8 * M + &1)))))` THEN
  STRIP_TAC THEN
  EXISTS_TAC `eta0:real` THEN ASM_REWRITE_TAC[] THEN
  (* the pair (u1, w1) *)
  MAP_EVERY X_GEN_TAC [`u1:real^2->real^K`; `w1:real^2->real^K`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `a:real^2`;
                 `r:real`; `u1:real^2->real^K`; `w1:real^2->real^K`] HMD_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (u1:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_cmap]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(a,r)) G (w1:real^2->real^K) <= e` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= wan_dir (ball(a,r)) (\x. (u1:real^2->real^K) x - u0 x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(a,r)) (\x. (w1:real^2->real^K) x - w0 x) < ddT` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `A * (eta0 + sqrt(wan_dir (ball(a,r)) (\x. (u1:real^2->real^K) x - u0 x)) +
                     wan_dir (ball(a,r)) (\x. (u1:real^2->real^K) x - u0 x))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `D0:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ddT:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `r - &2 * t <= norm(x - a:real^2)` THENL
   [(* near the circle *)
    SUBGOAL_THEN `&2 * Lam * wan_dir (ball(a,r)) (\x. (w1:real^2->real^K) x - w0 x)
                  <= TT / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * Lam * (TT / (&4 * Lam + &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `CQ:real`; `lam:real`;
                   `Lam:real`; `a:real^2`; `r:real`; `u1:real^2->real^K`; `w1:real^2->real^K`;
                   `u0:real^2->real^K`; `w0:real^2->real^K`; `t:real`; `eta0:real`;
                   `eps:real`; `T0:real`] HMD_NEAR_BDRY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `CQ * sqrt TT` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    (* inside *)
    SUBGOAL_THEN `!x. x IN ball(a,r) ==> x IN cball(a:real^2,r)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SUBSET; BALL_SUBSET_CBALL]; ALL_TAC] THEN
    SUBGOAL_THEN `!x. x IN ball(a,r) ==> norm((u1:real^2->real^K) x - u0 x) <= eta0`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * t < r /\ eta0 <= &1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `r pow 2 * wan_dir (ball(a,r)) (\x. (w1:real^2->real^K) x - w0 x) <=
      r pow 2 * (T2 / (&64 * r pow 2 + &1)) /\
      r pow 2 * wan_dir (ball(a,r)) (\x. (u1:real^2->real^K) x - u0 x) <=
      r pow 2 * (T2 / (&64 * r pow 2 + &1)) /\
      M * eta0 <= M * (T2 / (&8 * M + &1))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `C:num->real`;
                   `a:real^2`; `r:real`; `u1:real^2->real^K`; `w1:real^2->real^K`;
                   `u0:real^2->real^K`; `w0:real^2->real^K`; `t:real`; `L:real`; `eps:real`;
                   `eta0:real`] HMD_INTERIOR_PAIR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN REWRITE_TAC[IN_CBALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `~(r - &2 * t <= norm(x - a:real^2))` THEN CONV_TAC NORM_ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* CM Cor 3.4, Step 2 for sequences, the context hmd_ctx from the chain      *)
(* hypotheses, CM_REPLACEMENT_STATEMENT and the chain theorem.               *)
(* ------------------------------------------------------------------------- *)

let HMD_P2 = prove
 (`!S (G:real^K->real^K^K) d e.
     hmd_ctx S G d e
     ==> !(a:real^2) r (u:num->real^2->real^K) u0 w w0.
           &0 < r /\
           (!n. cm_cmap S (ball(a,r)) (u n) /\ wan_gdir (ball(a,r)) G (u n) <= e /\
                cm_minimizer S G (ball(a,r)) (w n) /\ cm_cmap S (ball(a,r)) (w n) /\
                (!x. x IN sphere(a,r) ==> w n x = u n x)) /\
           cm_cmap S (ball(a,r)) u0 /\ wan_gdir (ball(a,r)) G u0 <= e /\
           cm_minimizer S G (ball(a,r)) w0 /\ cm_cmap S (ball(a,r)) w0 /\
           (!x. x IN sphere(a,r) ==> w0 x = u0 x) /\
           (!e'. &0 < e'
                 ==> eventually (\n. !x. x IN cball(a,r) ==> norm(u n x - u0 x) < e')
                                sequentially) /\
           ((\n. wan_dir (ball(a,r)) (\x. u n x - u0 x)) ---> &0) sequentially
           ==> (!e'. &0 < e'
                     ==> eventually (\n. !x. x IN cball(a,r) ==> norm(w n x - w0 x) < e')
                                    sequentially) /\
               ((\n. wan_dir (ball(a,r)) (\x. w n x - w0 x)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HMD_UNIF_PAIR) THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:num->real^2->real^K`; `u0:real^2->real^K`;
                       `w:num->real^2->real^K`; `w0:real^2->real^K`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `r:real`; `u0:real^2->real^K`;
                                `w0:real^2->real^K`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!eps. &0 < eps
          ==> ?N. !n. N <= n
                      ==> (!x. x IN cball(a,r)
                               ==> norm((w:num->real^2->real^K) n x - w0 x) < eps) /\
                          wan_dir (ball(a,r)) (\x. w n x - w0 x) < eps`
  ASSUME_TAC THENL
   [X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `eta:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `u0:real^2->real^K`)) (concl th) &&
      can (find_term ((=) `sequentially`)) (concl th))) THEN
    ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    UNDISCH_TAC `((\n. wan_dir (ball(a,r)) (\x. (u:num->real^2->real^K) n x - u0 x)) ---> &0)
                 sequentially` THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `eta:real`) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `eta:real`)) (concl th) &&
      can (find_term ((=) `w1:real^2->real^K`)) (concl th))) THEN
    EXISTS_TAC `(u:num->real^2->real^K) n` THEN REWRITE_TAC[ETA_AX] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `cm_minimizer:(real^K->bool)->(real^K->real^K^K)->(real^2->bool)->(real^2->real^K)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `N1:num`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `N2:num`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `e':real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e':real`) THEN ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    X_GEN_TAC `e':real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e':real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= wan_dir (ball(a,r)) (\x. (w:num->real^2->real^K) n x - w0 x)`
    MP_TAC THENL
     [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN
      SUBGOAL_THEN `!v:real^2->real^K. cm_cmap S (ball(a,r)) v ==> wan_w12 (ball(a,r)) v`
      ASSUME_TAC THENL [SIMP_TAC[cm_cmap]; ALL_TAC] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `cm_minimizer:(real^K->bool)->(real^K->real^K^K)->(real^2->bool)->(real^2->real^K)->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[ETA_AX];
      ASM_REAL_ARITH_TAC]]);;

let HMD_PG_HOLDS = prove
 (`HMD_PG_STATEMENT (:K)`,
  REWRITE_TAC[HMD_PG_STATEMENT; hmd_pgdata] THEN MATCH_ACCEPT_TAC HMR_PI_GLOBAL);;

let HMD_CTX_EXISTS = prove
 (`!S (G:real^K->real^K^K) d.
     WAN_RELLICH0_STATEMENT (:2) (:K) /\ WAN_GDIR_LSC_STATEMENT (:2) (:K) /\
     WAN_W120_CONT_STATEMENT (:2) (:K) /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
     CM_MINIMIZER_SMOOTH_STATEMENT (:K) /\ CM_EPS_REG_STATEMENT (:K) /\
     CM_CONVEXITY_STATEMENT (:K) /\ cm_target S G d
     ==> ?e. hmd_ctx S G d e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMD_CONVEX_FROM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` (X_CHOOSE_TAC `c:real`)) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMD_EPSREG_FROM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e2:real` (X_CHOOSE_TAC `C:num->real`)) THEN
  SUBGOAL_THEN `&0 < e1 /\ &0 < e2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[hmd_convex; hmd_epsreg]; ALL_TAC] THEN
  EXISTS_TAC `min e1 e2` THEN REWRITE_TAC[hmd_ctx] THEN
  ASM_REWRITE_TAC[HMD_PG_HOLDS; REAL_LT_MIN] THEN CONJ_TAC THENL
   [EXISTS_TAC `c:real` THEN MATCH_MP_TAC HMD_CONVEX_MONO THEN EXISTS_TAC `e1:real` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
    EXISTS_TAC `C:num->real` THEN MATCH_MP_TAC HMD_EPSREG_MONO THEN EXISTS_TAC `e2:real` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC]);;

let HMD_REPLACEMENT = prove
 (`WAN_RELLICH0_STATEMENT (:2) (:K) /\ WAN_GDIR_LSC_STATEMENT (:2) (:K) /\
   WAN_W120_CONT_STATEMENT (:2) (:K) /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
   CM_MINIMIZER_SMOOTH_STATEMENT (:K) /\ CM_EPS_REG_STATEMENT (:K) /\
   CM_CONVEXITY_STATEMENT (:K)
   ==> CM_REPLACEMENT_STATEMENT (:K)`,
  STRIP_TAC THEN REWRITE_TAC[CM_REPLACEMENT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMD_CTX_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `e:real`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HMD_ENERGY_EST) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [ASM_MESON_TAC[hmd_ctx]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `C:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real^K`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `a:real^2`;
                   `r:real`; `u:real^2->real^K`] HMD_SOLVE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:num->real^2->real^K`; `u0:real^2->real^K`;
                       `w:num->real^2->real^K`; `w0:real^2->real^K`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HMD_P2) THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^2`; `r:real`; `u:num->real^2->real^K`;
                             `u0:real^2->real^K`; `w:num->real^2->real^K`;
                             `w0:real^2->real^K`]) THEN
  ASM_REWRITE_TAC[]);;

let CM_CHAIN_HM_DIRICHLET = prove
 (`!kk:K->bool. CM_CHAIN_HM_DIRICHLET_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_CHAIN_HM_DIRICHLET_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC HMD_REPLACEMENT THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* CM_REPLACEMENT with the hypotheses WAN_RELLICH0 (pc_wan_sob2r),           *)
(* WAN_GDIR_LSC (pc_wan_sob2b) and CM_EPS_REG (pc_hm_reg_eps) discharged by  *)
(* their theorems; it keeps the other four hypotheses (WAN_W120_CONT,        *)
(* WAN_CHAIN_W12, CM_MINIMIZER_SMOOTH and CM_CONVEXITY).                     *)
(* ------------------------------------------------------------------------- *)

let HMD_REPLACEMENT_REDUCED = prove
 (`WAN_W120_CONT_STATEMENT (:2) (:K) /\ WAN_CHAIN_W12_STATEMENT (:2) (:K) (:K) /\
   CM_MINIMIZER_SMOOTH_STATEMENT (:K) /\ CM_CONVEXITY_STATEMENT (:K)
   ==> CM_REPLACEMENT_STATEMENT (:K)`,
  STRIP_TAC THEN MATCH_MP_TAC HMD_REPLACEMENT THEN
  ASM_REWRITE_TAC[WAN_RELLICH0; WAN_GDIR_LSC; CM_EPS_REG]);;

