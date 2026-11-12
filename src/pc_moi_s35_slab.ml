(* ========================================================================= *)
(* pc_moi_s35_slab: the Sec 35 unit s35_slab (pc_moi_s35_stmt.ml), main      *)
(* theorem SLAB_PRODUCT = MOI_S35_SLAB_PRODUCT: the part of a finite         *)
(* complex of dimension at most 2 in real^3 between two levels with no       *)
(* vertex is a PL product (Moise p.250 push-offs).  Each crossing triangle   *)
(* meets the slab in a trapezoid, parametrized by a level-preserving PL map  *)
(* split along a diagonal; crossing edges give straight paths.               *)
(* ========================================================================= *)

needs "src/pc_moi_s35_stmt.ml";;
needs "src/pc_moi_ptri.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The trapezoid map.  p1, p2 at the lower level, q1, q2 at the upper one,  *)
(* p2 = p1 + alpha % w and q2 = q1 + beta % w (alpha, beta > 0).  For x on  *)
(* segment[p1,p2] with coordinate mu x along w, the point at time s is      *)
(* x + max(s - mu x, 0) % (q1 - p1) + min(mu x, s) % (q2 - p2), affine on   *)
(* each of the two triangles mu <= s and mu >= s.                           *)
(* ------------------------------------------------------------------------- *)

let moi_s5s_pt = new_definition
 `moi_s5s_pt (a:real^3) (b:real^3) t = a + ((t - a$3) / (b$3 - a$3)) % (b - a)`;;

let moi_s5s_mu = new_definition
 `moi_s5s_mu (p1:real^3) (w:real^3) alpha (x:real^3) =
    ((x - p1) dot w) / (alpha * (w dot w))`;;

let moi_s5s_trap = new_definition
 `moi_s5s_trap (p1:real^3) (p2:real^3) (q1:real^3) (q2:real^3) (w:real^3) alpha
               (z:real^(3,1)finite_sum) =
    fstcart z +
    max (drop(sndcart z) - moi_s5s_mu p1 w alpha (fstcart z)) (&0) % (q1 - p1) +
    min (moi_s5s_mu p1 w alpha (fstcart z)) (drop(sndcart z)) % (q2 - p2)`;;

let MOI_S5S_MU_SEG = prove
 (`!(p1:real^3) w alpha x.
     ~(w = vec 0) /\ &0 < alpha /\ x IN segment[p1,p1 + alpha % w]
     ==> &0 <= moi_s5s_mu p1 w alpha x /\ moi_s5s_mu p1 w alpha x <= &1 /\
         x = p1 + (alpha * moi_s5s_mu p1 w alpha x) % w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `moi_s5s_mu p1 w alpha (x:real^3) = u` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[moi_s5s_mu] THEN
    REWRITE_TAC[VECTOR_ARITH `((&1 - u) % p1 + u % (p1 + a % w)) - p1:real^3 =
                              (u * a) % w`] THEN
    REWRITE_TAC[DOT_LMUL] THEN
    SUBGOAL_THEN `~((w:real^3) dot w = &0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
    SUBGOAL_THEN `~(alpha = &0)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `~(a = &0) /\ ~(ww = &0) ==> ((u * a) * ww) / (a * ww) = u`];
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

let MOI_S5S_KAPPA = prove
 (`!alpha beta mu s.
     &0 < alpha /\ &0 < beta /\ &0 <= mu /\ mu <= &1 /\ &0 <= s /\ s <= &1
     ==> &0 <= alpha * mu + min mu s * (beta - alpha) /\
         alpha * mu + min mu s * (beta - alpha) <= alpha + s * (beta - alpha) /\
         &0 < alpha + s * (beta - alpha)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= alpha * s /\ alpha * s <= alpha /\ &0 <= beta * mu /\
                &0 <= alpha * mu /\ alpha * mu <= alpha` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < alpha + s * (beta - alpha)` ASSUME_TAC THENL
   [ASM_CASES_TAC `s = &1` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < (&1 - s) * alpha /\ &0 <= s * beta` MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `mu <= s` THENL
   [ASM_SIMP_TAC[REAL_ARITH `mu <= s ==> min mu s = mu`] THEN
    SUBGOAL_THEN `beta * mu <= beta * s` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_ARITH `~(mu <= s) ==> min mu s = s`] THEN
    SUBGOAL_THEN `alpha * s <= alpha * mu /\ beta * s <= beta /\ &0 <= beta * s`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_S5S_KAPPA_MONO = prove
 (`!alpha beta mu mu' s.
     &0 < alpha /\ &0 < beta /\ mu < mu'
     ==> alpha * mu + min mu s * (beta - alpha) <
         alpha * mu' + min mu' s * (beta - alpha)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `mu' <= s` THENL
   [SUBGOAL_THEN `mu <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `!a b. a <= b ==> min a b = a`] THEN
    SUBGOAL_THEN `beta * mu < beta * mu'` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `mu <= s` THENL
   [ASM_SIMP_TAC[REAL_ARITH `~(mu' <= s) ==> min mu' s = s`;
                 REAL_ARITH `mu <= s ==> min mu s = mu`] THEN
    SUBGOAL_THEN `beta * mu <= beta * s /\ alpha * s < alpha * mu'` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_ARITH `~(mu' <= s) ==> min mu' s = s`;
                 REAL_ARITH `~(mu <= s) ==> min mu s = s`] THEN
    SUBGOAL_THEN `alpha * mu < alpha * mu'` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* PL-ness of the trapezoid map: affine pieces, scaled PL scalars, max/min. *)
(* ------------------------------------------------------------------------- *)

let MOI_S5S_SCALE_PL = prove
 (`!s (g:real^M->real^1) (v:real^N).
     pl_map_on s g ==> pl_map_on s (\x. drop(g x) % v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^M. drop(g x) % (v:real^N)) = (\y. drop y % v) o g`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^1)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\y:real^1. (\y. drop y % (v:real^N)) y + vec 0` THEN
  CONJ_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
  MP_TAC(ISPECL [`\x:real^1. x`; `v:real^N`] LINEAR_VMUL_DROP) THEN
  REWRITE_TAC[LINEAR_ID]);;

let MOI_S5S_MU_PL = prove
 (`!s (p1:real^3) w alpha.
     locally_polyhedral (s:real^(3,1)finite_sum->bool)
     ==> pl_map_on s (\z. lift(moi_s5s_mu p1 w alpha (fstcart z)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC
   `\z:real^(3,1)finite_sum.
      (\z. inv(alpha * (w dot w)) % lift(w dot fstcart z)) z +
      lift(--(inv(alpha * (w dot w)) * (w dot p1)))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    REWRITE_TAC[moi_s5s_mu; GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN
    REWRITE_TAC[DOT_LSUB; real_div] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
  SUBGOAL_THEN `(\z:real^(3,1)finite_sum. lift((w:real^3) dot fstcart z)) =
                (\x. lift(w dot x)) o fstcart` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[LINEAR_FSTCART; LINEAR_LIFT_DOT]);;

let MOI_S5S_TRAP_PL = prove
 (`!(p1:real^3) p2 q1 q2 w alpha.
     pl_map_on (segment[p1,p2] PCROSS interval[vec 0:real^1,vec 1])
               (moi_s5s_trap p1 p2 q1 q2 w alpha)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `dd = segment[p1:real^3,p2] PCROSS interval[vec 0:real^1,vec 1]` THEN
  SUBGOAL_THEN `locally_polyhedral (dd:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
    MATCH_MP_TAC POLYTOPE_PCROSS THEN REWRITE_TAC[POLYTOPE_SEGMENT; POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (dd:real^(3,1)finite_sum->bool) sndcart`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^(3,1)finite_sum. (sndcart:real^(3,1)finite_sum->real^1) z + vec 0` THEN
    CONJ_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[LINEAR_SNDCART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dd:real^(3,1)finite_sum->bool`; `p1:real^3`; `w:real^3`; `alpha:real`]
    MOI_S5S_MU_PL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC
   `\z:real^(3,1)finite_sum.
      fstcart z +
      max (drop(sndcart z) - moi_s5s_mu p1 w alpha (fstcart z)) (&0) % (q1 - p1) +
      min (moi_s5s_mu p1 w alpha (fstcart z)) (drop(sndcart z)) % (q2 - p2)` THEN
  CONJ_TAC THENL [REWRITE_TAC[moi_s5s_trap]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^(3,1)finite_sum. (fstcart:real^(3,1)finite_sum->real^3) z + vec 0` THEN
    CONJ_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[LINEAR_FSTCART];
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_ADD THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`dd:real^(3,1)finite_sum->bool`;
      `\z:real^(3,1)finite_sum. lift(max (drop(sndcart z) - moi_s5s_mu p1 w alpha (fstcart z)) (&0))`;
      `q1 - p1:real^3`] MOI_S5S_SCALE_PL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`dd:real^(3,1)finite_sum->bool`;
      `\z:real^(3,1)finite_sum. lift(drop(sndcart z)) - lift(moi_s5s_mu p1 w alpha (fstcart z))`;
      `\z:real^(3,1)finite_sum. lift(&0)`] PL_MAP_ON_LIFT_MAX) THEN
    REWRITE_TAC[DROP_SUB; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PL_MAP_ON_CONST] THEN
    REWRITE_TAC[VECTOR_ARITH `(x:real^1) - y = x + (--(&1)) % y`] THEN
    MATCH_MP_TAC PL_MAP_ON_ADD THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC PL_MAP_ON_CMUL THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`dd:real^(3,1)finite_sum->bool`;
      `\z:real^(3,1)finite_sum. lift(min (moi_s5s_mu p1 w alpha (fstcart z)) (drop(sndcart z)))`;
      `q2 - p2:real^3`] MOI_S5S_SCALE_PL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`dd:real^(3,1)finite_sum->bool`;
      `\z:real^(3,1)finite_sum. lift(moi_s5s_mu p1 w alpha (fstcart z))`;
      `\z:real^(3,1)finite_sum. lift(drop(sndcart z))`] PL_MAP_ON_LIFT_MIN) THEN
    ASM_REWRITE_TAC[LIFT_DROP; ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* The trapezoid map: normal form, level, bottom, sides, injectivity, image. *)
(* ------------------------------------------------------------------------- *)

let MOI_S5S_TRAP_FORM = prove
 (`!(p1:real^3) p2 q1 q2 w alpha beta x s.
     ~(w = vec 0) /\ &0 < alpha /\ p2 = p1 + alpha % w /\ q2 = q1 + beta % w /\
     x IN segment[p1,p2]
     ==> moi_s5s_trap p1 p2 q1 q2 w alpha (pastecart x s) =
         (p1 + drop s % (q1 - p1)) +
         (alpha * moi_s5s_mu p1 w alpha x +
          min (moi_s5s_mu p1 w alpha x) (drop s) * (beta - alpha)) % w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `p2 = p1 + alpha % (w:real^3)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `q2 = q1 + beta % (w:real^3)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`p1:real^3`; `w:real^3`; `alpha:real`; `x:real^3`] MOI_S5S_MU_SEG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "xe"))) THEN
  REWRITE_TAC[moi_s5s_trap; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[REAL_ARITH `max (s - m) (&0) = s - min m s`] THEN
  USE_THEN "xe" (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
  VECTOR_ARITH_TAC);;

let MOI_S5S_MU_ENDS = prove
 (`!(p1:real^3) w alpha.
     ~(w = vec 0) /\ &0 < alpha
     ==> moi_s5s_mu p1 w alpha p1 = &0 /\
         moi_s5s_mu p1 w alpha (p1 + alpha % w) = &1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s5s_mu; VECTOR_SUB_REFL; DOT_LZERO; real_div; REAL_MUL_LZERO;
              VECTOR_ARITH `(p1 + a % w) - p1:real^3 = a % w`; DOT_LMUL] THEN
  SUBGOAL_THEN `~((w:real^3) dot w = &0) /\ ~(alpha = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_DIV_REFL; REAL_ENTIRE]);;

let MOI_S5S_TRAP_BASIC = prove
 (`!(p1:real^3) p2 q1 q2 w alpha beta c d.
     ~(w = vec 0) /\ &0 < alpha /\ &0 < beta /\
     p2 = p1 + alpha % w /\ q2 = q1 + beta % w /\
     p1$3 = c /\ q1$3 = d /\ w$3 = &0
     ==> (!x s. x IN segment[p1,p2]
                ==> (moi_s5s_trap p1 p2 q1 q2 w alpha (pastecart x s))$3 =
                    c + drop s * (d - c)) /\
         (!x. x IN segment[p1,p2]
              ==> moi_s5s_trap p1 p2 q1 q2 w alpha (pastecart x (vec 0)) = x) /\
         (!s. s IN interval[vec 0,vec 1]
              ==> moi_s5s_trap p1 p2 q1 q2 w alpha (pastecart p1 s) =
                  p1 + drop s % (q1 - p1) /\
                  moi_s5s_trap p1 p2 q1 q2 w alpha (pastecart p2 s) =
                  p2 + drop s % (q2 - p2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p1:real^3`; `w:real^3`; `alpha:real`] MOI_S5S_MU_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p1:real^3`; `p2:real^3`; `q1:real^3`; `q2:real^3`; `w:real^3`;
                   `alpha:real`; `beta:real`; `x:real^3`; `s:real^1`] MOI_S5S_TRAP_FORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p1:real^3`; `p2:real^3`; `q1:real^3`; `q2:real^3`; `w:real^3`;
                   `alpha:real`; `beta:real`; `x:real^3`; `vec 0:real^1`] MOI_S5S_TRAP_FORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`p1:real^3`; `w:real^3`; `alpha:real`; `x:real^3`] MOI_S5S_MU_SEG) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "xe"))) THEN
    REWRITE_TAC[DROP_VEC] THEN
    SUBGOAL_THEN `min (moi_s5s_mu p1 w alpha (x:real^3)) (&0) = &0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "xe" (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    VECTOR_ARITH_TAC;
    X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`p1:real^3`; `p2:real^3`; `q1:real^3`; `q2:real^3`; `w:real^3`;
                     `alpha:real`; `beta:real`; `p1:real^3`; `s:real^1`] MOI_S5S_TRAP_FORM) THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> min (&0) s = &0`] THEN VECTOR_ARITH_TAC;
      MP_TAC(ISPECL [`p1:real^3`; `p2:real^3`; `q1:real^3`; `q2:real^3`; `w:real^3`;
                     `alpha:real`; `beta:real`; `p2:real^3`; `s:real^1`] MOI_S5S_TRAP_FORM) THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[REAL_ARITH `s <= &1 ==> min (&1) s = s`] THEN VECTOR_ARITH_TAC]]);;

let MOI_S5S_MU_POINT = prove
 (`!(p1:real^3) w alpha m.
     ~(w = vec 0) /\ &0 < alpha
     ==> moi_s5s_mu p1 w alpha (p1 + (alpha * m) % w) = m /\
         (&0 <= m /\ m <= &1 ==> p1 + (alpha * m) % w IN segment[p1,p1 + alpha % w])`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[moi_s5s_mu; VECTOR_ARITH `(p1 + a % w) - p1:real^3 = a % w`; DOT_LMUL] THEN
    SUBGOAL_THEN `~((w:real^3) dot w = &0) /\ ~(alpha = &0)` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `~(a = &0) /\ ~(ww = &0) ==> ((a * m) * ww) / (a * ww) = m`];
    REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `m:real` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

let MOI_S5S_TRAP_INJ = prove
 (`!(p1:real^3) p2 q1 q2 w alpha beta c d.
     ~(w = vec 0) /\ &0 < alpha /\ &0 < beta /\
     p2 = p1 + alpha % w /\ q2 = q1 + beta % w /\
     p1$3 = c /\ q1$3 = d /\ w$3 = &0 /\ c < d
     ==> !z z'. z IN segment[p1,p2] PCROSS interval[vec 0,vec 1] /\
                z' IN segment[p1,p2] PCROSS interval[vec 0,vec 1] /\
                moi_s5s_trap p1 p2 q1 q2 w alpha z =
                moi_s5s_trap p1 p2 q1 q2 w alpha z'
                ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p1:real^3`; `p2:real^3`; `q1:real^3`; `q2:real^3`; `w:real^3`;
                 `alpha:real`; `beta:real`; `c:real`; `d:real`] MOI_S5S_TRAP_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lev") (K ALL_TAC)) THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real^1`; `x':real^3`; `s':real^1`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `s:real^1 = s'` SUBST_ALL_TAC THENL
   [USE_THEN "lev" (fun th -> MP_TAC(MATCH_MP (SPECL [`x:real^3`; `s:real^1`] th)
      (ASSUME `(x:real^3) IN segment[p1,p1 + alpha % w]`))) THEN
    USE_THEN "lev" (fun th -> MP_TAC(MATCH_MP (SPECL [`x':real^3`; `s':real^1`] th)
      (ASSUME `(x':real^3) IN segment[p1,p1 + alpha % w]`))) THEN
    UNDISCH_TAC
     `moi_s5s_trap p1 (p1 + alpha % w) q1 (q1 + beta % w) w alpha
                   (pastecart (x:real^3) (s:real^1)) =
      moi_s5s_trap p1 (p1 + alpha % w) q1 (q1 + beta % w) w alpha
                   (pastecart (x':real^3) (s':real^1))` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_EQ_ADD_LCANCEL] THEN
    ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL; REAL_ARITH `c < d ==> ~(d - c = &0)`; DROP_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PASTECART_INJ] THEN
  MP_TAC(ISPECL [`p1:real^3`; `w:real^3`; `alpha:real`; `x:real^3`] MOI_S5S_MU_SEG) THEN
  MP_TAC(ISPECL [`p1:real^3`; `w:real^3`; `alpha:real`; `x':real^3`] MOI_S5S_MU_SEG) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "x'e"))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "xe"))) THEN
  SUBGOAL_THEN `moi_s5s_mu p1 w alpha (x:real^3) = moi_s5s_mu p1 w alpha x'`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `moi_s5s_trap p1 (p1 + alpha % w) q1 (q1 + beta % w) w alpha
                   (pastecart (x:real^3) (s':real^1)) =
      moi_s5s_trap p1 (p1 + alpha % w) q1 (q1 + beta % w) w alpha
                   (pastecart (x':real^3) (s':real^1))` THEN
    MP_TAC(ISPECL [`p1:real^3`; `p2:real^3`; `q1:real^3`; `q2:real^3`; `w:real^3`;
                   `alpha:real`; `beta:real`; `x:real^3`; `s':real^1`] MOI_S5S_TRAP_FORM) THEN
    MP_TAC(ISPECL [`p1:real^3`; `p2:real^3`; `q1:real^3`; `q2:real^3`; `w:real^3`;
                   `alpha:real`; `beta:real`; `x':real^3`; `s':real^1`] MOI_S5S_TRAP_FORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `a + x % w:real^3 = a + y % w <=> x % w = y % w`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(m < m' ==> k < k') /\ (m' < m ==> k' < k) ==> k = k' ==> m = m'`) THEN
    CONJ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S5S_KAPPA_MONO THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "xe" SUBST1_TAC THEN USE_THEN "x'e" SUBST1_TAC THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5S_KAPPA_ONTO = prove
 (`!alpha beta s k.
     &0 < alpha /\ &0 < beta /\ &0 <= s /\ s <= &1 /\
     &0 <= k /\ k <= alpha + s * (beta - alpha)
     ==> ?mu. &0 <= mu /\ mu <= &1 /\ alpha * mu + min mu s * (beta - alpha) = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `k <= s * beta` THENL
   [EXISTS_TAC `k / beta` THEN
    SUBGOAL_THEN `k / beta <= s` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE;
                 REAL_ARITH `m <= s ==> min m s = m`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < beta` THEN CONV_TAC REAL_FIELD;
    EXISTS_TAC `(k - s * (beta - alpha)) / alpha` THEN
    SUBGOAL_THEN `s <= (k - s * (beta - alpha)) / alpha` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `s <= m ==> min m s = s`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < alpha` THEN CONV_TAC REAL_FIELD]]);;

let MOI_S5S_SEG_ALONG = prove
 (`!(a:real^3) w phi y.
     &0 < phi
     ==> (y IN segment[a,a + phi % w] <=>
          ?k. &0 <= k /\ k <= phi /\ y = a + k % w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u * phi` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k / phi` THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - u) % a + u % (a + p % w):real^3 = a + (u * p) % w`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]]);;

let MOI_S5S_TRAP_IMAGE = prove
 (`!(p1:real^3) p2 q1 q2 w alpha beta.
     ~(w = vec 0) /\ &0 < alpha /\ &0 < beta /\
     p2 = p1 + alpha % w /\ q2 = q1 + beta % w
     ==> IMAGE (moi_s5s_trap p1 p2 q1 q2 w alpha)
               (segment[p1,p2] PCROSS interval[vec 0,vec 1]) =
         {y | ?s. s IN interval[vec 0,vec 1] /\
                  y IN segment[p1 + drop s % (q1 - p1), p2 + drop s % (q2 - p2)]}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. p2 + drop s % (q2 - p2) =
        (p1 + drop s % (q1 - p1)) + (alpha + drop s * (beta - alpha)) % (w:real^3)`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `s:real^1`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `s:real^1` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p1:real^3`; `w:real^3`; `alpha:real`; `x:real^3`] MOI_S5S_MU_SEG) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`alpha:real`; `beta:real`; `moi_s5s_mu p1 w alpha (x:real^3)`;
                   `drop(s:real^1)`] MOI_S5S_KAPPA) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MOI_S5S_SEG_ALONG] THEN
    EXISTS_TAC `alpha * moi_s5s_mu p1 w alpha (x:real^3) +
                min (moi_s5s_mu p1 w alpha x) (drop(s:real^1)) * (beta - alpha)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5S_TRAP_FORM THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`alpha:real`; `beta:real`; `&0`; `drop(s:real^1)`] MOI_S5S_KAPPA) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_01] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p1 + drop s % (q1 - p1):real^3`; `w:real^3`;
                   `alpha + drop s * (beta - alpha)`; `y:real^3`] MOI_S5S_SEG_ALONG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`alpha:real`; `beta:real`; `drop(s:real^1)`; `k:real`]
      MOI_S5S_KAPPA_ONTO) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`p1:real^3`; `w:real^3`; `alpha:real`; `m:real`] MOI_S5S_MU_POINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `p1 + (alpha * m) % w IN segment[p1:real^3,p2]` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`p1 + (alpha * m) % w:real^3`; `s:real^1`] THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    MP_TAC(ISPECL [`p1:real^3`; `p2:real^3`; `q1:real^3`; `q2:real^3`; `w:real^3`;
                   `alpha:real`; `beta:real`; `p1 + (alpha * m) % w:real^3`; `s:real^1`]
      MOI_S5S_TRAP_FORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Points at a given level on a segment, and level slices of a triangle      *)
(* whose apex is on the other side of the level from the two base points.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S5S_PT_HEIGHT = prove
 (`!(a:real^3) b t. ~(a$3 = b$3) ==> (moi_s5s_pt a b t)$3 = t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s5s_pt; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_SUB_COMPONENT] THEN
  UNDISCH_TAC `~((a:real^3)$3 = (b:real^3)$3)` THEN CONV_TAC REAL_FIELD);;

let MOI_S5S_PT_SYM = prove
 (`!(a:real^3) b t. ~(a$3 = b$3) ==> moi_s5s_pt a b t = moi_s5s_pt b a t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s5s_pt; VECTOR_ARITH
   `a + x % (b - a):real^3 = b + y % (a - b) <=> (&1 - x - y) % (a - b) = vec 0`] THEN
  SUBGOAL_THEN `&1 - (t - (a:real^3)$3) / ((b:real^3)$3 - a$3) - (t - b$3) / (a$3 - b$3) = &0`
    (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
  UNDISCH_TAC `~((a:real^3)$3 = (b:real^3)$3)` THEN CONV_TAC REAL_FIELD);;

let MOI_S5S_PT_AFFINE = prove
 (`!(a:real^3) b c d s.
     moi_s5s_pt a b (c + s * (d - c)) =
     moi_s5s_pt a b c + s % (moi_s5s_pt a b d - moi_s5s_pt a b c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5s_pt] THEN
  REWRITE_TAC[VECTOR_ARITH
   `a + x % (b - a):real^3 = (a + y % (b - a)) + s % ((a + z % (b - a)) - (a + y % (b - a))) <=>
    (x - y - s * (z - y)) % (b - a) = vec 0`] THEN
  MATCH_MP_TAC(MESON[VECTOR_MUL_LZERO] `x = &0 ==> x % (v:real^3) = vec 0`) THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let MOI_S5S_PT_IN_SEGMENT = prove
 (`!(a:real^3) b t.
     (a$3 <= t /\ t <= b$3 \/ b$3 <= t /\ t <= a$3) /\ ~(a$3 = b$3)
     ==> moi_s5s_pt a b t IN segment[a,b]`,
  SUBGOAL_THEN
   `!(a:real^3) b t. a$3 <= t /\ t <= b$3 /\ a$3 < b$3
                     ==> moi_s5s_pt a b t IN segment[a,b]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT; moi_s5s_pt] THEN
    EXISTS_TAC `(t - (a:real^3)$3) / ((b:real^3)$3 - a$3)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `moi_s5s_pt (a:real^3) b t = moi_s5s_pt b a t` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_S5S_PT_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_S5S_SEG_HEIGHT = prove
 (`!(a:real^3) b y.
     y IN segment[a,b] /\ ~(a$3 = b$3) ==> y = moi_s5s_pt a b (y$3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[moi_s5s_pt; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SUBGOAL_THEN
   `(((&1 - u) * (a:real^3)$3 + u * (b:real^3)$3) - a$3) / (b$3 - a$3) = u`
  SUBST1_TAC THENL
   [UNDISCH_TAC `~((a:real^3)$3 = (b:real^3)$3)` THEN CONV_TAC REAL_FIELD;
    VECTOR_ARITH_TAC]);;

let MOI_S5S_CS_SCALAR = prove
 (`!tau d1 d2 v1 v2.
     ~(tau = &0) /\ &0 < d1 / tau /\ &0 < d2 / tau /\
     v1 * d1 + v2 * d2 = tau /\ &0 <= v1 /\ &0 <= v2
     ==> &0 <= v2 * d2 / tau /\ v2 * d2 / tau <= &1 /\
         (&1 - v2 * d2 / tau) * (tau / d1) = v1 /\
         (v2 * d2 / tau) * (tau / d2) = v2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(d1 = &0) /\ ~(d2 = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `&0 < d1 / tau` THEN UNDISCH_TAC `&0 < d2 / tau` THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 - v2 * d2 / tau = v1 * (d1 / tau)` ASSUME_TAC THENL
   [UNDISCH_TAC `v1 * d1 + v2 * d2 = tau` THEN UNDISCH_TAC `~(tau = &0)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `v2 * d2 / tau = v2 * (d2 / tau)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v1 * (d1 / tau) /\ &0 <= v2 * (d2 / tau)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&1 - v2 * d2 / tau = v1 * (d1 / tau)` THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 <= v2 * (d2 / tau)` THEN REWRITE_TAC[real_div];
    UNDISCH_TAC `&0 <= v1 * (d1 / tau)` THEN REWRITE_TAC[real_div] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(tau = &0)` THEN
    UNDISCH_TAC `~(d1 = &0)` THEN CONV_TAC REAL_FIELD;
    UNDISCH_TAC `~(tau = &0)` THEN UNDISCH_TAC `~(d2 = &0)` THEN
    CONV_TAC REAL_FIELD]);;

let MOI_S5S_DIV_NEG2 = prove
 (`!x y. x / y = (--x) / (--y)`,
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]);;

let MOI_S5S_CONE_SLICE = prove
 (`!(ap:real^3) r1 r2 t.
     (ap$3 < t /\ t < r1$3 /\ t < r2$3) \/ (r1$3 < t /\ r2$3 < t /\ t < ap$3)
     ==> {y | y IN convex hull {ap,r1,r2} /\ y$3 = t} =
         segment[moi_s5s_pt ap r1 t, moi_s5s_pt ap r2 t]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `~(t - (ap:real^3)$3 = &0) /\
    &0 < ((r1:real^3)$3 - ap$3) / (t - ap$3) /\
    &0 < ((r2:real^3)$3 - ap$3) / (t - ap$3) /\
    ~(ap$3 = r1$3) /\ ~(ap$3 = r2$3) /\
    (ap$3 <= t /\ t <= r1$3 \/ r1$3 <= t /\ t <= ap$3) /\
    (ap$3 <= t /\ t <= r2$3 \/ r2$3 <= t /\ t <= ap$3)`
  (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THEN REPEAT CONJ_TAC THEN
    TRY ASM_REAL_ARITH_TAC THEN
    TRY(MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC) THEN
    ONCE_REWRITE_TAC[MOI_S5S_DIV_NEG2] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v1:real`
      (X_CHOOSE_THEN `v2:real` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
    SUBGOAL_THEN `u = &1 - v1 - v2` SUBST_ALL_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `v1 * ((r1:real^3)$3 - (ap:real^3)$3) + v2 * ((r2:real^3)$3 - ap$3) = t - ap$3`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3)$3 = t` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t - (ap:real^3)$3`; `(r1:real^3)$3 - (ap:real^3)$3`;
                   `(r2:real^3)$3 - (ap:real^3)$3`; `v1:real`; `v2:real`] MOI_S5S_CS_SCALAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_SEGMENT; moi_s5s_pt] THEN
    EXISTS_TAC `v2 * ((r2:real^3)$3 - (ap:real^3)$3) / (t - ap$3)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - p) % (a + x % (r - a)) + p % (a + z % (q - a)):real^3 =
      a + ((&1 - p) * x) % (r - a) + (p * z) % (q - a)`] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN segment[moi_s5s_pt ap r1 t,moi_s5s_pt ap r2 t]` THEN
      SPEC_TAC(`y:real^3`,`y:real^3`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] (ISPEC `{ap:real^3,r1,r2}`
        CONVEX_CONVEX_HULL)) THEN
      CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THENL
       [EXISTS_TAC `segment[ap:real^3,r1]`; EXISTS_TAC `segment[ap:real^3,r2]`] THEN
      ASM_SIMP_TAC[MOI_S5S_PT_IN_SEGMENT] THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN segment[moi_s5s_pt ap r1 t,moi_s5s_pt ap r2 t]` THEN
      REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; MOI_S5S_PT_HEIGHT] THEN
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Crossing triangles (canonical data: apex alone on its side, base points  *)
(* in lexicographic order) and crossing edges; their trapezoid data.        *)
(* ------------------------------------------------------------------------- *)

let moi_s5s_lexlt = new_definition
 `moi_s5s_lexlt (x:real^3) (y:real^3) <=>
    x$1 < y$1 \/ (x$1 = y$1 /\ (x$2 < y$2 \/ (x$2 = y$2 /\ x$3 < y$3)))`;;

let moi_s5s_tri = new_definition
 `moi_s5s_tri (k:(real^3->bool)->bool) c d (ap:real^3) r1 r2 <=>
    convex hull {ap,r1,r2} IN k /\ ~affine_dependent {ap,r1,r2} /\
    moi_s5s_lexlt r1 r2 /\
    ((ap$3 < c /\ d < r1$3 /\ d < r2$3) \/ (r1$3 < c /\ r2$3 < c /\ d < ap$3))`;;

let moi_s5s_edge = new_definition
 `moi_s5s_edge (k:(real^3->bool)->bool) c d (a:real^3) b <=>
    segment[a,b] IN k /\ a$3 < c /\ d < b$3`;;

let moi_s5s_w = new_definition
 `moi_s5s_w (ap:real^3) r1 r2 =
    (if ap$3 < r1$3 then &1 else -- &1) %
    (inv(r2$3 - ap$3) % (r2 - ap) - inv(r1$3 - ap$3) % (r1 - ap))`;;

let MOI_S5S_LEX_TOTAL = prove
 (`!x y:real^3. ~(x = y) ==> moi_s5s_lexlt x y \/ moi_s5s_lexlt y x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; moi_s5s_lexlt] THEN
  REAL_ARITH_TAC);;

let MOI_S5S_LEX_ASYM = prove
 (`!x y:real^3. ~(moi_s5s_lexlt x y /\ moi_s5s_lexlt y x)`,
  REWRITE_TAC[moi_s5s_lexlt] THEN REAL_ARITH_TAC);;

let MOI_S5S_TRI_DATA = prove
 (`!(k:(real^3->bool)->bool) c d ap r1 r2.
     c < d /\ moi_s5s_tri k c d ap r1 r2
     ==> ~(moi_s5s_w ap r1 r2 = vec 0) /\ &0 < abs(c - ap$3) /\ &0 < abs(d - ap$3) /\
         moi_s5s_pt ap r2 c =
         moi_s5s_pt ap r1 c + abs(c - ap$3) % moi_s5s_w ap r1 r2 /\
         moi_s5s_pt ap r2 d =
         moi_s5s_pt ap r1 d + abs(d - ap$3) % moi_s5s_w ap r1 r2 /\
         (moi_s5s_pt ap r1 c)$3 = c /\ (moi_s5s_pt ap r1 d)$3 = d /\
         (moi_s5s_w ap r1 r2)$3 = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5s_tri] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  (SUBGOAL_THEN `~((ap:real^3)$3 = (r1:real^3)$3) /\ ~(ap$3 = (r2:real^3)$3)`
   STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[MOI_S5S_PT_HEIGHT] THEN
  (SUBGOAL_THEN
    `!t. moi_s5s_pt (ap:real^3) r2 t - moi_s5s_pt ap r1 t =
         (t - ap$3) % (inv(r2$3 - ap$3) % (r2 - ap) - inv(r1$3 - ap$3) % (r1 - ap))`
   ASSUME_TAC THENL
    [GEN_TAC THEN REWRITE_TAC[moi_s5s_pt; real_div] THEN VECTOR_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `!t. (if (ap:real^3)$3 < c then t - ap$3 else ap$3 - t) *
         ((if ap$3 < (r1:real^3)$3 then &1 else -- &1)) = t - ap$3`
   ASSUME_TAC THENL
    [GEN_TAC THEN COND_CASES_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s5s_w; VECTOR_MUL_EQ_0] THEN
    SUBGOAL_THEN `~((if (ap:real^3)$3 < (r1:real^3)$3 then &1 else -- &1) = &0)`
      (fun th -> REWRITE_TAC[th]) THENL [COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN DISCH_TAC THEN
    UNDISCH_TAC `~affine_dependent {ap:real^3,r1,r2}` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `r2 - ap = (((r2:real^3)$3 - (ap:real^3)$3) * inv((r1:real^3)$3 - ap$3)) %
                            (r1 - ap)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. ((r2:real^3)$3 - (ap:real^3)$3) % v`) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_SUB_0; VECTOR_MUL_LID] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_AC];
      ALL_TAC] THEN
    SUBGOAL_THEN `collinear {ap:real^3,r1,r2}` MP_TAC THENL
     [SUBGOAL_THEN `{ap:real^3,r1,r2} = {r1,ap,r2}` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[COLLINEAR_3] THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
      DISJ2_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `((r2:real^3)$3 - (ap:real^3)$3) * inv((r1:real^3)$3 - ap$3)` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN
      SUBGOAL_THEN `~(ap:real^3 = r1) /\ ~(ap = r2) /\ ~(r1 = r2)` MP_TAC THENL
       [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
        TRY(FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[MOI_S5S_LEX_ASYM]
          `moi_s5s_lexlt (x:real^3) x ==> F`))) THEN ASM_REAL_ARITH_TAC;
        MESON_TAC[]]];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[VECTOR_ARITH `(a:real^3) = b + x <=> a - b = x`] THEN
    ASM_REWRITE_TAC[moi_s5s_w; VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[VECTOR_ARITH `(a:real^3) = b + x <=> a - b = x`] THEN
    ASM_REWRITE_TAC[moi_s5s_w; VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[moi_s5s_w; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_SUB_0] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Relative interiors: a point lies in the relative interior of at most one *)
(* simplex of a complex; open level slices of crossing triangles and level  *)
(* points of crossing edges lie in the relative interiors.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S5S_RELINT_UNIQ = prove
 (`!(k:(real^N->bool)->bool) s t x.
     simplicial_complex k /\ s IN k /\ t IN k /\
     x IN relative_interior s /\ x IN relative_interior t
     ==> s = t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) INTER t face_of s /\ s INTER t face_of t`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) INTER t = s /\ s INTER t = t` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`(s:real^N->bool) INTER t`; `s:real^N->bool`]
        FACE_OF_DISJOINT_RELATIVE_INTERIOR);
      MP_TAC(ISPECL [`(s:real^N->bool) INTER t`; `t:real^N->bool`]
        FACE_OF_DISJOINT_RELATIVE_INTERIOR)] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    SET_TAC[]]);;

let MOI_S5S_PT_OPEN_SEGMENT = prove
 (`!(a:real^3) b t.
     (a$3 < t /\ t < b$3 \/ b$3 < t /\ t < a$3)
     ==> moi_s5s_pt a b t IN segment(a,b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((a:real^3) = b) /\ ~(a$3 = (b:real^3)$3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_SEGMENT; moi_s5s_pt] THEN
  EXISTS_TAC `(t - (a:real^3)$3) / ((b:real^3)$3 - a$3)` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[MOI_S5S_DIV_NEG2] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [SUBGOAL_THEN `&0 < (b:real^3)$3 - (a:real^3)$3` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      ONCE_REWRITE_TAC[MOI_S5S_DIV_NEG2] THEN
      SUBGOAL_THEN `&0 < --((b:real^3)$3 - (a:real^3)$3)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    VECTOR_ARITH_TAC]);;

let MOI_S5S_TRI_EDGES = prove
 (`!(k:(real^3->bool)->bool) c d ap r1 r2.
     simplicial_complex k /\ moi_s5s_tri k c d ap r1 r2
     ==> segment[ap,r1] IN k /\ segment[ap,r2] IN k /\ {ap} IN k /\
         {r1} IN k /\ {r2} IN k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5s_tri; simplicial_complex] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!c'. c' SUBSET {ap:real^3,r1,r2} ==> convex hull c' IN k`
  (fun th -> REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
             REPEAT CONJ_TAC THEN
             TRY(GEN_REWRITE_TAC (LAND_CONV) [GSYM CONVEX_HULL_SING]) THEN
             MATCH_MP_TAC th THEN SET_TAC[]) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term (fun t -> t = `(face_of):(real^3->bool)->(real^3->bool)->bool`))
        (concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
  EXISTS_TAC `convex hull {ap:real^3,r1,r2}` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  EXISTS_TAC `c':real^3->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S5S_LAMBDA = prove
 (`!(ap:real^3) (r:real^3) t.
     ap$3 < t /\ t < r$3 \/ r$3 < t /\ t < ap$3
     ==> &0 < (t - ap$3) / (r$3 - ap$3) /\ (t - ap$3) / (r$3 - ap$3) < &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ap:real^3`; `r:real^3`; `t:real`] MOI_S5S_PT_OPEN_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((ap:real^3) = r) /\ ~(ap$3 = (r:real^3)$3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_SEGMENT; moi_s5s_pt] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t - (ap:real^3)$3) / ((r:real^3)$3 - ap$3) = u`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. v$3`) THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  UNDISCH_TAC `~((ap:real^3)$3 = (r:real^3)$3)` THEN CONV_TAC REAL_FIELD);;

let MOI_S5S_TRI_RELINT = prove
 (`!(ap:real^3) r1 r2 t x.
     ~affine_dependent {ap,r1,r2} /\
     ((ap$3 < t /\ t < r1$3 /\ t < r2$3) \/ (r1$3 < t /\ r2$3 < t /\ t < ap$3)) /\
     x IN segment(moi_s5s_pt ap r1 t, moi_s5s_pt ap r2 t)
     ==> x IN relative_interior(convex hull {ap,r1,r2})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC `r1:real^3 = r2` THENL
   [ASM_REWRITE_TAC[SEGMENT_REFL; NOT_IN_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `~((ap:real^3) = r1) /\ ~(ap = r2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`ap:real^3`; `r1:real^3`; `t:real`] MOI_S5S_LAMBDA) THEN
  MP_TAC(ISPECL [`ap:real^3`; `r2:real^3`; `t:real`] MOI_S5S_LAMBDA) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  ABBREV_TAC `l1 = (t - (ap:real^3)$3) / ((r1:real^3)$3 - ap$3)` THEN
  ABBREV_TAC `l2 = (t - (ap:real^3)$3) / ((r2:real^3)$3 - ap$3)` THEN
  ASM_REWRITE_TAC[IN_SEGMENT; moi_s5s_pt] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `{ap:real^3,r1,r2}` RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `\v:real^3. if v = ap then &1 - (&1 - th) * l1 - th * l2
                        else if v = r1 then (&1 - th) * l1 else th * l2` THEN
  SUBGOAL_THEN `~((r1:real^3) = ap) /\ ~(r2 = ap) /\ ~(r2 = r1)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_neg o concl))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           IN_INSERT; NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; VECTOR_ADD_RID] THEN
  SUBGOAL_THEN `&0 < (&1 - th) * l1 /\ &0 < th * l2 /\ (&1 - th) * l1 < &1 - th /\
                th * l2 < th` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
    VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Classification of the simplices that meet the slab: crossing edges and   *)
(* crossing triangles with canonical data.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S5S_TRI_AFFDIM = prove
 (`!(k:(real^3->bool)->bool) c d ap r1 r2.
     c < d /\ moi_s5s_tri k c d ap r1 r2
     ==> aff_dim(convex hull {ap,r1,r2}) = &2 /\
         ~(ap = r1) /\ ~(ap = r2) /\ ~(r1 = r2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5s_tri] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `~((ap:real^3) = r1) /\ ~(ap = r2) /\ ~(r1 = r2)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[MOI_S5S_LEX_ASYM]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[ARITH] THEN CONV_TAC INT_REDUCE_CONV);;

let MOI_S5S_ORDER2 = prove
 (`!q1 q2:real^3. ~(q1 = q2)
     ==> ?r1 r2. {r1,r2} = {q1,q2} /\ moi_s5s_lexlt r1 r2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP MOI_S5S_LEX_TOTAL) THENL
   [MAP_EVERY EXISTS_TAC [`q1:real^3`; `q2:real^3`];
    MAP_EVERY EXISTS_TAC [`q2:real^3`; `q1:real^3`]] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_S5S_APEX = prove
 (`!c d (ap:real^3) q1 q2.
     ~(q1 = q2) /\
     (ap$3 < c /\ d < q1$3 /\ d < q2$3 \/ q1$3 < c /\ q2$3 < c /\ d < ap$3)
     ==> ?r1 r2. {ap,r1,r2} = {ap,q1,q2} /\ moi_s5s_lexlt r1 r2 /\
                 (ap$3 < c /\ d < r1$3 /\ d < r2$3 \/
                  r1$3 < c /\ r2$3 < c /\ d < ap$3)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real^3` (X_CHOOSE_THEN `r2:real^3`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_S5S_ORDER2) THEN
  MAP_EVERY EXISTS_TAC [`r1:real^3`; `r2:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(r1:real^3) IN {q1,q2} /\ r2 IN {q1,q2}` MP_TAC THENL
   [UNDISCH_TAC `{r1:real^3,r2} = {q1,q2}` THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5S_APEX3 = prove
 (`!c d (p:real^3) q r.
     ~(p = q) /\ ~(p = r) /\ ~(q = r) /\ c < d /\
     (p$3 < c \/ d < p$3) /\ (q$3 < c \/ d < q$3) /\ (r$3 < c \/ d < r$3) /\
     (p$3 < c \/ q$3 < c \/ r$3 < c) /\ (d < p$3 \/ d < q$3 \/ d < r$3)
     ==> ?ap r1 r2. {ap,r1,r2} = {p,q,r} /\ moi_s5s_lexlt r1 r2 /\
                    (ap$3 < c /\ d < r1$3 /\ d < r2$3 \/
                     r1$3 < c /\ r2$3 < c /\ d < ap$3)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ASM_CASES_TAC `(p:real^3)$3 < c` THEN ASM_CASES_TAC `(q:real^3)$3 < c` THEN
  ASM_CASES_TAC `(r:real^3)$3 < c` THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
  MAP_FIRST (fun (a,b,e) ->
    MP_TAC(SPECL [`c:real`; `d:real`; a; b; e] MOI_S5S_APEX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real^3` (X_CHOOSE_THEN `r2:real^3`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))) THEN
    MAP_EVERY EXISTS_TAC [a; `r1:real^3`; `r2:real^3`] THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[])
   [`p:real^3`,`q:real^3`,`r:real^3`; `q:real^3`,`p:real^3`,`r:real^3`;
    `r:real^3`,`p:real^3`,`q:real^3`]);;

let MOI_S5S_CLASSIFY = prove
 (`!(k:(real^3->bool)->bool) c d s y.
     simplicial_complex k /\ (!s. s IN k ==> aff_dim s <= &2) /\ c < d /\
     (!v. {v} IN k ==> v$3 < c \/ d < v$3) /\
     s IN k /\ y IN s /\ c <= y$3 /\ y$3 <= d
     ==> (?a b. moi_s5s_edge k c d a b /\ s = segment[a,b]) \/
         (?ap r1 r2. moi_s5s_tri k c d ap r1 r2 /\ s = convex hull {ap,r1,r2})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sc") (CONJUNCTS_THEN2 (LABEL_TAC "dim")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vert")
    STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `?n. n simplex (s:real^3->bool)` MP_TAC THENL
   [USE_THEN "sc" (MP_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `vv:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `FINITE (vv:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. v IN vv ==> v$3 < c \/ d < v$3` (LABEL_TAC "side") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN USE_THEN "vert" MATCH_MP_TAC THEN
    USE_THEN "sc" (MP_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
    DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{v:real^3}` THEN ASM_REWRITE_TAC[CONVEX_HULL_SING; SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^3. u IN vv /\ u$3 < c` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?u:real^3. u IN vv /\ u$3 < c` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    SUBGOAL_THEN `(s:real^3->bool) SUBSET {x | x$3 > d}` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GT; SUBSET; IN_ELIM_THM; real_gt] THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `(y:real^3) IN s` THEN UNDISCH_TAC `(y:real^3)$3 <= d` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_gt] THEN MESON_TAC[REAL_NOT_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^3. w IN vv /\ d < w$3` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?w:real^3. w IN vv /\ d < w$3` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    SUBGOAL_THEN `(s:real^3->bool) SUBSET {x | x$3 < c}` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT; SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `(y:real^3) IN s` THEN UNDISCH_TAC `c <= (y:real^3)$3` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_NOT_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u:real^3 = w)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(vv:real^3->bool) = 2 \/ CARD vv = 3` MP_TAC THENL
   [SUBGOAL_THEN `aff_dim(s:real^3->bool) = n` MP_TAC THENL
     [ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "dim" (MP_TAC o C MATCH_MP (ASSUME `(s:real^3->bool) IN k`) o
      SPEC `s:real^3->bool`) THEN
    SUBGOAL_THEN `2 <= CARD(vv:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `CARD {u:real^3,w} = 2 /\ CARD {u,w} <= CARD(vv:real^3->bool)
                               ==> 2 <= CARD vv`) THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
        ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY] THEN ARITH_TAC;
        MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `&(CARD(vv:real^3->bool)) = (n:int) + &1` THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`u:real^3`; `w:real^3`] THEN
    SUBGOAL_THEN `vv = {u:real^3,w}` SUBST_ALL_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_s5s_edge; SEGMENT_CONVEX_HULL] THEN
    UNDISCH_TAC `(s:real^3->bool) IN k` THEN ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL];
    DISJ2_TAC THEN
    SUBGOAL_THEN `(vv:real^3->bool) HAS_SIZE 3` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3`
      (X_CHOOSE_THEN `r:real^3` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(p:real^3) IN vv /\ q IN vv /\ r IN vv` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:real`; `d:real`; `p:real^3`; `q:real^3`; `r:real^3`]
      MOI_S5S_APEX3) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      TRY(USE_THEN "side" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THENL
       [UNDISCH_TAC `(u:real^3) IN vv` THEN UNDISCH_TAC `(u:real^3)$3 < c`;
        UNDISCH_TAC `(w:real^3) IN vv` THEN UNDISCH_TAC `d < (w:real^3)$3`] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `vv = {p:real^3,q,r}` THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `s = convex hull {p:real^3,q,r}` THEN DISCH_THEN SUBST_ALL_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ap:real^3` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r1:real^3` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r2:real^3` THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    ASM_REWRITE_TAC[moi_s5s_tri]]);;

(* ------------------------------------------------------------------------- *)
(* The global map: canonical data of each crossing triangle (by choice), the *)
(* candidate values, and their uniqueness (relative interiors).             *)
(* ------------------------------------------------------------------------- *)

let moi_s5s_dat = new_definition
 `moi_s5s_dat (k:(real^3->bool)->bool) c d (s:real^3->bool) =
    @q:real^3#real^3#real^3.
      moi_s5s_tri k c d (FST q) (FST(SND q)) (SND(SND q)) /\
      s = convex hull {FST q, FST(SND q), SND(SND q)}`;;

let moi_s5s_trapof = new_definition
 `moi_s5s_trapof (ap:real^3) r1 r2 c d (z:real^(3,1)finite_sum) =
    moi_s5s_trap (moi_s5s_pt ap r1 c) (moi_s5s_pt ap r2 c)
                 (moi_s5s_pt ap r1 d) (moi_s5s_pt ap r2 d)
                 (moi_s5s_w ap r1 r2) (abs(c - ap$3)) z`;;

let moi_s5s_cand = new_definition
 `moi_s5s_cand (k:(real^3->bool)->bool) c d (x:real^3) (s:real^1) (y:real^3) <=>
    (?t. t IN k /\
         (?ap r1 r2. moi_s5s_tri k c d ap r1 r2 /\ t = convex hull {ap,r1,r2}) /\
         x IN t /\ x$3 = c /\
         y = moi_s5s_trapof (FST(moi_s5s_dat k c d t)) (FST(SND(moi_s5s_dat k c d t)))
                            (SND(SND(moi_s5s_dat k c d t))) c d (pastecart x s)) \/
    (?a b. moi_s5s_edge k c d a b /\ x = moi_s5s_pt a b c /\
           y = moi_s5s_pt a b (c + drop s * (d - c)))`;;

let MOI_S5S_DAT = prove
 (`!(k:(real^3->bool)->bool) c d t.
     (?ap r1 r2. moi_s5s_tri k c d ap r1 r2 /\ t = convex hull {ap,r1,r2})
     ==> moi_s5s_tri k c d (FST(moi_s5s_dat k c d t)) (FST(SND(moi_s5s_dat k c d t)))
                           (SND(SND(moi_s5s_dat k c d t))) /\
         t = convex hull {FST(moi_s5s_dat k c d t), FST(SND(moi_s5s_dat k c d t)),
                          SND(SND(moi_s5s_dat k c d t))}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `ap:real^3` (X_CHOOSE_THEN `r1:real^3`
    (X_CHOOSE_THEN `r2:real^3` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[moi_s5s_dat] THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `(ap:real^3),(r1:real^3),(r2:real^3)` THEN ASM_REWRITE_TAC[]);;

let MOI_S5S_EDGE_FACTS = prove
 (`!(k:(real^3->bool)->bool) c d a b.
     c < d /\ moi_s5s_edge k c d a b
     ==> ~(a$3 = b$3) /\ ~(a = b) /\ (moi_s5s_pt a b c)$3 = c /\
         moi_s5s_pt a b c IN relative_interior(segment[a,b]) /\
         !t. c <= t /\ t <= d ==> moi_s5s_pt a b t IN relative_interior(segment[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5s_edge] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((a:real^3)$3 = (b:real^3)$3) /\ ~(a = b)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; DISCH_THEN SUBST_ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S5S_PT_HEIGHT; RELATIVE_INTERIOR_SEGMENT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5S_PT_OPEN_SEGMENT THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5S_PT_OPEN_SEGMENT THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Open slices go to open slices; the trapezoid of a crossing triangle.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S5S_SEG_ALONG_OPEN = prove
 (`!(a:real^3) w phi y.
     &0 < phi /\ ~(w = vec 0)
     ==> (y IN segment(a,a + phi % w) <=>
          ?k. &0 < k /\ k < phi /\ y = a + k % w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(a = a + phi % (w:real^3))` (fun th -> REWRITE_TAC[IN_SEGMENT; th]) THENL
   [REWRITE_TAC[VECTOR_ARITH `a = a + x:real^3 <=> x = vec 0`; VECTOR_MUL_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u * phi` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k / phi` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - u) % a + u % (a + p % w):real^3 = a + (u * p) % w`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]]);;

let MOI_S5S_TRAP_OPEN = prove
 (`!(p1:real^3) p2 q1 q2 w alpha beta x s.
     ~(w = vec 0) /\ &0 < alpha /\ &0 < beta /\
     p2 = p1 + alpha % w /\ q2 = q1 + beta % w /\
     x IN segment(p1,p2) /\ s IN interval[vec 0,vec 1]
     ==> moi_s5s_trap p1 p2 q1 q2 w alpha (pastecart x s) IN
         segment(p1 + drop s % (q1 - p1), p2 + drop s % (q2 - p2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN segment[p1,p2]` ASSUME_TAC THENL
   [ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p1:real^3`; `w:real^3`; `alpha:real`; `x:real^3`] MOI_S5S_MU_SEG) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "xe"))) THEN
  SUBGOAL_THEN `~(x:real^3 = p1) /\ ~(x = p2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ENDS_NOT_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < moi_s5s_mu p1 w alpha (x:real^3) /\ moi_s5s_mu p1 w alpha x < &1`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= m /\ m <= &1 /\ ~(m = &0) /\ ~(m = &1)
                             ==> &0 < m /\ m < &1`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~(x:real^3 = p1)`; UNDISCH_TAC `~(x:real^3 = p2)`] THEN
    USE_THEN "xe" MP_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `m = moi_s5s_mu p1 w alpha (x:real^3)` THEN
  MP_TAC(ISPECL [`p1:real^3`; `p2:real^3`; `q1:real^3`; `q2:real^3`; `w:real^3`;
                 `alpha:real`; `beta:real`; `x:real^3`; `s:real^1`] MOI_S5S_TRAP_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(p1 + alpha % w) + drop s % ((q1 + beta % w) - (p1 + alpha % w)) =
    (p1 + drop s % (q1 - p1)) + (alpha + drop s * (beta - alpha)) % (w:real^3)`
  SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`alpha:real`; `beta:real`; `&0`; `drop(s:real^1)`] MOI_S5S_KAPPA) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LE_01] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_S5S_SEG_ALONG_OPEN] THEN
  EXISTS_TAC `alpha * m + min m (drop(s:real^1)) * (beta - alpha)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`alpha:real`; `beta:real`; `&0`; `m:real`; `drop(s:real^1)`]
      MOI_S5S_KAPPA_MONO) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> min (&0) s = &0`] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`alpha:real`; `beta:real`; `m:real`; `&1`; `drop(s:real^1)`]
      MOI_S5S_KAPPA_MONO) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `s <= &1 ==> min (&1) s = s`] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The trapezoid of a crossing triangle: slab part, level slice, open parts. *)
(* ------------------------------------------------------------------------- *)

let MOI_S5S_TRI_STRICT = prove
 (`!(k:(real^3->bool)->bool) c d ap r1 r2 t.
     moi_s5s_tri k c d ap r1 r2 /\ c <= t /\ t <= d
     ==> (ap$3 < t /\ t < r1$3 /\ t < r2$3) \/ (r1$3 < t /\ r2$3 < t /\ t < ap$3)`,
  REWRITE_TAC[moi_s5s_tri] THEN REAL_ARITH_TAC);;

let MOI_S5S_TRI_SLICE = prove
 (`!(k:(real^3->bool)->bool) c d ap r1 r2.
     c < d /\ moi_s5s_tri k c d ap r1 r2
     ==> {x | x IN convex hull {ap,r1,r2} /\ x$3 = c} =
         segment[moi_s5s_pt ap r1 c,moi_s5s_pt ap r2 c]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5S_CONE_SLICE THEN
  MATCH_MP_TAC MOI_S5S_TRI_STRICT THEN
  MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`; `c:real`; `d:real`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5S_TRI_SLAB = prove
 (`!(k:(real^3->bool)->bool) c d ap r1 r2.
     c < d /\ moi_s5s_tri k c d ap r1 r2
     ==> {y | y IN convex hull {ap,r1,r2} /\ c <= y$3 /\ y$3 <= d} =
         IMAGE (moi_s5s_trapof ap r1 r2 c d)
               (segment[moi_s5s_pt ap r1 c,moi_s5s_pt ap r2 c] PCROSS
                interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `ap:real^3`;
                 `r1:real^3`; `r2:real^3`] MOI_S5S_TRI_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s5s_trapof ap r1 r2 c d =
    moi_s5s_trap (moi_s5s_pt ap r1 c) (moi_s5s_pt ap r2 c)
                 (moi_s5s_pt ap r1 d) (moi_s5s_pt ap r2 d)
                 (moi_s5s_w ap r1 r2) (abs(c - (ap:real^3)$3))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_s5s_trapof]; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`moi_s5s_pt ap r1 c:real^3`; `moi_s5s_pt ap r2 c:real^3`;
     `moi_s5s_pt ap r1 d:real^3`; `moi_s5s_pt ap r2 d:real^3`;
     `moi_s5s_w ap r1 r2`; `abs(c - (ap:real^3)$3)`; `abs(d - (ap:real^3)$3)`]
    MOI_S5S_TRAP_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM MOI_S5S_PT_AFFINE] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    EXISTS_TAC `lift(((y:real^3)$3 - c) / (d - c))` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    SUBGOAL_THEN `c + ((y:real^3)$3 - c) / (d - c) * (d - c) = y$3` SUBST1_TAC THENL
     [UNDISCH_TAC `c < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`ap:real^3`; `r1:real^3`; `r2:real^3`; `(y:real^3)$3`]
        MOI_S5S_CONE_SLICE) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MOI_S5S_TRI_STRICT THEN
        MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`; `c:real`; `d:real`] THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_ELIM_THM]]];
    DISCH_THEN(X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `c <= c + drop(s:real^1) * (d - c) /\ c + drop s * (d - c) <= d`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> c <= c + x`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= &1 * (d - c) ==> c + x <= d`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ap:real^3`; `r1:real^3`; `r2:real^3`;
                   `c + drop(s:real^1) * (d - c)`] MOI_S5S_CONE_SLICE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MOI_S5S_TRI_STRICT THEN
      MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`; `c:real`; `d:real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(IN) (y:real^3)` o SYM) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S5S_TRAP_ALL = prove
 (`!(p1:real^3) p2 q1 q2 w alpha beta c d.
     (~(w = vec 0) /\ &0 < alpha /\ &0 < beta /\
      p2 = p1 + alpha % w /\ q2 = q1 + beta % w /\
      p1$3 = c /\ q1$3 = d /\ w$3 = &0) /\ c < d
     ==> ((!x s. x IN segment[p1,p2]
                 ==> (moi_s5s_trap p1 p2 q1 q2 w alpha (pastecart x s))$3 =
                     c + drop s * (d - c)) /\
          (!x. x IN segment[p1,p2]
               ==> moi_s5s_trap p1 p2 q1 q2 w alpha (pastecart x (vec 0)) = x) /\
          (!s. s IN interval[vec 0,vec 1]
               ==> moi_s5s_trap p1 p2 q1 q2 w alpha (pastecart p1 s) =
                   p1 + drop s % (q1 - p1) /\
                   moi_s5s_trap p1 p2 q1 q2 w alpha (pastecart p2 s) =
                   p2 + drop s % (q2 - p2))) /\
         (!z z'. z IN segment[p1,p2] PCROSS interval[vec 0,vec 1] /\
                 z' IN segment[p1,p2] PCROSS interval[vec 0,vec 1] /\
                 moi_s5s_trap p1 p2 q1 q2 w alpha z =
                 moi_s5s_trap p1 p2 q1 q2 w alpha z'
                 ==> z = z') /\
         (!x s. x IN segment(p1,p2) /\ s IN interval[vec 0,vec 1]
                ==> moi_s5s_trap p1 p2 q1 q2 w alpha (pastecart x s) IN
                    segment(p1 + drop s % (q1 - p1), p2 + drop s % (q2 - p2)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5S_TRAP_BASIC THEN EXISTS_TAC `beta:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5S_TRAP_INJ THEN
    MAP_EVERY EXISTS_TAC [`beta:real`; `c:real`; `d:real`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5S_TRAP_OPEN THEN
    EXISTS_TAC `beta:real` THEN ASM_REWRITE_TAC[]]);;

let MOI_S5S_TRI_TRAP = prove
 (`!(k:(real^3->bool)->bool) c d ap r1 r2.
     c < d /\ moi_s5s_tri k c d ap r1 r2
     ==> pl_map_on (segment[moi_s5s_pt ap r1 c,moi_s5s_pt ap r2 c] PCROSS
                    interval[vec 0,vec 1]) (moi_s5s_trapof ap r1 r2 c d) /\
         (!x s. x IN segment[moi_s5s_pt ap r1 c,moi_s5s_pt ap r2 c]
                ==> (moi_s5s_trapof ap r1 r2 c d (pastecart x s))$3 =
                    c + drop s * (d - c)) /\
         (!x. x IN segment[moi_s5s_pt ap r1 c,moi_s5s_pt ap r2 c]
              ==> moi_s5s_trapof ap r1 r2 c d (pastecart x (vec 0)) = x) /\
         (!s. s IN interval[vec 0,vec 1]
              ==> moi_s5s_trapof ap r1 r2 c d (pastecart (moi_s5s_pt ap r1 c) s) =
                  moi_s5s_pt ap r1 (c + drop s * (d - c)) /\
                  moi_s5s_trapof ap r1 r2 c d (pastecart (moi_s5s_pt ap r2 c) s) =
                  moi_s5s_pt ap r2 (c + drop s * (d - c))) /\
         (!z z'. z IN segment[moi_s5s_pt ap r1 c,moi_s5s_pt ap r2 c] PCROSS
                      interval[vec 0,vec 1] /\
                 z' IN segment[moi_s5s_pt ap r1 c,moi_s5s_pt ap r2 c] PCROSS
                       interval[vec 0,vec 1] /\
                 moi_s5s_trapof ap r1 r2 c d z = moi_s5s_trapof ap r1 r2 c d z'
                 ==> z = z') /\
         (!x s. x IN segment(moi_s5s_pt ap r1 c,moi_s5s_pt ap r2 c) /\
                s IN interval[vec 0,vec 1]
                ==> moi_s5s_trapof ap r1 r2 c d (pastecart x s) IN
                    relative_interior(convex hull {ap,r1,r2})) /\
         (!x. x IN segment(moi_s5s_pt ap r1 c,moi_s5s_pt ap r2 c)
              ==> x IN relative_interior(convex hull {ap,r1,r2}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s5s_trapof ap r1 r2 c d =
    moi_s5s_trap (moi_s5s_pt ap r1 c) (moi_s5s_pt ap r2 c)
                 (moi_s5s_pt ap r1 d) (moi_s5s_pt ap r2 d)
                 (moi_s5s_w ap r1 r2) (abs(c - (ap:real^3)$3))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_s5s_trapof]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `ap:real^3`;
                 `r1:real^3`; `r2:real^3`] MOI_S5S_TRI_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun data -> MP_TAC(MATCH_MP MOI_S5S_TRAP_ALL
    (CONJ data (ASSUME `c < d`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC MP_TAC)) THEN
  DISCH_THEN(LABEL_TAC "open") THEN DISCH_THEN(LABEL_TAC "inj") THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lev") (CONJUNCTS_THEN2 (LABEL_TAC "bot")
    (LABEL_TAC "sides"))) THEN
  REWRITE_TAC[MOI_S5S_TRAP_PL] THEN
  CONJ_TAC THENL [USE_THEN "lev" ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "bot" ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    USE_THEN "sides" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(s:real^1) IN interval[vec 0,vec 1]`)]) THEN
    REWRITE_TAC[MOI_S5S_PT_AFFINE];
    ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "inj" ACCEPT_TAC; ALL_TAC] THEN
  UNDISCH_TAC `moi_s5s_tri k c d ap r1 r2` THEN REWRITE_TAC[moi_s5s_tri] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5S_TRI_RELINT THENL
   [EXISTS_TAC `c + drop(s:real^1) * (d - c)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `&0 <= drop(s:real^1) * (d - c) /\ drop s * (d - c) <= d - c`
      MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[MOI_S5S_PT_AFFINE] THEN
      USE_THEN "open" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC]];
    EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Normal form of candidate values (carrier simplex of the bottom point) and *)
(* uniqueness.                                                                *)
(* ------------------------------------------------------------------------- *)

let moi_s5s_nf = new_definition
 `moi_s5s_nf (k:(real^3->bool)->bool) c d (x:real^3) (s:real^1) (y:real^3) <=>
    (?t. t IN k /\ aff_dim t = &2 /\ x IN relative_interior t /\
         y = moi_s5s_trapof (FST(moi_s5s_dat k c d t)) (FST(SND(moi_s5s_dat k c d t)))
                            (SND(SND(moi_s5s_dat k c d t))) c d (pastecart x s)) \/
    (?a b. segment[a,b] IN k /\ ~(a$3 = b$3) /\
           x IN relative_interior(segment[a,b]) /\
           y = moi_s5s_pt a b (c + drop s * (d - c)))`;;

let MOI_S5S_CAND_NF = prove
 (`!(k:(real^3->bool)->bool) c d x s y.
     simplicial_complex k /\ c < d /\ s IN interval[vec 0,vec 1] /\
     moi_s5s_cand k c d x s y
     ==> moi_s5s_nf k c d x s y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5s_cand; moi_s5s_nf] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MOI_S5S_DAT) STRIP_ASSUME_TAC))) THEN
    ABBREV_TAC `bp = FST(moi_s5s_dat k c d (t:real^3->bool))` THEN
    ABBREV_TAC `b1 = FST(SND(moi_s5s_dat k c d (t:real^3->bool)))` THEN
    ABBREV_TAC `b2 = SND(SND(moi_s5s_dat k c d (t:real^3->bool)))` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `bp:real^3`;
                   `b1:real^3`; `b2:real^3`] MOI_S5S_TRI_TRAP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "sides")
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "openy")
      (LABEL_TAC "openx"))))))) THEN
    SUBGOAL_THEN `(x:real^3) IN segment[moi_s5s_pt bp b1 c,moi_s5s_pt bp b2 c]`
    MP_TAC THENL
     [MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `bp:real^3`;
                     `b1:real^3`; `b2:real^3`] MOI_S5S_TRI_SLICE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT;
                                     NOT_IN_EMPTY]) THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `bp:real^3`;
                   `b1:real^3`; `b2:real^3`] MOI_S5S_TRI_EDGES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `bp:real^3`;
                   `b1:real^3`; `b2:real^3`] MOI_S5S_TRI_AFFDIM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `moi_s5s_tri k c d bp b1 b2` THEN REWRITE_TAC[moi_s5s_tri] THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `convex hull {bp:real^3,b1,b2}` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "openx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`bp:real^3`; `b1:real^3`];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`bp:real^3`; `b2:real^3`]] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC MOI_S5S_PT_OPEN_SEGMENT THEN ASM_REAL_ARITH_TAC) THEN
    USE_THEN "sides" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(s:real^1) IN interval[vec 0,vec 1]`)]);
    FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3`
      STRIP_ASSUME_TAC)) THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `a:real^3`;
                   `b:real^3`] MOI_S5S_EDGE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_s5s_edge]]);;

let MOI_S5S_NF_UNIQ = prove
 (`!(k:(real^3->bool)->bool) c d x s y y'.
     simplicial_complex k /\ moi_s5s_nf k c d x s y /\ moi_s5s_nf k c d x s y'
     ==> y = y'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5s_nf] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC MP_TAC)) THEN
  SUBGOAL_THEN
   `!t (a:real^3) b. t IN k /\ aff_dim t = &2 /\ x IN relative_interior t /\
                     segment[a,b] IN k /\ ~(a$3 = b$3) /\
                     x IN relative_interior(segment[a,b]) ==> F`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`;
                   `segment[a:real^3,b]`; `x:real^3`] MOI_S5S_RELINT_UNIQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim(segment[a:real^3,b]) = &2` THEN
    REWRITE_TAC[AFF_DIM_SEGMENT] THEN COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `t':real^3->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `a':real^3` (X_CHOOSE_THEN `b':real^3` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`; `t':real^3->bool`;
                   `x:real^3`] MOI_S5S_RELINT_UNIQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `segment[a:real^3,b]`;
                   `segment[a':real^3,b']`; `x:real^3`] MOI_S5S_RELINT_UNIQ) THEN
    ASM_REWRITE_TAC[SEGMENT_EQ] THEN
    REWRITE_TAC[SET_RULE `{a:real^3,b} = {c,d} <=> a = c /\ b = d \/ a = d /\ b = c`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S5S_PT_SYM THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The global map and its values on the pieces.                              *)
(* ------------------------------------------------------------------------- *)

let moi_s5s_f = new_definition
 `moi_s5s_f (k:(real^3->bool)->bool) c d (z:real^(3,1)finite_sum) =
    @y. moi_s5s_cand k c d (fstcart z) (sndcart z) y`;;

let moi_s5s_hyp = new_definition
 `moi_s5s_hyp (k:(real^3->bool)->bool) c d <=>
    FINITE k /\ simplicial_complex k /\ (!s. s IN k ==> aff_dim s <= &2) /\
    c < d /\ (!v. {v} IN k ==> v$3 < c \/ d < v$3)`;;

let MOI_S5S_F_EXISTS = prove
 (`!(k:(real^3->bool)->bool) c d x s.
     moi_s5s_hyp k c d /\ x IN UNIONS k /\ x$3 = c
     ==> ?y. moi_s5s_cand k c d x s y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5s_hyp; IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)
     ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `t:real^3->bool`;
                 `x:real^3`] MOI_S5S_CLASSIFY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s5s_cand] THEN STRIP_TAC THENL
   [EXISTS_TAC `moi_s5s_pt a b (c + drop(s:real^1) * (d - c))` THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `a:real^3`;
                   `b:real^3`] MOI_S5S_EDGE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `x:real^3`] MOI_S5S_SEG_HEIGHT) THEN
    ASM_MESON_TAC[];
    EXISTS_TAC
     `moi_s5s_trapof (FST(moi_s5s_dat k c d t)) (FST(SND(moi_s5s_dat k c d t)))
                     (SND(SND(moi_s5s_dat k c d (t:real^3->bool)))) c d
                     (pastecart x s)` THEN
    DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`ap:real^3`; `r1:real^3`; `r2:real^3`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S5S_F_EQ = prove
 (`!(k:(real^3->bool)->bool) c d x s y.
     moi_s5s_hyp k c d /\ x IN UNIONS k /\ x$3 = c /\ s IN interval[vec 0,vec 1] /\
     moi_s5s_cand k c d x s y
     ==> moi_s5s_f k c d (pastecart x s) = y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s5s_f; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SUBGOAL_THEN `moi_s5s_cand k c d x s (@y. moi_s5s_cand k c d x s y)` ASSUME_TAC THENL
   [CONV_TAC SELECT_CONV THEN MATCH_MP_TAC MOI_S5S_F_EXISTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s5s_hyp k c d` THEN REWRITE_TAC[moi_s5s_hyp] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S5S_NF_UNIQ THEN
  MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `x:real^3`;
                        `s:real^1`] THEN
  ASM_SIMP_TAC[MOI_S5S_CAND_NF]);;

(* ------------------------------------------------------------------------- *)
(* The pieces: the bottom slice of each simplex times [0,1].                 *)
(* ------------------------------------------------------------------------- *)

let moi_s5s_inf = new_definition
 `moi_s5s_inf (k:(real^3->bool)->bool) c d (z:real^(3,1)finite_sum) (y:real^3) <=>
    (?t. t IN k /\ aff_dim t = &2 /\ y IN relative_interior t /\
         z IN segment[moi_s5s_pt (FST(moi_s5s_dat k c d t)) (FST(SND(moi_s5s_dat k c d t))) c,
                      moi_s5s_pt (FST(moi_s5s_dat k c d t)) (SND(SND(moi_s5s_dat k c d t))) c]
              PCROSS interval[vec 0,vec 1] /\
         y = moi_s5s_trapof (FST(moi_s5s_dat k c d t)) (FST(SND(moi_s5s_dat k c d t)))
                            (SND(SND(moi_s5s_dat k c d t))) c d z) \/
    (?a b. segment[a,b] IN k /\ ~(a$3 = b$3) /\
           y IN relative_interior(segment[a,b]) /\ fstcart z = moi_s5s_pt a b c /\
           y = moi_s5s_pt a b (c + drop(sndcart z) * (d - c)))`;;

let MOI_S5S_PL_EMPTY = prove
 (`!f:real^M->real^N. pl_map_on {} f`,
  REWRITE_TAC[pl_map_on; NOT_IN_EMPTY]);;

let MOI_S5S_PIECE_TRI = prove
 (`!(k:(real^3->bool)->bool) c d t.
     moi_s5s_hyp k c d /\ t IN k /\
     (?ap r1 r2. moi_s5s_tri k c d ap r1 r2 /\ t = convex hull {ap,r1,r2})
     ==> pl_map_on ({x | x IN t /\ x$3 = c} PCROSS interval[vec 0,vec 1])
                   (moi_s5s_f k c d) /\
         IMAGE (moi_s5s_f k c d) ({x | x IN t /\ x$3 = c} PCROSS interval[vec 0,vec 1]) =
         {y | y IN t /\ c <= y$3 /\ y$3 <= d} /\
         (!z. z IN {x | x IN t /\ x$3 = c} PCROSS interval[vec 0,vec 1]
              ==> (moi_s5s_f k c d z)$3 = c + drop(sndcart z) * (d - c) /\
                  moi_s5s_inf k c d z (moi_s5s_f k c d z)) /\
         (!x. x IN t /\ x$3 = c ==> moi_s5s_f k c d (pastecart x (vec 0)) = x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(MATCH_MP MOI_S5S_DAT th)) THEN
  ABBREV_TAC `bp = FST(moi_s5s_dat k c d (t:real^3->bool))` THEN
  ABBREV_TAC `b1 = FST(SND(moi_s5s_dat k c d (t:real^3->bool)))` THEN
  ABBREV_TAC `b2 = SND(SND(moi_s5s_dat k c d (t:real^3->bool)))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> if concl th = `moi_s5s_hyp k c d` then
    MAP_EVERY ASSUME_TAC (CONJUNCTS(REWRITE_RULE[moi_s5s_hyp] th)) else NO_TAC) THEN
  SUBGOAL_THEN `{x | x IN t /\ x$3 = c} =
                segment[moi_s5s_pt bp b1 c,moi_s5s_pt bp b2 c]` (LABEL_TAC "slice") THENL
   [UNDISCH_TAC `t = convex hull {bp:real^3,b1,b2}` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_S5S_TRI_SLICE THEN
    MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `bp:real^3`;
                 `b1:real^3`; `b2:real^3`] MOI_S5S_TRI_TRAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pl") (CONJUNCTS_THEN2 (LABEL_TAC "lev")
    (CONJUNCTS_THEN2 (LABEL_TAC "bot") (CONJUNCTS_THEN2 (LABEL_TAC "sides")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "openy")
    (K ALL_TAC))))))) THEN
  SUBGOAL_THEN
   `!z. z IN segment[moi_s5s_pt bp b1 c,moi_s5s_pt bp b2 c] PCROSS interval[vec 0,vec 1]
        ==> moi_s5s_f k c d z = moi_s5s_trapof bp b1 b2 c d z`
  (LABEL_TAC "feq") THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN t /\ x$3 = c` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN segment[moi_s5s_pt bp b1 c,moi_s5s_pt bp b2 c]` THEN
      USE_THEN "slice" (fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S5S_F_EQ THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_s5s_cand] THEN DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "slice" (fun th -> REWRITE_TAC[th]) THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `moi_s5s_trapof bp b1 b2 c d` THEN
    ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `IMAGE (moi_s5s_f k c d)
            (segment[moi_s5s_pt bp b1 c,moi_s5s_pt bp b2 c] PCROSS interval[vec 0,vec 1]) =
      IMAGE (moi_s5s_trapof bp b1 b2 c d)
            (segment[moi_s5s_pt bp b1 c,moi_s5s_pt bp b2 c] PCROSS interval[vec 0,vec 1])`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x = g x) ==> IMAGE (f:real^(3,1)finite_sum->real^3) s = IMAGE g s`) THEN
      USE_THEN "feq" ACCEPT_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `t = convex hull {bp:real^3,b1,b2}` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_S5S_TRI_SLAB THEN EXISTS_TAC `k:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real^1`] THEN STRIP_TAC THEN
    USE_THEN "feq" (fun th -> REWRITE_TAC[MATCH_MP th
      (REWRITE_RULE[GSYM PASTECART_IN_PCROSS] (CONJ
        (ASSUME `(x:real^3) IN segment[moi_s5s_pt bp b1 c,moi_s5s_pt bp b2 c]`)
        (ASSUME `(s:real^1) IN interval[vec 0,vec 1]`)))]) THEN
    CONJ_TAC THENL
     [USE_THEN "lev" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `bp:real^3`;
                   `b1:real^3`; `b2:real^3`] MOI_S5S_TRI_EDGES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `bp:real^3`;
                   `b1:real^3`; `b2:real^3`] MOI_S5S_TRI_AFFDIM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `c <= c + drop(s:real^1) * (d - c) /\ c + drop s * (d - c) <= d`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> c <= c + x`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= &1 * (d - c) ==> c + x <= d`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[moi_s5s_inf; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    UNDISCH_TAC `(x:real^3) IN segment[moi_s5s_pt bp b1 c,moi_s5s_pt bp b2 c]` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
      MP_TAC(REWRITE_RULE[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] th)) THEN
    UNDISCH_TAC `moi_s5s_tri k c d bp b1 b2` THEN REWRITE_TAC[moi_s5s_tri] THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
      USE_THEN "openy" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`bp:real^3`; `b1:real^3`];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`bp:real^3`; `b2:real^3`]] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "sides" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(s:real^1) IN interval[vec 0,vec 1]`)]) THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
    MATCH_MP_TAC MOI_S5S_PT_OPEN_SEGMENT THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN segment[moi_s5s_pt bp b1 c,moi_s5s_pt bp b2 c]`
    ASSUME_TAC THENL
     [USE_THEN "slice" (fun th -> REWRITE_TAC[GSYM th]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "feq" (fun th -> REWRITE_TAC[MATCH_MP th
      (REWRITE_RULE[GSYM PASTECART_IN_PCROSS] (CONJ
        (ASSUME `(x:real^3) IN segment[moi_s5s_pt bp b1 c,moi_s5s_pt bp b2 c]`)
        (MESON[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1; DROP_VEC; REAL_POS]
          `vec 0 IN interval[vec 0:real^1,vec 1]`)))]) THEN
    USE_THEN "bot" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S5S_PIECE_EDGE = prove
 (`!(k:(real^3->bool)->bool) c d a b.
     moi_s5s_hyp k c d /\ moi_s5s_edge k c d a b
     ==> pl_map_on ({x | x IN segment[a,b] /\ x$3 = c} PCROSS interval[vec 0,vec 1])
                   (moi_s5s_f k c d) /\
         IMAGE (moi_s5s_f k c d)
               ({x | x IN segment[a,b] /\ x$3 = c} PCROSS interval[vec 0,vec 1]) =
         {y | y IN segment[a,b] /\ c <= y$3 /\ y$3 <= d} /\
         (!z. z IN {x | x IN segment[a,b] /\ x$3 = c} PCROSS interval[vec 0,vec 1]
              ==> (moi_s5s_f k c d z)$3 = c + drop(sndcart z) * (d - c) /\
                  moi_s5s_inf k c d z (moi_s5s_f k c d z)) /\
         (!x. x IN segment[a,b] /\ x$3 = c
              ==> moi_s5s_f k c d (pastecart x (vec 0)) = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if concl th = `moi_s5s_hyp k c d` then
    MAP_EVERY ASSUME_TAC (CONJUNCTS(REWRITE_RULE[moi_s5s_hyp] th)) else NO_TAC) THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `a:real^3`;
                 `b:real^3`] MOI_S5S_EDGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ri"))))) THEN
  UNDISCH_TAC `moi_s5s_edge k c d a b` THEN REWRITE_TAC[moi_s5s_edge] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `{x | x IN segment[a,b] /\ x$3 = c} = {moi_s5s_pt (a:real^3) b c}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
     [STRIP_TAC THEN MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `x:real^3`]
        MOI_S5S_SEG_HEIGHT) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_S5S_PT_IN_SEGMENT THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN interval[vec 0,vec 1]
        ==> moi_s5s_f k c d (pastecart (moi_s5s_pt a b c) s) =
            moi_s5s_pt (a:real^3) b (c + drop s * (d - c))`
  (LABEL_TAC "feq") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5S_F_EQ THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[a:real^3,b]` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5S_PT_IN_SEGMENT THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[moi_s5s_cand] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN
      ASM_REWRITE_TAC[moi_s5s_edge]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^(3,1)finite_sum.
                  (\z. drop(sndcart z) % (moi_s5s_pt a b d - moi_s5s_pt (a:real^3) b c)) z +
                  moi_s5s_pt a b c` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real^1`] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[MOI_S5S_PT_AFFINE] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
        MATCH_MP_TAC POLYTOPE_PCROSS THEN REWRITE_TAC[POLYTOPE_SING; POLYTOPE_INTERVAL];
        MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_SNDCART]]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING;
                IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `s:real^1`
        STRIP_ASSUME_TAC)) THEN
      UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
      SUBGOAL_THEN `c <= c + drop(s:real^1) * (d - c) /\ c + drop s * (d - c) <= d`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> c <= c + x`) THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `x <= &1 * (d - c) ==> c + x <= d`) THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_SIMP_TAC[IN_INTERVAL_1; DROP_VEC; MOI_S5S_PT_HEIGHT] THEN
      MATCH_MP_TAC MOI_S5S_PT_IN_SEGMENT THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN
      ABBREV_TAC `sv = lift(((y:real^3)$3 - c) / (d - c))` THEN
      SUBGOAL_THEN `(sv:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
       [EXPAND_TAC "sv" THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`moi_s5s_pt (a:real^3) b c`; `sv:real^1`] THEN
      ASM_SIMP_TAC[] THEN EXPAND_TAC "sv" THEN REWRITE_TAC[LIFT_DROP] THEN
      SUBGOAL_THEN `c + ((y:real^3)$3 - c) / (d - c) * (d - c) = y$3` SUBST1_TAC THENL
       [UNDISCH_TAC `c < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC MOI_S5S_SEG_HEIGHT THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real^1`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MOI_S5S_PT_HEIGHT] THEN
    REWRITE_TAC[moi_s5s_inf; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ri" MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> c <= c + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= &1 * (d - c) ==> c + x <= d`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `x = moi_s5s_pt (a:real^3) b c` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `x:real^3`] MOI_S5S_SEG_HEIGHT) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "feq" (fun th -> REWRITE_TAC[MATCH_MP th
      (MESON[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1; DROP_VEC; REAL_POS]
        `vec 0 IN interval[vec 0:real^1,vec 1]`)]) THEN
    REWRITE_TAC[DROP_VEC; REAL_MUL_LZERO; REAL_ADD_RID]]);;


(* ------------------------------------------------------------------------- *)
(* Assembly: the pieces of every simplex, PL on a finite union of compact    *)
(* pieces, and injectivity by carriers.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S5S_PL_UNIONS = prove
 (`!(P:(real^M->bool)->bool) (f:real^M->real^N).
     FINITE P /\ (!p. p IN P ==> compact p /\ pl_map_on p f)
     ==> pl_map_on (UNIONS P) f`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; MOI_S5S_PL_EMPTY; FORALL_IN_INSERT; UNIONS_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`p:real^M->bool`; `P:(real^M->bool)->bool`] THEN
  STRIP_TAC THEN X_GEN_TAC `f:real^M->real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `compact(UNIONS P:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[]);;

let MOI_S5S_PIECE = prove
 (`!(k:(real^3->bool)->bool) c d t.
     moi_s5s_hyp k c d /\ t IN k
     ==> compact({x | x IN t /\ x$3 = c} PCROSS interval[vec 0:real^1,vec 1]) /\
         pl_map_on ({x | x IN t /\ x$3 = c} PCROSS interval[vec 0,vec 1])
                   (moi_s5s_f k c d) /\
         IMAGE (moi_s5s_f k c d) ({x | x IN t /\ x$3 = c} PCROSS interval[vec 0,vec 1]) =
         {y | y IN t /\ c <= y$3 /\ y$3 <= d} /\
         (!z. z IN {x | x IN t /\ x$3 = c} PCROSS interval[vec 0,vec 1]
              ==> (moi_s5s_f k c d z)$3 = c + drop(sndcart z) * (d - c) /\
                  moi_s5s_inf k c d z (moi_s5s_f k c d z)) /\
         (!x. x IN t /\ x$3 = c ==> moi_s5s_f k c d (pastecart x (vec 0)) = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if concl th = `moi_s5s_hyp k c d` then
    MAP_EVERY ASSUME_TAC (CONJUNCTS(REWRITE_RULE[moi_s5s_hyp] th)) else NO_TAC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    REWRITE_TAC[SET_RULE `{x:real^3 | x IN t /\ P x} = t INTER {x | P x}`] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    REWRITE_TAC[CLOSED_STANDARD_HYPERPLANE] THEN
    UNDISCH_TAC `simplicial_complex (k:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  ASM_CASES_TAC `?y:real^3. y IN t /\ c <= y$3 /\ y$3 <= d` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `t:real^3->bool`;
                   `y:real^3`] MOI_S5S_CLASSIFY) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC MOI_S5S_PIECE_EDGE THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5S_PIECE_TRI THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`ap:real^3`; `r1:real^3`; `r2:real^3`] THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `{x:real^3 | x IN t /\ x$3 = c} = {} /\
                  {y:real^3 | y IN t /\ c <= y$3 /\ y$3 <= d} = {}`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REWRITE_TAC[PCROSS_EMPTY; IMAGE_CLAUSES; MOI_S5S_PL_EMPTY; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[REAL_LE_REFL; REAL_LT_IMP_LE]]);;

let MOI_S5S_SEG_DIM = prove
 (`!a b:real^3. ~(aff_dim(segment[a,b]) = &2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFF_DIM_SEGMENT] THEN COND_CASES_TAC THEN
  CONV_TAC INT_REDUCE_CONV);;

let MOI_S5S_INF_INJ = prove
 (`!(k:(real^3->bool)->bool) c d z z' y.
     moi_s5s_hyp k c d /\ c <= y$3 /\ y$3 <= d /\
     moi_s5s_inf k c d z y /\ moi_s5s_inf k c d z' y /\ sndcart z = sndcart z'
     ==> z = z'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5s_inf] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS(REWRITE_RULE[moi_s5s_hyp] th)))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `!t (a:real^3) b. t IN k /\ aff_dim t = &2 /\ y IN relative_interior t /\
                     segment[a,b] IN k /\ ~(a$3 = b$3) /\
                     y IN relative_interior(segment[a,b]) ==> F`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`;
                   `segment[a:real^3,b]`; `y:real^3`] MOI_S5S_RELINT_UNIQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[MOI_S5S_SEG_DIM];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `t':real^3->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `a':real^3` (X_CHOOSE_THEN `b':real^3` STRIP_ASSUME_TAC))) THENL
   [MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`; `t':real^3->bool`;
                   `y:real^3`] MOI_S5S_RELINT_UNIQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `t':real^3->bool`;
                   `y:real^3`] MOI_S5S_CLASSIFY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ALL_TAC] THEN
    STRIP_TAC THENL [ASM_MESON_TAC[MOI_S5S_SEG_DIM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `t':real^3->bool`]
      MOI_S5S_DAT) THEN
    ANTS_TAC THENL
     [MAP_EVERY EXISTS_TAC [`ap:real^3`; `r1:real^3`; `r2:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`;
                   `FST(moi_s5s_dat k c d (t':real^3->bool))`;
                   `FST(SND(moi_s5s_dat k c d (t':real^3->bool)))`;
                   `SND(SND(moi_s5s_dat k c d (t':real^3->bool)))`] MOI_S5S_TRI_TRAP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o el 4 o CONJUNCTS) THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `segment[a:real^3,b]`;
                   `segment[a':real^3,b']`; `y:real^3`] MOI_S5S_RELINT_UNIQ) THEN
    ASM_REWRITE_TAC[SEGMENT_EQ] THEN
    REWRITE_TAC[SET_RULE `{a:real^3,b} = {c,d} <=> a = c /\ b = d \/ a = d /\ b = c`] THEN
    ONCE_REWRITE_TAC[PASTECART_EQ] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S5S_PT_SYM THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem SLAB_PRODUCT.                                             *)
(* ------------------------------------------------------------------------- *)

let SLAB_PRODUCT = prove
 (MOI_S35_SLAB_PRODUCT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s5s_hyp k c d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s5s_hyp]; ALL_TAC] THEN
  ABBREV_TAC
   `pp = IMAGE (\t:real^3->bool. {x | x IN t /\ x$3 = c} PCROSS
                                interval[vec 0:real^1,vec 1]) k` THEN
  SUBGOAL_THEN
   `{x | x IN UNIONS (k:(real^3->bool)->bool) /\ x$3 = c} PCROSS
    interval[vec 0:real^1,vec 1] = UNIONS pp` ASSUME_TAC THENL
   [EXPAND_TAC "pp" THEN
    REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIONS;
                EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN pp
                    ==> compact p /\ pl_map_on p (moi_s5s_f k c d)` ASSUME_TAC THENL
   [EXPAND_TAC "pp" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `t:real^3->bool`]
      MOI_S5S_PIECE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (pp:(real^(3,1)finite_sum->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "pp" THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x s. x IN UNIONS k /\ x$3 = c /\ s IN interval[vec 0:real^1,vec 1]
          ==> (moi_s5s_f k c d (pastecart x s))$3 = c + drop s * (d - c) /\
              moi_s5s_inf k c d (pastecart x s) (moi_s5s_f k c d (pastecart x s))`
  (LABEL_TAC "lev") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `t:real^3->bool`]
      MOI_S5S_PIECE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (x:real^3) (s:real^1)` o el 3 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM; SNDCART_PASTECART];
    ALL_TAC] THEN
  EXISTS_TAC `moi_s5s_f k c d` THEN
  SUBGOAL_THEN
   `IMAGE (moi_s5s_f k c d)
          ({x | x IN UNIONS k /\ x$3 = c} PCROSS interval[vec 0:real^1,vec 1]) =
    {x | x IN UNIONS k /\ c <= x$3 /\ x$3 <= d}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_UNIONS] THEN EXPAND_TAC "pp" THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    SUBGOAL_THEN
     `!t. t IN k
          ==> IMAGE (moi_s5s_f k c d)
                ({x | x IN t /\ x$3 = c} PCROSS interval[vec 0:real^1,vec 1]) =
              {y | y IN t /\ c <= y$3 /\ y$3 <= d}`
    (LABEL_TAC "img") THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `t:real^3->bool`]
        MOI_S5S_PIECE) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(y:real^3) IN IMAGE (moi_s5s_f k c d)
                     ({x | x IN t /\ x$3 = c} PCROSS interval[vec 0:real^1,vec 1])` THEN
      USE_THEN "img" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(t:real^3->bool) IN k`)]) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)
        STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "img" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(t:real^3->bool) IN k`)]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on ({x | x IN UNIONS k /\ x$3 = c} PCROSS interval[vec 0:real^1,vec 1])
              (moi_s5s_f k c d)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5S_PL_UNIONS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g. homeomorphism
          ({x | x IN UNIONS k /\ x$3 = c} PCROSS interval[vec 0:real^1,vec 1],
           {x | x IN UNIONS k /\ c <= x$3 /\ x$3 <= d})
          (moi_s5s_f k c d,g)`
  (X_CHOOSE_TAC `g:real^3->real^(3,1)finite_sum`) THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real^1`; `x':real^3`; `s':real^1`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(moi_s5s_f k c d (pastecart x s))$3 = c + drop s * (d - c) /\
      moi_s5s_inf k c d (pastecart x s) (moi_s5s_f k c d (pastecart x s))`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "lev" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(moi_s5s_f k c d (pastecart x' s'))$3 = c + drop s' * (d - c) /\
      moi_s5s_inf k c d (pastecart x' s') (moi_s5s_f k c d (pastecart x' s'))`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "lev" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s:real^1 = s'` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ] THEN
      MATCH_MP_TAC(REAL_FIELD `c < d /\ c + s * (d - c) = c + s' * (d - c) ==> s = s'`) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(moi_s5s_f k c d (pastecart x s))$3 = c + drop s * (d - c)` THEN
      UNDISCH_TAC `(moi_s5s_f k c d (pastecart x' s'))$3 = c + drop s' * (d - c)` THEN
      UNDISCH_TAC `moi_s5s_f k c d (pastecart x s) = moi_s5s_f k c d (pastecart x' s')` THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`;
                   `pastecart (x:real^3) (s:real^1)`; `pastecart (x':real^3) (s':real^1)`;
                   `moi_s5s_f k c d (pastecart x s)`] MOI_S5S_INF_INJ) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `&0 <= drop(s:real^1) * (d - c) /\ drop s * (d - c) <= d - c`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `moi_s5s_f k c d (pastecart x s) = moi_s5s_f k c d (pastecart x' s')` THEN
      DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[SNDCART_PASTECART]];
    ALL_TAC] THEN
  EXISTS_TAC `g:real^3->real^(3,1)finite_sum` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "lev" (MP_TAC o SPECL [`x:real^3`; `s:real^1`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real`; `d:real`; `t:real^3->bool`]
    MOI_S5S_PIECE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3` o el 4 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[]);;

