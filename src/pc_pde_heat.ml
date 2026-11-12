(* ========================================================================= *)
(* Unit pc_pde_heat: Fourier series on the torus T^N = R^N / Z^N (maps on    *)
(* real^N, periodicity a predicate) and the flat heat equation               *)
(* u_t = Delta u + f with smooth periodic data, smooth up to                 *)
(* t = 0 (PDE_TORUS_HEAT).  The Fourier layer generalizes the 2-dimensional  *)
(* Fourier layer of src/ns_torus_inv.ml of the Navier_Stokes development     *)
(* (github.com/hol-light-family/Navier_Stokes) to dimension N.               *)
(*                                                                           *)
(* First the lattice Z^N and the shells infnorm k = m.                       *)
(* ========================================================================= *)

needs "src/pc_pde_torus.ml";;
needs "src/pc_pde_st.ml";;

prioritize_real();;
type_invention_error := true;;

let pde_zlat = new_definition
 `pde_zlat (k:real^N) <=> !i. 1 <= i /\ i <= dimindex(:N) ==> integer(k$i)`;;

let pde_shell = new_definition
 `pde_shell m = {k:real^N | pde_zlat k /\ infnorm k = &m}`;;

(* Cosine and sine coefficients over the unit cube:                         *)
(*   u = sum over k in Z^N of cos(2 pi k.x) fc u k + sin(2 pi k.x) fs u k.  *)

let pde_fc = new_definition
 `pde_fc (u:real^N->real^K) (k:real^N) =
    integral (interval[vec 0,vec 1]) (\x. cos(&2 * pi * (k dot x)) % u x)`;;

let pde_fs = new_definition
 `pde_fs (u:real^N->real^K) (k:real^N) =
    integral (interval[vec 0,vec 1]) (\x. sin(&2 * pi * (k dot x)) % u x)`;;

let pde_mode = new_definition
 `pde_mode (u:real^N->real^K) (k:real^N) (x:real^N) =
    cos(&2 * pi * (k dot x)) % pde_fc u k + sin(&2 * pi * (k dot x)) % pde_fs u k`;;

let pde_fsh = new_definition
 `pde_fsh (u:real^N->real^K) m (x:real^N) = vsum (pde_shell m) (\k. pde_mode u k x)`;;

(* Lattice points. *)

let PDE_FT_ZLAT_DOT = prove
 (`!k a:real^N. pde_zlat k /\ pde_zlat a ==> integer(k dot a)`,
  REWRITE_TAC[pde_zlat; dot] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGER_SUM THEN REWRITE_TAC[IN_NUMSEG] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;

let PDE_FT_ZLAT_CLAUSES = prove
 (`pde_zlat(vec 0:real^N) /\
   (!i. pde_zlat(basis i:real^N)) /\
   (!a b:real^N. pde_zlat a /\ pde_zlat b ==> pde_zlat(a + b)) /\
   (!a b:real^N. pde_zlat a /\ pde_zlat b ==> pde_zlat(a - b)) /\
   (!a:real^N. pde_zlat a ==> pde_zlat(--a))`,
  SIMP_TAC[pde_zlat; VEC_COMPONENT; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
           VECTOR_NEG_COMPONENT; BASIS_COMPONENT; INTEGER_CLOSED] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[INTEGER_CLOSED]);;

let PDE_FT_INTEGER_SHIFT = prove
 (`!x m. integer x /\ abs x <= &m ==> ?i. i <= 2 * m /\ x = &i - &m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x + &m` INTEGER_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
  EXISTS_TAC `i:num` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
  ASM_REAL_ARITH_TAC);;

(* Shells. *)

let PDE_FT_INFNORM_ATTAINED = prove
 (`!k:real^N. ?j. 1 <= j /\ j <= dimindex(:N) /\ infnorm k = abs(k$j)`,
  GEN_TAC THEN MP_TAC(INST [`k:real^N`,`x:real^N`] INFNORM_SET_LEMMA) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUP_FINITE) THEN
  REWRITE_TAC[GSYM infnorm; IN_ELIM_THM] THEN MESON_TAC[]);;

let PDE_FT_SHELL_ZLAT = prove
 (`!m k:real^N. k IN pde_shell m ==> pde_zlat k`,
  SIMP_TAC[pde_shell; IN_ELIM_THM]);;

let PDE_FT_SHELL_COMPONENT = prove
 (`!m k:real^N i. k IN pde_shell m /\ 1 <= i /\ i <= dimindex(:N) ==> abs(k$i) <= &m`,
  REWRITE_TAC[pde_shell; IN_ELIM_THM] THEN MESON_TAC[COMPONENT_LE_INFNORM]);;

let PDE_FT_SHELL_COORD = prove
 (`!m k:real^N. k IN pde_shell m
                ==> ?j. 1 <= j /\ j <= dimindex(:N) /\ abs(k$j) = &m`,
  REWRITE_TAC[pde_shell; IN_ELIM_THM] THEN MESON_TAC[PDE_FT_INFNORM_ATTAINED]);;

let PDE_FT_SHELL_NEG = prove
 (`!m k:real^N. --k IN pde_shell m <=> k IN pde_shell m`,
  REWRITE_TAC[pde_shell; IN_ELIM_THM; INFNORM_NEG] THEN
  MESON_TAC[PDE_FT_ZLAT_CLAUSES; VECTOR_NEG_NEG]);;

let PDE_FT_SHELL_EXISTS = prove
 (`!k:real^N. pde_zlat k ==> ?m. k IN pde_shell m`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k:real^N` PDE_FT_INFNORM_ATTAINED) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `abs((k:real^N)$j)` INTEGER_POS) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `integer(abs((k:real^N)$j))` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[pde_zlat; INTEGER_CLOSED]; ALL_TAC] THEN
  ASM_REWRITE_TAC[pde_shell; IN_ELIM_THM]);;

let PDE_FT_SHELL_UNIQUE = prove
 (`!m n k:real^N. k IN pde_shell m /\ k IN pde_shell n ==> m = n`,
  REWRITE_TAC[pde_shell; IN_ELIM_THM] THEN MESON_TAC[REAL_OF_NUM_EQ]);;

let PDE_FT_SHELL_0 = prove
 (`!k:real^N. k IN pde_shell 0 <=> k = vec 0`,
  GEN_TAC THEN REWRITE_TAC[pde_shell; IN_ELIM_THM; INFNORM_EQ_0] THEN
  MESON_TAC[PDE_FT_ZLAT_CLAUSES]);;

let PDE_FT_SHELL_SUBSET = prove
 (`!m. pde_shell m SUBSET
       IMAGE (\f. (lambda i. &(f i) - &m):real^N)
             {f | (!i. i IN 1..dimindex(:N) ==> f i IN 0..2 * m) /\
                  (!i. ~(i IN 1..dimindex(:N)) ==> f i = 0)}`,
  GEN_TAC THEN REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
  X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. ?j. 1 <= i /\ i <= dimindex(:N) ==> j <= 2 * m /\ (k:real^N)$i = &j - &m`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `1 <= i /\ i <= dimindex(:N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_FT_INTEGER_SHIFT THEN
    ASM_MESON_TAC[PDE_FT_SHELL_ZLAT; pde_zlat; PDE_FT_SHELL_COMPONENT];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `g:num->num`) THEN
  EXISTS_TAC `\i. if 1 <= i /\ i <= dimindex(:N) then (g:num->num) i else 0` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let PDE_FT_SHELL_FINITE = prove
 (`!m. FINITE(pde_shell m:real^N->bool)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `IMAGE (\f. (lambda i. &(f i) - &m):real^N)
          {f | (!i. i IN 1..dimindex(:N) ==> f i IN 0..2 * m) /\
               (!i. ~(i IN 1..dimindex(:N)) ==> f i = 0)}` THEN
  REWRITE_TAC[PDE_FT_SHELL_SUBSET] THEN MATCH_MP_TAC FINITE_IMAGE THEN
  MATCH_MP_TAC FINITE_FUNSPACE THEN REWRITE_TAC[FINITE_NUMSEG]);;

let PDE_FT_SHELL_CARD = prove
 (`!m. CARD(pde_shell m:real^N->bool) <= (2 * m + 1) EXP dimindex(:N)`,
  GEN_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
   `CARD(IMAGE (\f. (lambda i. &(f i) - &m):real^N)
          {f | (!i. i IN 1..dimindex(:N) ==> f i IN 0..2 * m) /\
               (!i. ~(i IN 1..dimindex(:N)) ==> f i = 0)})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[PDE_FT_SHELL_SUBSET] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_FUNSPACE THEN REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
   `CARD {f | (!i. i IN 1..dimindex(:N) ==> f i IN 0..2 * m) /\
              (!i. ~(i IN 1..dimindex(:N)) ==> f i = 0)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_LE THEN
    MATCH_MP_TAC FINITE_FUNSPACE THEN REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `2 * m + 1`; `0..2 * m`; `dimindex(:N)`; `1..dimindex(:N)`]
                HAS_SIZE_FUNSPACE) THEN
  REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[HAS_SIZE; FINITE_NUMSEG; CARD_NUMSEG] THEN ARITH_TAC;
    SIMP_TAC[HAS_SIZE; LE_REFL]]);;

(* ========================================================================= *)
(* The modes cos(2 pi k.x) A + sin(2 pi k.x) B (periodicity, derivatives,    *)
(* smoothness, closure under partials with the bound (2 pi infnorm k)^n).    *)
(* The scalar lemmas are those of ns_torus_inv.ml (stated there on any       *)
(* real^M); their names here begin with PDE_FT.                              *)
(* ========================================================================= *)

let PDE_FT_COS_SIN_PER = prove
 (`!k a y:real^N.
     pde_zlat k /\ pde_zlat a
     ==> cos(&2 * pi * (k dot (y + a))) = cos(&2 * pi * (k dot y)) /\
         sin(&2 * pi * (k dot (y + a))) = sin(&2 * pi * (k dot y))`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP PDE_FT_ZLAT_DOT) THEN
  REWRITE_TAC[DOT_RADD; REAL_ARITH
   `&2 * pi * (x + z) = &2 * pi * x + (&2 * pi) * z`] THEN
  ASM_SIMP_TAC[COS_ADD; SIN_ADD; COS_INTEGER_2PI; SIN_INTEGER_2PI] THEN
  REAL_ARITH_TAC);;

let PDE_FT_LINEAR_PHASE = prove
 (`!k:real^M. linear (\y. lift(&2 * pi * (k dot y)))`,
  GEN_TAC THEN REWRITE_TAC[linear] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
  REAL_ARITH_TAC);;

let PDE_FT_HAS_DERIVATIVE_LIFT_COS = prove
 (`!(k:real^M) y.
     ((\y. lift(cos(&2 * pi * (k dot y)))) has_derivative
      (\h. lift(--(sin(&2 * pi * (k dot y))) * (&2 * pi * (k dot h))))) (at y)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\y:real^M. lift(cos(&2 * pi * (k dot y)))) =
                (lift o cos o drop) o (\y. lift(&2 * pi * (k dot y)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^M. lift(--(sin(&2 * pi * (k dot y))) * (&2 * pi * (k dot h)))) =
    (\x. --(sin(&2 * pi * (k dot y))) % x) o (\h. lift(&2 * pi * (k dot h)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[PDE_FT_LINEAR_PHASE];
    REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT; HAS_REAL_DERIVATIVE_COS]]);;

let PDE_FT_HAS_DERIVATIVE_LIFT_SIN = prove
 (`!(k:real^M) y.
     ((\y. lift(sin(&2 * pi * (k dot y)))) has_derivative
      (\h. lift(cos(&2 * pi * (k dot y)) * (&2 * pi * (k dot h))))) (at y)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\y:real^M. lift(sin(&2 * pi * (k dot y)))) =
                (lift o sin o drop) o (\y. lift(&2 * pi * (k dot y)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^M. lift(cos(&2 * pi * (k dot y)) * (&2 * pi * (k dot h)))) =
    (\x. cos(&2 * pi * (k dot y)) % x) o (\h. lift(&2 * pi * (k dot h)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[PDE_FT_LINEAR_PHASE];
    REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT; HAS_REAL_DERIVATIVE_SIN]]);;

let PDE_FT_SMOOTH_PHASE = prove
 (`!k:real^M. smooth_map_on (:real^M) (\y. lift(&2 * pi * (k dot y)))`,
  GEN_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; PDE_FT_LINEAR_PHASE]);;

let PDE_FT_SMOOTH_LIFT_COS_SIN = prove
 (`!k:real^M. smooth_map_on (:real^M) (\y. lift(cos(&2 * pi * (k dot y)))) /\
              smooth_map_on (:real^M) (\y. lift(sin(&2 * pi * (k dot y))))`,
  GEN_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^M)`; `\y:real^M. lift(&2 * pi * (k dot y))`]
      SMOOTH_MAP_ON_LIFT_COS);
    MP_TAC(ISPECL [`(:real^M)`; `\y:real^M. lift(&2 * pi * (k dot y))`]
      SMOOTH_MAP_ON_LIFT_SIN)] THEN
  REWRITE_TAC[OPEN_UNIV; LIFT_DROP; PDE_FT_SMOOTH_PHASE]);;

let PDE_FT_CONT_LIFT_COS_SIN = prove
 (`!k:real^M. (\y. lift(cos(&2 * pi * (k dot y)))) continuous_on (:real^M) /\
              (\y. lift(sin(&2 * pi * (k dot y)))) continuous_on (:real^M)`,
  MESON_TAC[PDE_FT_SMOOTH_LIFT_COS_SIN; SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let PDE_FT_PD_LIFT_COS_SIN = prove
 (`!(k:real^M) j y.
     1 <= j /\ j <= dimindex(:M)
     ==> partial_derivative j (\y. lift(cos(&2 * pi * (k dot y)))) y =
         lift(--(&2 * pi * k$j) * sin(&2 * pi * (k dot y))) /\
         partial_derivative j (\y. lift(sin(&2 * pi * (k dot y)))) y =
         lift((&2 * pi * k$j) * cos(&2 * pi * (k dot y)))`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`k:real^M`; `y:real^M`] PDE_FT_HAS_DERIVATIVE_LIFT_COS);
    MP_TAC(ISPECL [`k:real^M`; `y:real^M`] PDE_FT_HAS_DERIVATIVE_LIFT_SIN)] THEN
  DISCH_THEN(SUBST1_TAC o SPEC `j:num` o
    MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
  ASM_SIMP_TAC[DOT_BASIS; LIFT_EQ] THEN REAL_ARITH_TAC);;

let PDE_FT_PD_LIFT_COS_SIN_FUN = prove
 (`!(k:real^M) j.
     1 <= j /\ j <= dimindex(:M)
     ==> partial_derivative j (\y. lift(cos(&2 * pi * (k dot y)))) =
         (\y. lift(--(&2 * pi * k$j) * sin(&2 * pi * (k dot y)))) /\
         partial_derivative j (\y. lift(sin(&2 * pi * (k dot y)))) =
         (\y. lift((&2 * pi * k$j) * cos(&2 * pi * (k dot y))))`,
  SIMP_TAC[FUN_EQ_THM; PDE_FT_PD_LIFT_COS_SIN]);;

(* Vector modes. *)

let PDE_FT_VMODE_HAS_DERIVATIVE = prove
 (`!(k:real^N) (A:real^K) B y.
     ((\x. cos(&2 * pi * (k dot x)) % A + sin(&2 * pi * (k dot x)) % B) has_derivative
      (\h. (--(sin(&2 * pi * (k dot y))) * (&2 * pi * (k dot h))) % A +
           (cos(&2 * pi * (k dot y)) * (&2 * pi * (k dot h))) % B)) (at y)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
   [MP_TAC(INST [`at (y:real^N)`,`net:(real^N)net`]
     (ISPECL [`\x:real^N. lift(cos(&2 * pi * (k dot x)))`;
              `\h:real^N. lift(--(sin(&2 * pi * (k dot y))) * (&2 * pi * (k dot h)))`;
              `A:real^K`] HAS_DERIVATIVE_VMUL_DROP)) THEN
    REWRITE_TAC[LIFT_DROP; PDE_FT_HAS_DERIVATIVE_LIFT_COS];
    MP_TAC(INST [`at (y:real^N)`,`net:(real^N)net`]
     (ISPECL [`\x:real^N. lift(sin(&2 * pi * (k dot x)))`;
              `\h:real^N. lift(cos(&2 * pi * (k dot y)) * (&2 * pi * (k dot h)))`;
              `B:real^K`] HAS_DERIVATIVE_VMUL_DROP)) THEN
    REWRITE_TAC[LIFT_DROP; PDE_FT_HAS_DERIVATIVE_LIFT_SIN]]);;

let PDE_FT_VMODE_PARTIAL = prove
 (`!(k:real^N) (A:real^K) B j.
     1 <= j /\ j <= dimindex(:N)
     ==> partial_derivative j
           (\x. cos(&2 * pi * (k dot x)) % A + sin(&2 * pi * (k dot x)) % B) =
         (\x. cos(&2 * pi * (k dot x)) % ((&2 * pi * k$j) % B) +
              sin(&2 * pi * (k dot x)) % (--(&2 * pi * k$j) % A))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
  MP_TAC(ISPECL [`k:real^N`; `A:real^K`; `B:real^K`; `y:real^N`]
                PDE_FT_VMODE_HAS_DERIVATIVE) THEN
  DISCH_THEN(SUBST1_TAC o SPEC `j:num` o
    MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
  ASM_SIMP_TAC[DOT_BASIS] THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; VECTOR_MUL_LNEG] THEN
  REWRITE_TAC[REAL_MUL_SYM] THEN VECTOR_ARITH_TAC);;

let PDE_FT_VMODE_SMOOTH = prove
 (`!(k:real^N) (A:real^K) B.
     smooth_map_on (:real^N)
       (\x. cos(&2 * pi * (k dot x)) % A + sin(&2 * pi * (k dot x)) % B)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:real^N. cos(&2 * pi * (k dot x)) % (A:real^K)) =
                  (\v:real^1. drop v % A) o (\x. lift(cos(&2 * pi * (k dot x))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC];
    SUBGOAL_THEN `(\x:real^N. sin(&2 * pi * (k dot x)) % (B:real^K)) =
                  (\v:real^1. drop v % B) o (\x. lift(sin(&2 * pi * (k dot x))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  REWRITE_TAC[OPEN_UNIV; PDE_FT_SMOOTH_LIFT_COS_SIN] THEN
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC);;

let PDE_FT_VMODE_NORM = prove
 (`!(k:real^N) (A:real^K) B x.
     norm(cos(&2 * pi * (k dot x)) % A + sin(&2 * pi * (k dot x)) % B) <= norm A + norm B`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(NORM_ARITH
   `norm(a:real^K) <= x /\ norm(b:real^K) <= y ==> norm(a + b) <= x + y`) THEN
  REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; COS_BOUND; SIN_BOUND]);;

let PDE_FT_VMODE_ZPER = prove
 (`!(k:real^N) (A:real^K) B.
     pde_zlat k
     ==> pde_zper (\x. cos(&2 * pi * (k dot x)) % A + sin(&2 * pi * (k dot x)) % B)`,
  SIMP_TAC[pde_zper; PDE_FT_COS_SIN_PER; PDE_FT_ZLAT_CLAUSES]);;

let PDE_FT_INFNORM_COMPONENT = prove
 (`!(k:real^N) j. 1 <= j /\ j <= dimindex(:N)
                  ==> abs(&2 * pi * k$j) <= &2 * pi * infnorm k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_PI; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[PI_POS_LE] THEN
  ASM_SIMP_TAC[COMPONENT_LE_INFNORM]);;

let PDE_FT_VMODE_ITERATED = prove
 (`!l (k:real^N).
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> !(A:real^K) B.
           ?A' B'. iterated_partial l
                     (\x. cos(&2 * pi * (k dot x)) % A + sin(&2 * pi * (k dot x)) % B) =
                   (\x. cos(&2 * pi * (k dot x)) % A' + sin(&2 * pi * (k dot x)) % B') /\
                   norm A' + norm B' <=
                   (&2 * pi * infnorm k) pow (LENGTH l) * (norm A + norm B)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; iterated_partial; LENGTH] THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`A:real^K`; `B:real^K`] THEN
    REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_LE_REFL; ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `k:real^N` THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`A:real^K`; `B:real^K`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`A:real^K`; `B:real^K`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real^K` (X_CHOOSE_THEN `B1:real^K` STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[PDE_FT_VMODE_PARTIAL] THEN
  EXISTS_TAC `(&2 * pi * (k:real^N)$h) % (B1:real^K)` THEN
  EXISTS_TAC `--(&2 * pi * (k:real^N)$h) % (A1:real^K)` THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_NEG] THEN
  MP_TAC(ISPECL [`k:real^N`; `h:num`] PDE_FT_INFNORM_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= &2 * pi * infnorm(k:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PI_POS_LE; INFNORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * pi * infnorm(k:real^N)) * (norm(B1:real^K) + norm(A1:real^K))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b c d:real. &0 <= a /\ b <= c * d ==> a * b <= (a * c) * d`
  MATCH_MP_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Fourier coefficients (integration by parts, orthogonality of the modes,   *)
(* coefficients of shell sums, decay), following ns_torus_inv.ml with the    *)
(* unit-cube integral of a partial (PDE_CUBE_INTEGRAL_PARTIAL) in place of   *)
(* Fubini.                                                                   *)
(* ========================================================================= *)

let PDE_FT_CONT_INTEGRABLE = prove
 (`!f:real^N->real^K.
     f continuous_on (:real^N) ==> f integrable_on interval[vec 0,vec 1]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let PDE_FT_CONT_MODE_MUL = prove
 (`!(k:real^N) (g:real^N->real^K).
     g continuous_on (:real^N)
     ==> (\y. cos(&2 * pi * (k dot y)) % g y) continuous_on (:real^N) /\
         (\y. sin(&2 * pi * (k dot y)) % g y) continuous_on (:real^N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  ASM_REWRITE_TAC[o_DEF; PDE_FT_CONT_LIFT_COS_SIN]);;

let PDE_FT_INTEGRAL_REAL_MUL = prove
 (`!(phi:real^N->real) (A:real^K) s.
     (\y. lift(phi y)) integrable_on s
     ==> integral s (\y. phi y % A) = drop(integral s (\y. lift(phi y))) % A`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^N. lift(phi y)`; `s:real^N->bool`;
                 `\x:real^1. drop x % (A:real^K)`] INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let PDE_FT_INTEGRAL_SCALE = prove
 (`!c (phi:real^N->real) (f:real^N->real^K) s.
     (\y. phi y % f y) integrable_on s
     ==> integral s (\y. (c * phi y) % f y) = c % integral s (\y. phi y % f y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^N. (c * phi y) % (f:real^N->real^K) y) =
                (\y. c % (phi y % f y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC]; ASM_SIMP_TAC[INTEGRAL_CMUL]]);;

let PDE_FT_LIFT_COS_SIN_ZPER = prove
 (`!k:real^N. pde_zlat k
              ==> pde_zper (\y. lift(cos(&2 * pi * (k dot y)))) /\
                  pde_zper (\y. lift(sin(&2 * pi * (k dot y))))`,
  SIMP_TAC[pde_zper; PDE_FT_COS_SIN_PER; PDE_FT_ZLAT_CLAUSES]);;

(* Integration by parts on the torus. *)

let PDE_FT_IBP_PRODUCT = prove
 (`!(a:real^N->real^1) (f:real^N->real^K) j.
     smooth_map_on (:real^N) a /\ pde_zper a /\
     smooth_map_on (:real^N) f /\ pde_zper f /\ 1 <= j /\ j <= dimindex(:N)
     ==> integral (interval[vec 0,vec 1]) (\y. drop(a y) % partial_derivative j f y) =
         --(integral (interval[vec 0,vec 1])
              (\y. drop(partial_derivative j a y) % f y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^N. drop((a:real^N->real^1) y) % (f:real^N->real^K) y`; `j:num`]
    PDE_CUBE_INTEGRAL_PARTIAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_MUL_DROP_OPEN; OPEN_UNIV] THEN
    REWRITE_TAC[pde_zper] THEN REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `partial_derivative j (\y:real^N. drop((a:real^N->real^1) y) % (f:real^N->real^K) y) =
    (\y. drop(a y) % partial_derivative j f y + drop(partial_derivative j a y) % f y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
    MATCH_MP_TAC PARTIAL_DERIVATIVE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y:real^N. drop((a:real^N->real^1) y) % partial_derivative j (f:real^N->real^K) y)
    integrable_on interval[vec 0,vec 1] /\
    (\y:real^N. drop(partial_derivative j (a:real^N->real^1) y) % (f:real^N->real^K) y)
    integrable_on interval[vec 0,vec 1]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_FT_CONT_INTEGRABLE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD] THEN VECTOR_ARITH_TAC);;

let PDE_FT_FC_PARTIAL = prove
 (`!(f:real^N->real^K) k j.
     smooth_map_on (:real^N) f /\ pde_zper f /\ pde_zlat k /\ 1 <= j /\ j <= dimindex(:N)
     ==> pde_fc (partial_derivative j f) k = (&2 * pi * k$j) % pde_fs f k /\
         pde_fs (partial_derivative j f) k = --(&2 * pi * k$j) % pde_fc f k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^K) continuous_on (:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  REWRITE_TAC[pde_fc; pde_fs] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\y:real^N. lift(cos(&2 * pi * (k dot y)))`;
                   `f:real^N->real^K`; `j:num`] PDE_FT_IBP_PRODUCT) THEN
    ASM_SIMP_TAC[PDE_FT_SMOOTH_LIFT_COS_SIN; PDE_FT_LIFT_COS_SIN_ZPER;
                 PDE_FT_PD_LIFT_COS_SIN; LIFT_DROP] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[PDE_FT_INTEGRAL_SCALE; PDE_FT_CONT_INTEGRABLE; PDE_FT_CONT_MODE_MUL] THEN
    VECTOR_ARITH_TAC;
    MP_TAC(ISPECL [`\y:real^N. lift(sin(&2 * pi * (k dot y)))`;
                   `f:real^N->real^K`; `j:num`] PDE_FT_IBP_PRODUCT) THEN
    ASM_SIMP_TAC[PDE_FT_SMOOTH_LIFT_COS_SIN; PDE_FT_LIFT_COS_SIN_ZPER;
                 PDE_FT_PD_LIFT_COS_SIN; LIFT_DROP] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[PDE_FT_INTEGRAL_SCALE; PDE_FT_CONT_INTEGRABLE; PDE_FT_CONT_MODE_MUL] THEN
    VECTOR_ARITH_TAC]);;

(* Integrals of the modes and orthogonality. *)

let PDE_FT_INT_MODE = prove
 (`!k:real^N.
     pde_zlat k
     ==> integral (interval[vec 0,vec 1]) (\y. lift(cos(&2 * pi * (k dot y)))) =
         (if k = vec 0 then vec 1 else vec 0) /\
         integral (interval[vec 0,vec 1]) (\y. lift(sin(&2 * pi * (k dot y)))) = vec 0`,
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `k:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[DOT_LZERO; REAL_MUL_RZERO; COS_0; SIN_0; LIFT_NUM; INTEGRAL_0;
                    INTEGRAL_CONST; CONTENT_UNIT; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?j. 1 <= j /\ j <= dimindex(:N) /\ ~((k:real^N)$j = &0)`
    (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `~(k:real^N = vec 0)` THEN
    REWRITE_TAC[CART_EQ; VEC_COMPONENT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&2 * pi * (k:real^N)$j = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ENTIRE; PI_NZ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\y:real^N. lift(sin(&2 * pi * (k dot y)))`; `j:num`]
      PDE_CUBE_INTEGRAL_PARTIAL);
    MP_TAC(ISPECL [`\y:real^N. lift(cos(&2 * pi * (k dot y)))`; `j:num`]
      PDE_CUBE_INTEGRAL_PARTIAL)] THEN
  ASM_SIMP_TAC[PDE_FT_LIFT_COS_SIN_ZPER; PDE_FT_SMOOTH_LIFT_COS_SIN] THEN
  ASM_SIMP_TAC[PDE_FT_PD_LIFT_COS_SIN_FUN] THEN
  REWRITE_TAC[LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; PDE_FT_CONT_INTEGRABLE; PDE_FT_CONT_LIFT_COS_SIN;
               VECTOR_MUL_EQ_0; REAL_NEG_EQ_0]);;

let PDE_FT_PHASE_SUB_ADD = prove
 (`!k k' y:real^N.
     &2 * pi * (k dot y) - &2 * pi * (k' dot y) = &2 * pi * ((k - k') dot y) /\
     &2 * pi * (k dot y) + &2 * pi * (k' dot y) = &2 * pi * ((k + k') dot y)`,
  REWRITE_TAC[DOT_LSUB; DOT_LADD] THEN REAL_ARITH_TAC);;

let PDE_FT_INT_PROD = prove
 (`!k k':real^N.
     pde_zlat k /\ pde_zlat k'
     ==> integral (interval[vec 0,vec 1])
           (\y. lift(cos(&2 * pi * (k dot y)) * cos(&2 * pi * (k' dot y)))) =
         lift(((if k = k' then &1 else &0) + (if k = --k' then &1 else &0)) / &2) /\
         integral (interval[vec 0,vec 1])
           (\y. lift(cos(&2 * pi * (k dot y)) * sin(&2 * pi * (k' dot y)))) = vec 0 /\
         integral (interval[vec 0,vec 1])
           (\y. lift(sin(&2 * pi * (k dot y)) * cos(&2 * pi * (k' dot y)))) = vec 0 /\
         integral (interval[vec 0,vec 1])
           (\y. lift(sin(&2 * pi * (k dot y)) * sin(&2 * pi * (k' dot y)))) =
         lift(((if k = k' then &1 else &0) - (if k = --k' then &1 else &0)) / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_zlat(k - k':real^N) /\ pde_zlat(k + k')` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PDE_FT_ZLAT_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_COS_COS; REAL_MUL_COS_SIN; REAL_MUL_SIN_COS; REAL_MUL_SIN_SIN;
              PDE_FT_PHASE_SUB_ADD] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 = inv(&2) * x`; LIFT_CMUL; LIFT_ADD; LIFT_SUB] THEN
  SIMP_TAC[INTEGRAL_CMUL; INTEGRAL_ADD; INTEGRAL_SUB; INTEGRABLE_ADD; INTEGRABLE_SUB;
           PDE_FT_CONT_INTEGRABLE; PDE_FT_CONT_LIFT_COS_SIN] THEN
  ASM_SIMP_TAC[PDE_FT_INT_MODE; VECTOR_SUB_EQ;
               VECTOR_ARITH `k + k':real^N = vec 0 <=> k = --k'`] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_MUL_RZERO] THEN
  SPEC_TAC(`k:real^N = k'`,`b1:bool`) THEN SPEC_TAC(`k:real^N = --k'`,`b2:bool`) THEN
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b1:bool` THEN BOOL_CASES_TAC `b2:bool` THEN
  REWRITE_TAC[GSYM LIFT_NUM; GSYM LIFT_ADD; GSYM LIFT_SUB; GSYM LIFT_CMUL; LIFT_EQ] THEN
  REAL_ARITH_TAC);;

let PDE_FT_FC_FS_MODE = prove
 (`!k k':real^N (A:real^K) B.
     pde_zlat k /\ pde_zlat k'
     ==> pde_fc (\y. cos(&2 * pi * (k' dot y)) % A + sin(&2 * pi * (k' dot y)) % B) k =
         (((if k = k' then &1 else &0) + (if k = --k' then &1 else &0)) / &2) % A /\
         pde_fs (\y. cos(&2 * pi * (k' dot y)) % A + sin(&2 * pi * (k' dot y)) % B) k =
         (((if k = k' then &1 else &0) - (if k = --k' then &1 else &0)) / &2) % B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[pde_fc; pde_fs; VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `!c d:real^N->real. (\y. lift(c y)) continuous_on (:real^N) /\
                       (\y. lift(d y)) continuous_on (:real^N)
         ==> (\y. lift(c y * d y)) integrable_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_FT_CONT_INTEGRABLE THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c d:real^N->real (A:real^K).
       (\y. lift(c y)) continuous_on (:real^N) /\ (\y. lift(d y)) continuous_on (:real^N)
       ==> (\y. (c y * d y) % A) integrable_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_FT_CONT_INTEGRABLE THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST; o_DEF] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; PDE_FT_CONT_LIFT_COS_SIN] THEN
  ASM_SIMP_TAC[PDE_FT_INTEGRAL_REAL_MUL; PDE_FT_CONT_LIFT_COS_SIN] THEN
  ASM_SIMP_TAC[PDE_FT_INT_PROD; LIFT_DROP; DROP_VEC; VECTOR_MUL_LZERO;
               VECTOR_ADD_RID; VECTOR_ADD_LID]);;

(* Linearity and symmetry of the coefficients. *)

let PDE_FT_FC_VSUM = prove
 (`!(g:A->real^N->real^K) s k.
     FINITE s /\ (!a. a IN s ==> g a continuous_on (:real^N))
     ==> pde_fc (\y. vsum s (\a. g a y)) k = vsum s (\a. pde_fc (g a) k) /\
         pde_fs (\y. vsum s (\a. g a y)) k = vsum s (\a. pde_fs (g a) k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[pde_fc; pde_fs; GSYM VSUM_LMUL] THEN CONJ_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
      [`\(a:A) (y:real^N). cos(&2 * pi * (k dot y)) % (g:A->real^N->real^K) a y`;
       `interval[vec 0:real^N,vec 1]`; `s:A->bool`] INTEGRAL_VSUM));
    MP_TAC(BETA_RULE(ISPECL
      [`\(a:A) (y:real^N). sin(&2 * pi * (k dot y)) % (g:A->real^N->real^K) a y`;
       `interval[vec 0:real^N,vec 1]`; `s:A->bool`] INTEGRAL_VSUM))] THEN
  ASM_SIMP_TAC[PDE_FT_CONT_INTEGRABLE; PDE_FT_CONT_MODE_MUL; ETA_AX]);;

let PDE_FT_FC_NEG = prove
 (`!(f:real^N->real^K) k.
     f continuous_on (:real^N)
     ==> pde_fc f (--k) = pde_fc f k /\ pde_fs f (--k) = --(pde_fs f k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[pde_fc; pde_fs; DOT_LNEG; REAL_MUL_RNEG; COS_NEG; SIN_NEG;
              VECTOR_MUL_LNEG] THEN
  ASM_SIMP_TAC[INTEGRAL_NEG; PDE_FT_CONT_INTEGRABLE; PDE_FT_CONT_MODE_MUL]);;

let PDE_FT_CONT_MODE = prove
 (`!(f:real^N->real^K) k. pde_mode f k continuous_on (:real^N)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `pde_mode (f:real^N->real^K) k =
                (\y. cos(&2 * pi * (k dot y)) % pde_fc f k +
                     sin(&2 * pi * (k dot y)) % pde_fs f k)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; pde_mode]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[PDE_FT_VMODE_SMOOTH]);;

let PDE_FT_CONT_FSH = prove
 (`!(f:real^N->real^K) m. pde_fsh f m continuous_on (:real^N)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `pde_fsh (f:real^N->real^K) m =
                (\y. vsum (pde_shell m) (\k. pde_mode f k y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; pde_fsh]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
  REWRITE_TAC[PDE_FT_SHELL_FINITE; PDE_FT_CONT_MODE; ETA_AX]);;

let PDE_FT_VSUM_DELTA_FUN = prove
 (`!s (a:A) (g:A->real^K).
     vsum s (\x. if x = a then g x else vec 0) = if a IN s then g a else vec 0`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum s (\x:A. if x = a then (g:A->real^K) a else vec 0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN
    GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[VSUM_DELTA]]);;

let PDE_FT_DELTA_HALF = prove
 (`!b1 b2 (A:real^K).
     (((if b1 then &1 else &0) + (if b2 then &1 else &0)) / &2) % A =
     inv(&2) % ((if b1 then A else vec 0) + (if b2 then A else vec 0)) /\
     (((if b1 then &1 else &0) - (if b2 then &1 else &0)) / &2) % A =
     inv(&2) % ((if b1 then A else vec 0) - (if b2 then A else vec 0))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b1:bool` THEN BOOL_CASES_TAC `b2:bool` THEN
  REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let PDE_FT_FC_FSH = prove
 (`!(f:real^N->real^K) k m.
     f continuous_on (:real^N) /\ pde_zlat k
     ==> pde_fc (pde_fsh f m) k =
           (if k IN pde_shell m then pde_fc f k else vec 0) /\
         pde_fs (pde_fsh f m) k =
           (if k IN pde_shell m then pde_fs f k else vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_fsh (f:real^N->real^K) m =
                (\y. vsum (pde_shell m) (\k. pde_mode f k y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; pde_fsh]; ALL_TAC] THEN
  SIMP_TAC[PDE_FT_FC_VSUM; PDE_FT_SHELL_FINITE; PDE_FT_CONT_MODE; ETA_AX] THEN
  SUBGOAL_THEN
   `!k'. k' IN pde_shell m
         ==> pde_fc (pde_mode (f:real^N->real^K) k') k =
             inv(&2) % ((if k' = k then pde_fc f k' else vec 0) +
                        (if k' = --k then pde_fc f k' else vec 0)) /\
             pde_fs (pde_mode f k') k =
             inv(&2) % ((if k' = k then pde_fs f k' else vec 0) -
                        (if k' = --k then pde_fs f k' else vec 0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k':real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pde_zlat(k':real^N)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PDE_FT_SHELL_ZLAT]; ALL_TAC] THEN
    SUBGOAL_THEN `pde_mode (f:real^N->real^K) k' =
                  (\y. cos(&2 * pi * (k' dot y)) % pde_fc f k' +
                       sin(&2 * pi * (k' dot y)) % pde_fs f k')` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; pde_mode]; ALL_TAC] THEN
    ASM_SIMP_TAC[PDE_FT_FC_FS_MODE] THEN
    SUBGOAL_THEN `(k:real^N = --k' <=> k' = --k) /\ (k = k' <=> k' = k)`
      (fun th -> REWRITE_TAC[th]) THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[PDE_FT_DELTA_HALF];
    ALL_TAC] THEN
  ASM_SIMP_TAC[VSUM_EQ] THEN
  SIMP_TAC[VSUM_LMUL; VSUM_ADD; VSUM_SUB; PDE_FT_SHELL_FINITE; PDE_FT_VSUM_DELTA_FUN] THEN
  REWRITE_TAC[PDE_FT_SHELL_NEG] THEN
  ASM_SIMP_TAC[PDE_FT_FC_NEG] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VECTOR_ADD_RID; VECTOR_SUB_REFL; VECTOR_MUL_RZERO] THEN
  VECTOR_ARITH_TAC);;

(* Decay of the coefficients of smooth periodic maps. *)

let PDE_FT_REPLICATE_APPEND = prove
 (`!n (j:num). APPEND (REPLICATE n j) [j] = REPLICATE (SUC n) j`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; APPEND]);;

let PDE_FT_COEFF_DECAY = prove
 (`!n (f:real^N->real^K) k j B.
     smooth_map_on (:real^N) f /\ pde_zper f /\ pde_zlat k /\
     1 <= j /\ j <= dimindex(:N) /\
     (!y. y IN interval[vec 0,vec 1]
          ==> norm(iterated_partial (REPLICATE n j) f y) <= B)
     ==> norm(pde_fc f k) * (&2 * pi * abs(k$j)) pow n <= B /\
         norm(pde_fs f k) * (&2 * pi * abs(k$j)) pow n <= B`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[REPLICATE; iterated_partial; real_pow; REAL_MUL_RID] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `(f:real^N->real^K) continuous_on (:real^N)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
    REWRITE_TAC[pde_fc; pde_fs] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`\y:real^N. cos(&2 * pi * (k dot y)) % (f:real^N->real^K) y`;
        `vec 0:real^N`; `vec 1:real^N`;
        `integral (interval[vec 0:real^N,vec 1])
           (\y:real^N. cos(&2 * pi * (k dot y)) % (f:real^N->real^K) y)`;
        `B:real`] HAS_INTEGRAL_BOUND);
      MP_TAC(ISPECL
       [`\y:real^N. sin(&2 * pi * (k dot y)) % (f:real^N->real^K) y`;
        `vec 0:real^N`; `vec 1:real^N`;
        `integral (interval[vec 0:real^N,vec 1])
           (\y:real^N. sin(&2 * pi * (k dot y)) % (f:real^N->real^K) y)`;
        `B:real`] HAS_INTEGRAL_BOUND)] THEN
    REWRITE_TAC[CONTENT_UNIT; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; PDE_FT_CONT_INTEGRABLE;
                 PDE_FT_CONT_MODE_MUL] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `norm((f:real^N->real^K) (vec 0))` THEN
       REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       REWRITE_TAC[IN_INTERVAL; VEC_COMPONENT] THEN REAL_ARITH_TAC;
       ALL_TAC]) THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE; COS_BOUND; SIN_BOUND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`partial_derivative j (f:real^N->real^K)`; `k:real^N`; `j:num`; `B:real`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV; PDE_ZPER_PARTIAL] THEN
    SUBGOAL_THEN
     `iterated_partial (REPLICATE n j) (partial_derivative j (f:real^N->real^K)) =
      iterated_partial (REPLICATE (SUC n) j) f`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM PDE_FT_REPLICATE_APPEND; ITERATED_PARTIAL_APPEND;
                  iterated_partial];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PDE_FT_FC_PARTIAL] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_NEG; real_pow] THEN
  SUBGOAL_THEN `abs(&2 * pi * (k:real^N)$j) = &2 * pi * abs(k$j)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_PI]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Completeness of the trigonometric system on T^N (as in ns_torus_inv.ml,   *)
(* in dimension N): trigonometric polynomials form an algebra; polynomials   *)
(* in the coordinates of the embedding y |-> (cos 2 pi y_i, sin 2 pi y_i)_i  *)
(* into real^(N,N)finite_sum are trigonometric polynomials;                  *)
(* Stone-Weierstrass on the compact image (the map descends by the           *)
(* closed-graph lemma) gives uniform approximation; the integral of f^2      *)
(* vanishes, so f = 0.                                                       *)
(* ========================================================================= *)

let pde_trigpoly_RULES, pde_trigpoly_INDUCT, pde_trigpoly_CASES =
  new_inductive_definition
 `(!k. pde_zlat k ==> pde_trigpoly (\y:real^N. cos(&2 * pi * (k dot y)))) /\
  (!k. pde_zlat k ==> pde_trigpoly (\y:real^N. sin(&2 * pi * (k dot y)))) /\
  (!p q. pde_trigpoly p /\ pde_trigpoly q ==> pde_trigpoly (\y:real^N. p y + q y)) /\
  (!c p. pde_trigpoly p ==> pde_trigpoly (\y:real^N. c * p y))`;;

let pde_temb = new_definition
 `pde_temb (y:real^N) =
    (lambda i. if i <= dimindex(:N) then cos(&2 * pi * y$i)
               else sin(&2 * pi * y$(i - dimindex(:N)))):real^(N,N)finite_sum`;;

let PDE_FT_TRIGPOLY_EQ = prove
 (`!p q:real^N->real. pde_trigpoly p /\ (!y. p y = q y) ==> pde_trigpoly q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `q:real^N->real = p` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM]);;

let PDE_FT_TRIGPOLY_COMB = prove
 (`!k1 k2:real^N a b.
     pde_zlat k1 /\ pde_zlat k2
     ==> pde_trigpoly (\y. a * cos(&2 * pi * (k1 dot y)) +
                           b * cos(&2 * pi * (k2 dot y))) /\
         pde_trigpoly (\y. a * sin(&2 * pi * (k1 dot y)) +
                           b * sin(&2 * pi * (k2 dot y)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 pde_trigpoly_RULES))) THEN
  CONJ_TAC THEN MATCH_MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2 pde_trigpoly_RULES))) THEN
  ASM_SIMP_TAC[pde_trigpoly_RULES]);;

let PDE_FT_TRIGPOLY_CONST = prove
 (`!c. pde_trigpoly (\y:real^N. c)`,
  GEN_TAC THEN MATCH_MP_TAC PDE_FT_TRIGPOLY_EQ THEN
  EXISTS_TAC `\y:real^N. c * cos(&2 * pi * (vec 0 dot y))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2 pde_trigpoly_RULES))) THEN
    MATCH_MP_TAC(CONJUNCT1 pde_trigpoly_RULES) THEN
    REWRITE_TAC[PDE_FT_ZLAT_CLAUSES];
    REWRITE_TAC[DOT_LZERO; REAL_MUL_RZERO; COS_0; REAL_MUL_RID]]);;

let PDE_FT_TRIGPOLY_COORD = prove
 (`!i. 1 <= i /\ i <= dimindex(:N)
       ==> pde_trigpoly (\y:real^N. cos(&2 * pi * y$i)) /\
           pde_trigpoly (\y:real^N. sin(&2 * pi * y$i))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `basis i:real^N` (CONJUNCT1 pde_trigpoly_RULES)) THEN
  MP_TAC(SPEC `basis i:real^N` (CONJUNCT1(CONJUNCT2 pde_trigpoly_RULES))) THEN
  ASM_SIMP_TAC[PDE_FT_ZLAT_CLAUSES; DOT_BASIS]);;

let PDE_FT_TRIGPOLY_MODE_MUL = prove
 (`!k:real^N. pde_zlat k
     ==> !q. pde_trigpoly q
             ==> pde_trigpoly (\y. cos(&2 * pi * (k dot y)) * q y) /\
                 pde_trigpoly (\y. sin(&2 * pi * (k dot y)) * q y)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pde_trigpoly_INDUCT THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k':real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pde_zlat(k - k':real^N) /\ pde_zlat(k + k')` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[PDE_FT_ZLAT_CLAUSES]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC PDE_FT_TRIGPOLY_EQ THENL
     [EXISTS_TAC `\y:real^N. inv(&2) * cos(&2 * pi * ((k - k') dot y)) +
                             inv(&2) * cos(&2 * pi * ((k + k') dot y))`;
      EXISTS_TAC `\y:real^N. inv(&2) * sin(&2 * pi * ((k + k') dot y)) +
                             inv(&2) * sin(&2 * pi * ((k - k') dot y))`] THEN
    ASM_SIMP_TAC[PDE_FT_TRIGPOLY_COMB] THEN
    REWRITE_TAC[REAL_MUL_COS_COS; REAL_MUL_SIN_COS; GSYM PDE_FT_PHASE_SUB_ADD] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `k':real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pde_zlat(k - k':real^N) /\ pde_zlat(k + k')` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[PDE_FT_ZLAT_CLAUSES]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC PDE_FT_TRIGPOLY_EQ THENL
     [EXISTS_TAC `\y:real^N. inv(&2) * sin(&2 * pi * ((k + k') dot y)) +
                             --inv(&2) * sin(&2 * pi * ((k - k') dot y))`;
      EXISTS_TAC `\y:real^N. inv(&2) * cos(&2 * pi * ((k - k') dot y)) +
                             --inv(&2) * cos(&2 * pi * ((k + k') dot y))`] THEN
    ASM_SIMP_TAC[PDE_FT_TRIGPOLY_COMB] THEN
    REWRITE_TAC[REAL_MUL_COS_SIN; REAL_MUL_SIN_SIN; GSYM PDE_FT_PHASE_SUB_ADD] THEN
    REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`p:real^N->real`; `q:real^N->real`] THEN STRIP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC PDE_FT_TRIGPOLY_EQ THENL
     [EXISTS_TAC `\y:real^N. cos(&2 * pi * ((k:real^N) dot y)) * (p:real^N->real) y +
                             cos(&2 * pi * (k dot y)) * (q:real^N->real) y`;
      EXISTS_TAC `\y:real^N. sin(&2 * pi * ((k:real^N) dot y)) * (p:real^N->real) y +
                             sin(&2 * pi * (k dot y)) * (q:real^N->real) y`] THEN
    (CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC]) THEN
    MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 pde_trigpoly_RULES))) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`c:real`; `p:real^N->real`] THEN STRIP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC PDE_FT_TRIGPOLY_EQ THENL
     [EXISTS_TAC `\y:real^N. c * (cos(&2 * pi * ((k:real^N) dot y)) * (p:real^N->real) y)`;
      EXISTS_TAC `\y:real^N. c * (sin(&2 * pi * ((k:real^N) dot y)) * (p:real^N->real) y)`] THEN
    (CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC]) THEN
    MATCH_MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2 pde_trigpoly_RULES))) THEN
    ASM_REWRITE_TAC[]]);;

let PDE_FT_TRIGPOLY_MUL = prove
 (`!p q:real^N->real. pde_trigpoly p /\ pde_trigpoly q ==> pde_trigpoly (\y. p y * q y)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC pde_trigpoly_INDUCT THEN REWRITE_TAC[] THEN
  SIMP_TAC[PDE_FT_TRIGPOLY_MODE_MUL] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p1:real^N->real`; `p2:real^N->real`] THEN
    DISCH_TAC THEN X_GEN_TAC `q:real^N->real` THEN DISCH_TAC THEN
    MATCH_MP_TAC PDE_FT_TRIGPOLY_EQ THEN
    EXISTS_TAC `\y:real^N. (p1:real^N->real) y * (q:real^N->real) y + p2 y * q y` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 pde_trigpoly_RULES))) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`c:real`; `p1:real^N->real`] THEN
    DISCH_TAC THEN X_GEN_TAC `q:real^N->real` THEN DISCH_TAC THEN
    MATCH_MP_TAC PDE_FT_TRIGPOLY_EQ THEN
    EXISTS_TAC `\y:real^N. c * ((p1:real^N->real) y * (q:real^N->real) y)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2 pde_trigpoly_RULES))) THEN
    ASM_SIMP_TAC[]]);;

let PDE_FT_TRIGPOLY_CONT = prove
 (`!p:real^N->real. pde_trigpoly p ==> (\y. lift(p y)) continuous_on (:real^N)`,
  MATCH_MP_TAC pde_trigpoly_INDUCT THEN
  SIMP_TAC[PDE_FT_CONT_LIFT_COS_SIN; LIFT_ADD; LIFT_CMUL; CONTINUOUS_ON_ADD;
           CONTINUOUS_ON_CMUL]);;

let PDE_FT_TEMB_COMPONENT = prove
 (`!(y:real^N) i.
     1 <= i /\ i <= dimindex(:(N,N)finite_sum)
     ==> pde_temb y $ i = if i <= dimindex(:N) then cos(&2 * pi * y$i)
                          else sin(&2 * pi * y$(i - dimindex(:N)))`,
  SIMP_TAC[pde_temb; LAMBDA_BETA]);;

let PDE_FT_POLY_EMB = prove
 (`!g. real_polynomial_function g
       ==> pde_trigpoly (\y:real^N. g(pde_temb y))`,
  MATCH_MP_TAC real_polynomial_function_INDUCT THEN
  REWRITE_TAC[PDE_FT_TRIGPOLY_CONST] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[PDE_FT_TEMB_COMPONENT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_SUM]) THEN
    ASM_CASES_TAC `i <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(SPEC `i:num` (INST_TYPE [`:N`,`:N`] PDE_FT_TRIGPOLY_COORD)) THEN
      ASM_SIMP_TAC[];
      MP_TAC(SPEC `i - dimindex(:N)` (INST_TYPE [`:N`,`:N`] PDE_FT_TRIGPOLY_COORD)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 pde_trigpoly_RULES))) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_FT_TRIGPOLY_MUL THEN ASM_REWRITE_TAC[]]);;

let PDE_FT_TRIGPOLY_ORTH = prove
 (`!f:real^N->real^K.
     f continuous_on (:real^N) /\
     (!k. pde_zlat k ==> pde_fc f k = vec 0 /\ pde_fs f k = vec 0)
     ==> !p. pde_trigpoly p
             ==> integral (interval[vec 0,vec 1]) (\y. p y % f y) = vec 0`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!p. pde_trigpoly p
        ==> (\y. lift(p y)) continuous_on (:real^N) /\
            integral (interval[vec 0,vec 1]) (\y. p y % (f:real^N->real^K) y) = vec 0`
   (fun th -> SIMP_TAC[th]) THEN
  MATCH_MP_TAC pde_trigpoly_INDUCT THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM pde_fc; GSYM pde_fs; PDE_FT_CONT_LIFT_COS_SIN] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LIFT_ADD; LIFT_CMUL; CONTINUOUS_ON_ADD; CONTINUOUS_ON_CMUL] THEN
  REWRITE_TAC[VECTOR_ADD_RDISTRIB; GSYM VECTOR_MUL_ASSOC] THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_ADD o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PDE_FT_CONT_INTEGRABLE THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_RID]];
    W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_CMUL o lhand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC PDE_FT_CONT_INTEGRABLE THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO]]]);;

(* The embedding of the torus. *)

let PDE_FT_EMB_CONT = prove
 (`(pde_temb:real^N->real^(N,N)finite_sum) continuous_on (:real^N)`,
  ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[PDE_FT_TEMB_COMPONENT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_SUM]) THEN
  ASM_CASES_TAC `i <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `basis i:real^N` PDE_FT_CONT_LIFT_COS_SIN) THEN
    ASM_SIMP_TAC[DOT_BASIS];
    MP_TAC(ISPEC `basis(i - dimindex(:N)):real^N` PDE_FT_CONT_LIFT_COS_SIN) THEN
    SUBGOAL_THEN `1 <= i - dimindex(:N) /\ i - dimindex(:N) <= dimindex(:N)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[DOT_BASIS]]]);;

let PDE_FT_EMB_EQ = prove
 (`!y y':real^N. pde_temb y = pde_temb y' ==> pde_zlat(y - y')`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CART_EQ] THEN DISCH_TAC THEN
  REWRITE_TAC[pde_zlat; VECTOR_SUB_COMPONENT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i + dimindex(:N)`) THEN
  SIMP_TAC[PDE_FT_TEMB_COMPONENT; DIMINDEX_FINITE_SUM] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= (i:num) ==> ~(i + n <= n) /\ 1 <= i + n`;
               ARITH_RULE `(i:num) <= n ==> i + n <= n + n /\ i <= n + n`; ADD_SUB] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&2 * pi * (y':real^N)$i`; `&2 * pi * (y:real^N)$i`] SIN_COS_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_FIELD
   `&2 * pi * a = &2 * pi * b + &2 * n * pi ==> ~(pi = &0) ==> a - b = n`)) THEN
  ASM_SIMP_TAC[PI_NZ]);;

let PDE_FT_REDUCE = prove
 (`!y:real^N. ?y' a. y' IN interval[vec 0,vec 1] /\ pde_zlat a /\ y = y' + a`,
  GEN_TAC THEN
  EXISTS_TAC `(lambda i. frac((y:real^N)$i)):real^N` THEN
  EXISTS_TAC `(lambda i. floor((y:real^N)$i)):real^N` THEN
  SIMP_TAC[IN_INTERVAL; pde_zlat; CART_EQ; LAMBDA_BETA; VEC_COMPONENT;
           VECTOR_ADD_COMPONENT; FLOOR_FRAC; REAL_LT_IMP_LE] THEN
  MESON_TAC[FLOOR_FRAC; REAL_ADD_SYM]);;

let PDE_FT_PER_REDUCE = prove
 (`!f:real^N->real^K.
     pde_zper f ==> !y. ?y'. y' IN interval[vec 0,vec 1] /\ f y = f y'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `y:real^N` PDE_FT_REDUCE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y':real^N`; `a:real^N`] THEN STRIP_TAC THEN
  EXISTS_TAC `y':real^N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PDE_ZPER_INTEGER THEN ASM_MESON_TAC[pde_zlat]);;

(* Completeness. *)

let PDE_FT_SQ_INTEGRAL_ZERO = prove
 (`!f:real^N->real^1.
     f continuous_on (:real^N) /\
     integral (interval[vec 0,vec 1]) (\y. drop(f y) % f y) = vec 0
     ==> !y. y IN interval[vec 0,vec 1] ==> f y = vec 0`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^N. drop((f:real^N->real^1) y) % f y`;
                 `interval[vec 0:real^N,vec 1]`] HAS_INTEGRAL_NEGLIGIBLE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_1; VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM drop; REAL_LE_SQUARE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y:real^N. drop((f:real^N->real^1) y) % f y) has_integral vec 0)
    (interval[vec 0,vec 1])` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
    MATCH_MP_TAC PDE_FT_CONT_INTEGRABLE THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0; DROP_EQ_0] THEN DISCH_TAC THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `u = {y:real^N | (f:real^N->real^1) y IN ((:real^1) DIFF {vec 0})}` THEN
  SUBGOAL_THEN `open(u:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
    MP_TAC(ISPECL [`f:real^N->real^1`; `(:real^N)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((u:real^N->bool) INTER interval(vec 0,vec 1) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^N->bool`; `interval(vec 0:real^N,vec 1)`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `closure(interval(vec 0:real^N,vec 1)) = interval[vec 0,vec 1]`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
      REWRITE_TAC[INTERVAL_NE_EMPTY; VEC_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y0:real^N` THEN
    EXPAND_TAC "u" THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(u:real^N->bool) INTER interval(vec 0,vec 1)` OPEN_NOT_NEGLIGIBLE) THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERVAL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] NEGLIGIBLE_SUBSET)) THEN
  EXPAND_TAC "u" THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `vec 1:real^N`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
  REWRITE_TAC[SUBSET] THEN MESON_TAC[]);;

let PDE_FT_SMALL_LEMMA = prove
 (`!x m. &0 <= x /\ (!e. &0 < e ==> x <= e * m) /\ &0 < m ==> x = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x / (&2 * m)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < m ==> x / (&2 * m) * m = x / &2`] THEN
  ASM_REAL_ARITH_TAC);;

let PDE_FT_COMPLETE_1 = prove
 (`!f:real^N->real^1.
     f continuous_on (:real^N) /\ pde_zper f /\
     (!k. pde_zlat k ==> pde_fc f k = vec 0 /\ pde_fs f k = vec 0)
     ==> !y. f y = vec 0`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `kk = interval[vec 0:real^N,vec 1]` THEN
  ABBREV_TAC `ss = IMAGE (pde_temb:real^N->real^(N,N)finite_sum) kk` THEN
  SUBGOAL_THEN `compact(kk:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[COMPACT_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(ss:real^(N,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[PDE_FT_EMB_CONT; CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `ft = \z:real^(N,N)finite_sum. drop((f:real^N->real^1)
                     (@y. y IN kk /\ pde_temb y = z))` THEN
  SUBGOAL_THEN `!y:real^N. y IN kk ==> ft(pde_temb y) = drop((f:real^N->real^1) y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "ft" THEN
    REWRITE_TAC[DROP_EQ] THEN
    SUBGOAL_THEN `?y':real^N. y' IN kk /\ pde_temb y' = pde_temb y` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN
    ABBREV_TAC `y1 = @y':real^N. y' IN kk /\ pde_temb y' = pde_temb y` THEN
    STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP PDE_FT_EMB_EQ) THEN
    SUBGOAL_THEN `y1:real^N = y + (y1 - y)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC;
      MATCH_MP_TAC PDE_ZPER_INTEGER THEN ASM_MESON_TAC[pde_zlat]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(lift o ft) continuous_on (ss:real^(N,N)finite_sum->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_FROM_CLOSED_GRAPH THEN
    EXISTS_TAC `IMAGE (f:real^N->real^1) kk` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      EXPAND_TAC "ss" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
      ASM_SIMP_TAC[LIFT_DROP] THEN ASM SET_TAC[];
      SUBGOAL_THEN
       `{pastecart x ((lift o ft) x) | x IN ss} =
        IMAGE (\y. pastecart (pde_temb y) ((f:real^N->real^1) y)) kk`
      SUBST1_TAC THENL
       [EXPAND_TAC "ss" THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; o_THM] THEN
        ASM_MESON_TAC[LIFT_DROP];
        ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      ASM_MESON_TAC[PDE_FT_EMB_CONT; CONTINUOUS_ON_SUBSET; SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?p. pde_trigpoly p /\
                !y. y IN kk ==> abs(drop((f:real^N->real^1) y) - p y) < e`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ft:real^(N,N)finite_sum->real`; `ss:real^(N,N)finite_sum->bool`;
                   `e:real`] STONE_WEIERSTRASS_REAL_POLYNOMIAL_FUNCTION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^(N,N)finite_sum->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\y:real^N. g(pde_temb y):real` THEN
    ASM_SIMP_TAC[PDE_FT_POLY_EMB] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pde_temb(y:real^N)`) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?mm. &0 < mm /\ !y. y IN kk ==> norm((f:real^N->real^1) y) <= mm`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (f:real^N->real^1) kk` COMPACT_IMP_BOUNDED) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral kk (\y. drop((f:real^N->real^1) y) % f y) = vec 0` ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[NORM_EQ_0] `norm(x:real^1) = &0 ==> x = vec 0`) THEN
    MATCH_MP_TAC PDE_FT_SMALL_LEMMA THEN
    EXISTS_TAC `mm:real` THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N->real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `f:real^N->real^1` PDE_FT_TRIGPOLY_ORTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `p:real^N->real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `integral kk (\y. drop((f:real^N->real^1) y) % f y) =
      integral kk (\y. (drop(f y) - p y) % f y)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_RDISTRIB] THEN EXPAND_TAC "kk" THEN
      W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_SUB o rand o snd) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC PDE_FT_CONT_INTEGRABLE THEN
        MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        ASM_SIMP_TAC[o_DEF; LIFT_DROP; ETA_AX; PDE_FT_TRIGPOLY_CONT];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[VECTOR_SUB_RZERO]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\y:real^N. (drop((f:real^N->real^1) y) - p y) % f y`;
                   `vec 0:real^N`; `vec 1:real^N`;
                   `integral kk (\y:real^N. (drop((f:real^N->real^1) y) - p y) % f y)`;
                   `e * mm:real`] HAS_INTEGRAL_BOUND) THEN
    ASM_REWRITE_TAC[CONTENT_UNIT; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN EXPAND_TAC "kk" THEN
      MATCH_MP_TAC PDE_FT_CONT_INTEGRABLE THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP; ETA_AX] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      ASM_SIMP_TAC[PDE_FT_TRIGPOLY_CONT];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN kk ==> (f:real^N->real^1) y = vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN MATCH_MP_TAC PDE_FT_SQ_INTEGRAL_ZERO THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[PDE_FT_PER_REDUCE]);;

let PDE_FT_FC_COMPONENT = prove
 (`!(f:real^N->real^K) k i.
     f continuous_on (:real^N)
     ==> pde_fc (\y. lift(f y$i)) k = lift(pde_fc f k$i) /\
         pde_fs (\y. lift(f y$i)) k = lift(pde_fs f k$i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_fc; pde_fs] THEN
  ASM_SIMP_TAC[INTEGRAL_COMPONENT; PDE_FT_CONT_INTEGRABLE; PDE_FT_CONT_MODE_MUL] THEN
  REWRITE_TAC[LIFT_DROP; VECTOR_MUL_COMPONENT; LIFT_CMUL]);;

let PDE_FT_COMPLETE = prove
 (`!f:real^N->real^K.
     f continuous_on (:real^N) /\ pde_zper f /\
     (!k. pde_zlat k ==> pde_fc f k = vec 0 /\ pde_fs f k = vec 0)
     ==> !y. f y = vec 0`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[CART_EQ; VEC_COMPONENT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\y:real^N. lift((f:real^N->real^K) y$i)` PDE_FT_COMPLETE_1) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PDE_FT_FC_COMPONENT; VEC_COMPONENT; LIFT_NUM] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`f:real^N->real^K`; `(:real^N)`] CONTINUOUS_ON_COMPONENTWISE_LIFT) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[pde_zper] THEN RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ]]);;

(* ========================================================================= *)
(* The Fourier series of a smooth periodic map, summed over shells,          *)
(* converges to it with all its derivatives (as in ns_torus_inv.ml, in       *)
(* dimension N, with smooth maps).                                           *)
(* ========================================================================= *)

let PDE_FT_MTEST = prove
 (`!(g:num->real^M->real^N) b.
     (!m. g m continuous_on (:real^M)) /\ summable (from 0) (lift o b) /\
     (!m y. norm(g m y) <= b m)
     ==> (!y. ((\m. g m y) sums infsum (from 0) (\m. g m y)) (from 0)) /\
         (!e. &0 < e
              ==> ?N. !n y. N <= n
                            ==> norm(vsum(0..n) (\m. g m y) -
                                     infsum (from 0) (\m. g m y)) < e) /\
         (\y. infsum (from 0) (\m. g m y)) continuous_on (:real^M) /\
         (!a c. ((\m. integral (interval[a,c]) (g m)) sums
                 integral (interval[a,c]) (\y. infsum (from 0) (\m. g m y))) (from 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. ((\m. (g:num->real^M->real^N) m y) sums infsum (from 0) (\m. g m y)) (from 0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[SUMS_INFSUM] THEN MATCH_MP_TAC SUMMABLE_COMPARISON THEN
    EXISTS_TAC `b:num->real` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N. !n y. N <= n
                      ==> norm(vsum(0..n) (\m. (g:num->real^M->real^N) m y) -
                               infsum (from 0) (\m. g m y)) < e`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\(y:real^M) (m:num). (g:num->real^M->real^N) m y`; `b:num->real`;
                   `\y:real^M. T`; `from 0`] SERIES_COMPARISON_UNIFORM) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM summable] THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FROM_INTER_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_TAC `l:real^M->real^N`) THEN
    SUBGOAL_THEN `!y. (l:real^M->real^N) y = infsum (from 0) (\m. g m y)` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `\n. vsum(0..n) (\m. (g:num->real^M->real^N) m y)` THEN
      REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
       [REWRITE_TAC[LIM_SEQUENTIALLY] THEN ASM_MESON_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `y:real^M`) THEN
        REWRITE_TAC[sums; FROM_INTER_NUMSEG]];
      ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    ASM_REWRITE_TAC[dist] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n. (\y. vsum(0..n) (\m. (g:num->real^M->real^N) m y)) continuous_on (:real^M)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. infsum (from 0) (\m. (g:num->real^M->real^N) m y)) continuous_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` CONTINUOUS_UNIFORM_LIMIT) THEN
    EXISTS_TAC `\n y. vsum(0..n) (\m. (g:num->real^M->real^N) m y)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY; IN_UNIV] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `c:real^M`] THEN
  REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN
  SUBGOAL_THEN
   `!n. vsum(0..n) (\m. integral (interval[a,c]) ((g:num->real^M->real^N) m)) =
        integral (interval[a,c]) (\y. vsum(0..n) (\m. g m y))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`g:num->real^M->real^N`; `interval[a:real^M,c]`; `0..n`]
      INTEGRAL_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (content(interval[a:real^M,c]) + &1)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^M`; `c:real^M`] CONTENT_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[dist] THEN
  SUBGOAL_THEN
   `(\y. vsum(0..n) (\m. (g:num->real^M->real^N) m y)) integrable_on interval[a,c] /\
    (\y. infsum (from 0) (\m. (g:num->real^M->real^N) m y)) integrable_on interval[a,c]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_SUB] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `e / (content(interval[a:real^M,c]) + &1) * content(interval[a,c])` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_BOUND THEN
    EXISTS_TAC `\y. vsum(0..n) (\m. (g:num->real^M->real^N) m y) -
                    infsum (from 0) (\m. g m y)` THEN
    ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; INTEGRABLE_SUB] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN
      MP_TAC(ISPECL [`a:real^M`; `c:real^M`] CONTENT_POS_LE) THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[REAL_LT_IMP_LE]];
    MP_TAC(ISPECL [`a:real^M`; `c:real^M`] CONTENT_POS_LE) THEN
    ABBREV_TAC `ct = content(interval[a:real^M,c])` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 <= ct ==> e / (ct + &1) * ct = e * ct / (ct + &1)`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ e * x < e * &1 ==> e * x < e`) THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_LDIV_EQ;
                 REAL_ARITH `&0 <= ct ==> &0 < ct + &1`] THEN
    ASM_REAL_ARITH_TAC]);;

let PDE_FT_MODE_NORM = prove
 (`!(f:real^N->real^K) k y.
     norm(pde_mode f k y) <= norm(pde_fc f k) + norm(pde_fs f k)`,
  REWRITE_TAC[pde_mode; PDE_FT_VMODE_NORM]);;

let PDE_FT_FSH_ZPER = prove
 (`!(f:real^N->real^K) m. pde_zper (pde_fsh f m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_zper; pde_fsh] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN REWRITE_TAC[pde_mode] THEN
  SUBGOAL_THEN `pde_zlat(k:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDE_FT_SHELL_ZLAT]; ALL_TAC] THEN
  ASM_SIMP_TAC[PDE_FT_COS_SIN_PER; PDE_FT_ZLAT_CLAUSES]);;

let PDE_FT_DELTA_SERIES = prove
 (`!(c:real^K) m0. ((\m. if m = m0 then c else vec 0) sums c) (from 0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\m:num. if m = m0 then (c:real^K) else vec 0`; `{m0:num}`; `from 0`]
    SERIES_FINITE_SUPPORT) THEN
  SUBGOAL_THEN `{m0:num} INTER from 0 = {m0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_FROM; LE_0]; ALL_TAC] THEN
  REWRITE_TAC[FINITE_SING; IN_SING; VSUM_SING] THEN
  DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[]);;

let PDE_FT_FSH_SUM_COEFF = prove
 (`!(f:real^N->real^K) b k.
     f continuous_on (:real^N) /\ summable (from 0) (lift o b) /\
     (!m y. norm(pde_fsh f m y) <= b m) /\ pde_zlat k
     ==> pde_fc (\y. infsum (from 0) (\m. pde_fsh f m y)) k = pde_fc f k /\
         pde_fs (\y. infsum (from 0) (\m. pde_fsh f m y)) k = pde_fs f k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m0:num` o MATCH_MP PDE_FT_SHELL_EXISTS) THEN
  SUBGOAL_THEN
   `!m. pde_fc (pde_fsh (f:real^N->real^K) m) k =
        (if m = m0 then pde_fc f k else vec 0) /\
        pde_fs (pde_fsh f m) k = (if m = m0 then pde_fs f k else vec 0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[PDE_FT_FC_FSH] THEN
    ASM_MESON_TAC[PDE_FT_SHELL_UNIQUE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. summable (from 0) (\m. pde_fsh (f:real^N->real^K) m y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SUMMABLE_COMPARISON THEN
    EXISTS_TAC `b:num->real` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c:real^N->real.
       (\y. lift(c y)) continuous_on (:real^N) /\ (!y. abs(c y) <= &1)
       ==> ((\m. integral (interval[vec 0,vec 1])
                   (\y. c y % pde_fsh (f:real^N->real^K) m y)) sums
            integral (interval[vec 0,vec 1])
              (\y. c y % infsum (from 0) (\m. pde_fsh f m y))) (from 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:real^N->real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\m y. (c:real^N->real) y % pde_fsh (f:real^N->real^K) m y`;
                   `b:num->real`] PDE_FT_MTEST) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        ASM_REWRITE_TAC[o_DEF; ETA_AX; PDE_FT_CONT_FSH];
        REPEAT GEN_TAC THEN REWRITE_TAC[NORM_MUL] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`vec 0:real^N`; `vec 1:real^N`] o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[INFSUM_CMUL; ETA_AX];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THENL
   [MAP_EVERY EXISTS_TAC [`\m. pde_fc (pde_fsh (f:real^N->real^K) m) k`; `from 0`];
    MAP_EVERY EXISTS_TAC [`\m. pde_fs (pde_fsh (f:real^N->real^K) m) k`; `from 0`]] THEN
  (CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[PDE_FT_DELTA_SERIES]]) THEN
  REWRITE_TAC[pde_fc; pde_fs] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[PDE_FT_CONT_LIFT_COS_SIN; COS_BOUND; SIN_BOUND]);;

(* Shell sums are smooth; bounds for their iterated partials. *)

let PDE_FT_ITERATED_PARTIAL_VSUM = prove
 (`!l (g:A->real^N->real^K) s.
     FINITE s /\ (!a. a IN s ==> smooth_map_on (:real^N) (g a))
     ==> iterated_partial l (\x. vsum s (\a. g a x)) =
         (\x. vsum s (\a. iterated_partial l (g a) x))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; ETA_AX] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`g:A->real^N->real^K`; `s:A->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
  MP_TAC(ISPECL [`h:num`; `\a:A. iterated_partial t ((g:A->real^N->real^K) a)`;
                 `s:A->bool`; `x:real^N`] PARTIAL_DERIVATIVE_VSUM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `(:real^N)` THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL]);;

let PDE_FT_MODE_EQ = prove
 (`!(u:real^N->real^K) k.
     pde_mode u k = (\x. cos(&2 * pi * (k dot x)) % pde_fc u k +
                         sin(&2 * pi * (k dot x)) % pde_fs u k)`,
  REWRITE_TAC[FUN_EQ_THM; pde_mode]);;

let PDE_FT_FSH_SMOOTH = prove
 (`!(u:real^N->real^K) m.
     smooth_map_on (:real^N) (pde_fsh u m) /\
     !l. iterated_partial l (pde_fsh u m) =
         (\x. vsum (pde_shell m) (\k. iterated_partial l (pde_mode u k) x))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `pde_fsh (u:real^N->real^K) m =
                (\x. vsum (pde_shell m) (\k. pde_mode u k x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; pde_fsh]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:real^N. smooth_map_on (:real^N) (pde_mode (u:real^N->real^K) k)`
  ASSUME_TAC THENL [REWRITE_TAC[PDE_FT_MODE_EQ; PDE_FT_VMODE_SMOOTH]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[PDE_FT_SHELL_FINITE; OPEN_UNIV; ETA_AX];
    GEN_TAC THEN MATCH_MP_TAC PDE_FT_ITERATED_PARTIAL_VSUM THEN
    ASM_REWRITE_TAC[PDE_FT_SHELL_FINITE]]);;

let PDE_FT_MODE_ITERATED_BOUND = prove
 (`!l (u:real^N->real^K) k x.
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> norm(iterated_partial l (pde_mode u k) x) <=
         (&2 * pi * infnorm k) pow (LENGTH l) * (norm(pde_fc u k) + norm(pde_fs u k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_FT_MODE_EQ] THEN
  MP_TAC(SPECL [`l:num list`; `k:real^N`] PDE_FT_VMODE_ITERATED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`pde_fc (u:real^N->real^K) k`; `pde_fs (u:real^N->real^K) k`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `A':real^K` (X_CHOOSE_THEN `B':real^K` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(A':real^K) + norm(B':real^K)` THEN
  ASM_REWRITE_TAC[PDE_FT_VMODE_NORM]);;

let PDE_FT_ALL_REPLICATE = prove
 (`!n (x:A) P. P x ==> ALL P (REPLICATE n x)`,
  INDUCT_TAC THEN ASM_SIMP_TAC[REPLICATE; ALL]);;

let PDE_FT_COEFF_SHELL_BOUND = prove
 (`!(u:real^N->real^K) p A m k.
     smooth_map_on (:real^N) u /\ pde_zper u /\ 1 <= m /\ k IN pde_shell m /\
     (!l y. LENGTH l <= p /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
            ==> norm(iterated_partial l u y) <= A)
     ==> norm(pde_fc u k) + norm(pde_fs u k) <= (&2 * A) / (&2 * pi * &m) pow p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC o MATCH_MP PDE_FT_SHELL_COORD) THEN
  MP_TAC(ISPECL [`p:num`; `u:real^N->real^K`; `k:real^N`; `j:num`; `A:real`]
                PDE_FT_COEFF_DECAY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[PDE_FT_SHELL_ZLAT];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[LENGTH_REPLICATE; LE_REFL] THEN
      MATCH_MP_TAC PDE_FT_ALL_REPLICATE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < (&2 * pi * &m) pow p` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC);;

let PDE_FT_TWO_PI_GE_1 = prove
 (`&1 <= &2 * pi`,
  MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let PDE_FT_SHELL_ARITH = prove
 (`!m n A c. 1 <= m /\ &0 <= A /\ &0 <= c /\ c <= &((2 * m + 1) EXP n)
             ==> c * ((&2 * A) / (&2 * pi * &m) pow (n + 2)) <=
                 ((&2 * A) * &3 pow n) * inv(&m pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(2 * m + 1) <= &3 * &m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&m <= &2 * pi * &m` ASSUME_TAC THENL
   [MP_TAC PDE_FT_TWO_PI_GE_1 THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&m pow (n + 2) <= (&2 * pi * &m) pow (n + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &m pow (n + 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `c <= (&3 * &m) pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&((2 * m + 1) EXP n)` THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&3 * &m) pow n * ((&2 * A) * inv(&m pow (n + 2)))` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_ADD] THEN
  SUBGOAL_THEN `~(&m pow n = &0) /\ ~(&m = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_NZ; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let PDE_FT_FSH_ITERATED_BOUND = prove
 (`!(u:real^N->real^K) l.
     smooth_map_on (:real^N) u /\ pde_zper u /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> ?C. &0 <= C /\
             !m x. norm(iterated_partial l (pde_fsh u m) x) <=
                   (if m = 0 then C else C * inv(&m pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `LENGTH(l:num list) + dimindex(:N) + 2`]
                PDE_ZPER_JET_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `A:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= &3 pow dimindex(:N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `(&2 * A) * &3 pow dimindex(:N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `x:real^N`] THEN
  REWRITE_TAC[PDE_FT_FSH_SMOOTH] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `pde_shell 0 = {vec 0:real^N}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_SING; PDE_FT_SHELL_0]; ALL_TAC] THEN
    REWRITE_TAC[VSUM_SING] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * pi * infnorm(vec 0:real^N)) pow (LENGTH(l:num list)) *
                (norm(pde_fc (u:real^N->real^K) (vec 0)) + norm(pde_fs u (vec 0)))` THEN
    ASM_SIMP_TAC[PDE_FT_MODE_ITERATED_BOUND] THEN
    REWRITE_TAC[INFNORM_0; REAL_MUL_RZERO; REAL_POW_ZERO] THEN
    MP_TAC(ISPECL [`0`; `u:real^N->real^K`; `vec 0:real^N`; `1`; `A:real`]
                  PDE_FT_COEFF_DECAY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PDE_FT_ZLAT_CLAUSES; LE_REFL; DIMINDEX_GE_1] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[REPLICATE; LENGTH; ALL; LE_0];
      ALL_TAC] THEN
    REWRITE_TAC[real_pow; REAL_MUL_RID] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * A` THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = &2 * pi * &m` THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(pde_shell m:real^N->bool)) *
              (q pow (LENGTH(l:num list)) *
               ((&2 * A) / q pow (LENGTH l + dimindex(:N) + 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_BOUND THEN REWRITE_TAC[PDE_FT_SHELL_FINITE] THEN
    X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * pi * infnorm(k:real^N)) pow (LENGTH(l:num list)) *
                (norm(pde_fc (u:real^N->real^K) k) + norm(pde_fs u k))` THEN
    ASM_SIMP_TAC[PDE_FT_MODE_ITERATED_BOUND] THEN
    SUBGOAL_THEN `infnorm(k:real^N) = &m` SUBST1_TAC THENL
     [UNDISCH_TAC `(k:real^N) IN pde_shell m` THEN SIMP_TAC[pde_shell; IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "q" THEN MATCH_MP_TAC PDE_FT_COEFF_SHELL_BOUND THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `q pow (LENGTH(l:num list)) * ((&2 * A) / q pow (LENGTH l + dimindex(:N) + 2)) =
    (&2 * A) / q pow (dimindex(:N) + 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD] THEN
    SUBGOAL_THEN `~(q pow LENGTH(l:num list) = &0) /\ ~(q pow dimindex(:N) = &0) /\
                  ~(q = &0)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_NZ; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  EXPAND_TAC "q" THEN MATCH_MP_TAC PDE_FT_SHELL_ARITH THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE; PDE_FT_SHELL_CARD] THEN ASM_REAL_ARITH_TAC);;

let PDE_FT_ZETA2_SUMMABLE = prove
 (`!C. summable (from 0) (\n. lift(C * inv(&n pow 2)))`,
  GEN_TAC THEN
  MP_TAC(SPECL [`0`; `2`] REAL_SUMMABLE_ZETA_INTEGER) THEN
  REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `C:real` o MATCH_MP REAL_SUMMABLE_LMUL) THEN
  REWRITE_TAC[REAL_SUMMABLE; o_DEF]);;

let PDE_FT_ZETA2_SUMMABLE_0 = prove
 (`!C. summable (from 0) (lift o (\m. if m = 0 then C else C * inv(&m pow 2)))`,
  GEN_TAC THEN REWRITE_TAC[ISPECL [`1`; `0`] SUMMABLE_FROM_ELSEWHERE_EQ] THEN
  MATCH_MP_TAC SUMMABLE_EQ THEN
  EXISTS_TAC `\n. lift(C * inv(&n pow 2))` THEN
  REWRITE_TAC[IN_FROM; o_THM] THEN CONJ_TAC THENL
   [SIMP_TAC[ARITH_RULE `1 <= n ==> ~(n = 0)`];
    REWRITE_TAC[ISPECL [`0`; `1`] SUMMABLE_FROM_ELSEWHERE_EQ] THEN
    REWRITE_TAC[PDE_FT_ZETA2_SUMMABLE]]);;

let PDE_FT_FC_SUB = prove
 (`!(f:real^N->real^K) g k.
     f continuous_on (:real^N) /\ g continuous_on (:real^N)
     ==> pde_fc (\y. f y - g y) k = pde_fc f k - pde_fc g k /\
         pde_fs (\y. f y - g y) k = pde_fs f k - pde_fs g k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_fc; pde_fs; VECTOR_SUB_LDISTRIB] THEN
  ASM_SIMP_TAC[INTEGRAL_SUB; PDE_FT_CONT_INTEGRABLE; PDE_FT_CONT_MODE_MUL]);;

(* The Fourier series of a smooth periodic map converges to it, with all     *)
(* derivatives.                                                              *)

let PDE_FT_FOURIER_SERIES = prove
 (`!u:real^N->real^K.
     smooth_map_on (:real^N) u /\ pde_zper u
     ==> !l x. ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
               ==> ((\m. iterated_partial l (pde_fsh u m) x) sums
                    iterated_partial l u x) (from 0)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `pde_fsh (u:real^N->real^K)`] SMOOTH_MAP_ON_SERIES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_UNIV; PDE_FT_FSH_SMOOTH; IN_UNIV] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`u:real^N->real^K`; `l:num list`] PDE_FT_FSH_ITERATED_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\n. C * inv(&n pow 2)` THEN EXISTS_TAC `1` THEN
    REWRITE_TAC[PDE_FT_ZETA2_SUMMABLE] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:real^N`]) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> ~(n = 0)`; PDE_FT_FSH_SMOOTH];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SER")) THEN
  SUBGOAL_THEN
   `(\x. infsum (from 0) (\n. pde_fsh (u:real^N->real^K) n x)) = u`
  (LABEL_TAC "EQ") THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    USE_THEN "SER" (MP_TAC o SPEC `x:real^N` o C MATCH_MP
      (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:N)) (l:num list)`)) THEN
    USE_THEN "EQ" (fun th -> REWRITE_TAC[th])] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  SPEC_TAC(`y:real^N`,`y:real^N`) THEN MATCH_MP_TAC PDE_FT_COMPLETE THEN
  SUBGOAL_THEN `(u:real^N->real^K) continuous_on (:real^N) /\
                (\x. infsum (from 0) (\n. pde_fsh (u:real^N->real^K) n x))
                continuous_on (:real^N)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[pde_zper] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!n. pde_fsh (u:real^N->real^K) n (x + basis i) = pde_fsh u n x`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`u:real^N->real^K`; `n:num`] PDE_FT_FSH_ZPER) THEN
      REWRITE_TAC[pde_zper] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`u:real^N->real^K`; `[]:num list`] PDE_FT_FSH_ITERATED_BOUND) THEN
    ASM_REWRITE_TAC[ALL; iterated_partial] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`u:real^N->real^K`;
                   `\m. if m = 0 then C else C * inv(&m pow 2)`; `k:real^N`]
                  PDE_FT_FSH_SUM_COEFF) THEN
    ASM_REWRITE_TAC[PDE_FT_ZETA2_SUMMABLE_0] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PDE_FT_FC_SUB; VECTOR_SUB_REFL]]);;

(* ========================================================================= *)
(* Space-time terms                                                          *)
(*   z = (t,y) |-> cos(2 pi k.y) A(t) + sin(2 pi k.y) B(t)                    *)
(* (time first): partials, and the closed form of all iterated partials when *)
(* A, B run through families of successive time derivatives.                 *)
(* ========================================================================= *)

let PDE_HEAT_DIFF_SPACE_FN = prove
 (`!(c:real^N->real^P) (z:real^(1,N)finite_sum).
     c differentiable (at (sndcart z)) ==> (\z. c(sndcart z)) differentiable (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (c:real^N->real^P)(sndcart z)) = c o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; LINEAR_SNDCART]);;

let PDE_HEAT_DIFF_TIME_FN = prove
 (`!(a:real^1->real^P) (z:real^(1,N)finite_sum).
     a differentiable (at (fstcart z)) ==> (\z. a(fstcart z)) differentiable (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (a:real^1->real^P)(fstcart z)) = a o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; LINEAR_FSTCART]);;

let PDE_HEAT_PD_SPACE_FN = prove
 (`!(c:real^N->real^P) (z:real^(1,N)finite_sum).
     c differentiable (at (sndcart z))
     ==> partial_derivative 1 (\z. c(sndcart z)) z = vec 0 /\
         !j. 1 <= j /\ j <= dimindex(:N)
             ==> partial_derivative (1 + j) (\z. c(sndcart z)) z =
                 partial_derivative j c (sndcart z)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[TEXT_PARTIAL_DERIVATIVE_SNDCART_COMPOSE] THEN
  ASM_SIMP_TAC[PDE_ST_BASIS_TIME; PDE_ST_BASIS_SPACE; SNDCART_PASTECART;
               partial_derivative] THEN
  MP_TAC(ISPEC `frechet_derivative (c:real^N->real^P) (at (sndcart(z:real^(1,N)finite_sum)))`
                LINEAR_0) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; REWRITE_TAC[]]);;

let PDE_HEAT_PD_TIME_FN = prove
 (`!(P:real->real^K) P' (z:real^(1,N)finite_sum).
     ((\w. P(drop w)) has_vector_derivative P') (at (fstcart z))
     ==> partial_derivative 1 (\z. P(drop(fstcart z))) z = P' /\
         !j. 1 <= j /\ j <= dimindex(:N)
             ==> partial_derivative (1 + j) (\z. P(drop(fstcart z))) z = vec 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\w. (P:real->real^K)(drop w)) differentiable
                (at (fstcart(z:real^(1,N)finite_sum)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[differentiable; has_vector_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN `(\h. drop h % (P':real^K)) =
                frechet_derivative (\w. (P:real->real^K)(drop w))
                                   (at (fstcart(z:real^(1,N)finite_sum)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[GSYM has_vector_derivative];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. (P:real->real^K)(drop w)`; `z:real^(1,N)finite_sum`]
                TEXT_PARTIAL_DERIVATIVE_FSTCART_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
  ASM_SIMP_TAC[PDE_ST_BASIS_TIME; PDE_ST_BASIS_SPACE; FSTCART_PASTECART] THEN
  REWRITE_TAC[LIFT_DROP; DROP_VEC; VECTOR_MUL_LID; VECTOR_MUL_LZERO]);;

let PDE_HEAT_COS_SIN_DIFF = prove
 (`!(k:real^N) y. (\y. lift(cos(&2 * pi * (k dot y)))) differentiable (at y) /\
                  (\y. lift(sin(&2 * pi * (k dot y)))) differentiable (at y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[differentiable] THEN
  MESON_TAC[PDE_FT_HAS_DERIVATIVE_LIFT_COS; PDE_FT_HAS_DERIVATIVE_LIFT_SIN]);;

let PDE_HEAT_PROD_PARTIAL = prove
 (`!(c:real^N->real) (P:real->real^K) P' (z:real^(1,N)finite_sum) i.
     (\y. lift(c y)) differentiable (at (sndcart z)) /\
     ((\w. P(drop w)) has_vector_derivative P') (at (fstcart z)) /\
     1 <= i /\ i <= dimindex(:N) + 1
     ==> partial_derivative i (\z. c(sndcart z) % P(drop(fstcart z))) z =
         (if i = 1 then c(sndcart z) % P'
          else drop(partial_derivative (i - 1) (\y. lift(c y)) (sndcart z)) %
               P(drop(fstcart z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\w. (P:real->real^K)(drop w)) differentiable
                (at (fstcart(z:real^(1,N)finite_sum)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[differentiable; has_vector_derivative]; ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`; `\z:real^(1,N)finite_sum. lift((c:real^N->real)(sndcart z))`;
                 `\z:real^(1,N)finite_sum. (P:real->real^K)(drop(fstcart z))`;
                 `z:real^(1,N)finite_sum`] PARTIAL_DERIVATIVE_MUL) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(BETA_RULE(ISPEC `\y:real^N. lift((c:real^N->real) y)`
                                   PDE_HEAT_DIFF_SPACE_FN));
      MATCH_MP_TAC(BETA_RULE(ISPEC `\w:real^1. (P:real->real^K)(drop w)`
                                   PDE_HEAT_DIFF_TIME_FN))] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`\y:real^N. lift((c:real^N->real) y)`; `z:real^(1,N)finite_sum`]
                PDE_HEAT_PD_SPACE_FN) THEN
  MP_TAC(ISPECL [`P:real->real^K`; `P':real^K`; `z:real^(1,N)finite_sum`]
                PDE_HEAT_PD_TIME_FN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `i = 1 + (i - 1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= i - 1 /\ i - 1 <= dimindex(:N)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ADD_SUB2; VECTOR_MUL_RZERO; VECTOR_ADD_LID]);;

let PDE_HEAT_PROD_DIFF = prove
 (`!(c:real^N->real) (P:real->real^K) (z:real^(1,N)finite_sum).
     (\y. lift(c y)) differentiable (at (sndcart z)) /\
     (\w. P(drop w)) differentiable (at (fstcart z))
     ==> (\z. c(sndcart z) % P(drop(fstcart z))) differentiable (at z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (c:real^N->real)(sndcart z)`;
                 `\z:real^(1,N)finite_sum. (P:real->real^K)(drop(fstcart z))`;
                 `z:real^(1,N)finite_sum`] DIFFERENTIABLE_MUL_AT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC(BETA_RULE(ISPEC `\y:real^N. lift((c:real^N->real) y)`
                                 PDE_HEAT_DIFF_SPACE_FN));
    MATCH_MP_TAC(BETA_RULE(ISPEC `\w:real^1. (P:real->real^K)(drop w)`
                                 PDE_HEAT_DIFF_TIME_FN))] THEN
  ASM_REWRITE_TAC[]);;

let PDE_HEAT_TERM_PARTIAL = prove
 (`!(k:real^N) (P:real->real^K) Q P' Q' (z:real^(1,N)finite_sum) i.
     ((\w. P(drop w)) has_vector_derivative P') (at (fstcart z)) /\
     ((\w. Q(drop w)) has_vector_derivative Q') (at (fstcart z)) /\
     1 <= i /\ i <= dimindex(:N) + 1
     ==> partial_derivative i
           (\z. cos(&2 * pi * (k dot sndcart z)) % P(drop(fstcart z)) +
                sin(&2 * pi * (k dot sndcart z)) % Q(drop(fstcart z))) z =
         (if i = 1
          then cos(&2 * pi * (k dot sndcart z)) % P' +
               sin(&2 * pi * (k dot sndcart z)) % Q'
          else cos(&2 * pi * (k dot sndcart z)) % ((&2 * pi * k$(i - 1)) % Q(drop(fstcart z))) +
               sin(&2 * pi * (k dot sndcart z)) %
                 (--(&2 * pi * k$(i - 1)) % P(drop(fstcart z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\w. (P:real->real^K)(drop w)) differentiable
                (at (fstcart(z:real^(1,N)finite_sum))) /\
                (\w. (Q:real->real^K)(drop w)) differentiable
                (at (fstcart(z:real^(1,N)finite_sum)))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[differentiable; has_vector_derivative]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`i:num`;
    `\z:real^(1,N)finite_sum. cos(&2 * pi * ((k:real^N) dot sndcart z)) %
                              (P:real->real^K)(drop(fstcart z))`;
    `\z:real^(1,N)finite_sum. sin(&2 * pi * ((k:real^N) dot sndcart z)) %
                              (Q:real->real^K)(drop(fstcart z))`;
    `z:real^(1,N)finite_sum`] PARTIAL_DERIVATIVE_ADD) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(BETA_RULE(ISPECL [`\y:real^N. cos(&2 * pi * ((k:real^N) dot y))`]
                                    PDE_HEAT_PROD_DIFF));
      MATCH_MP_TAC(BETA_RULE(ISPECL [`\y:real^N. sin(&2 * pi * ((k:real^N) dot y))`]
                                    PDE_HEAT_PROD_DIFF))] THEN
    ASM_REWRITE_TAC[PDE_HEAT_COS_SIN_DIFF];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`\y:real^N. cos(&2 * pi * ((k:real^N) dot y))`;
                           `P:real->real^K`; `P':real^K`; `z:real^(1,N)finite_sum`;
                           `i:num`] PDE_HEAT_PROD_PARTIAL)) THEN
  MP_TAC(BETA_RULE(ISPECL [`\y:real^N. sin(&2 * pi * ((k:real^N) dot y))`;
                           `Q:real->real^K`; `Q':real^K`; `z:real^(1,N)finite_sum`;
                           `i:num`] PDE_HEAT_PROD_PARTIAL)) THEN
  ASM_REWRITE_TAC[PDE_HEAT_COS_SIN_DIFF] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= i - 1 /\ i - 1 <= dimindex(:N)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[PDE_FT_PD_LIFT_COS_SIN; LIFT_DROP] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LNEG; VECTOR_MUL_LNEG] THEN
  REWRITE_TAC[REAL_MUL_SYM] THEN VECTOR_ARITH_TAC);;

let PDE_HEAT_TERM_ITERATED = prove
 (`!(k:real^N) (A:num->real->real^K) B a b.
     (!j t. a < t /\ t < b
            ==> ((\w. A j (drop w)) has_vector_derivative A (SUC j) t) (at (lift t)) /\
                ((\w. B j (drop w)) has_vector_derivative B (SUC j) t) (at (lift t)))
     ==> !l. ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) l
             ==> ?i c1 c2 sw.
                   i <= LENGTH l /\
                   abs c1 <= (&1 + &2 * pi * infnorm k) pow (LENGTH l) /\
                   abs c2 <= (&1 + &2 * pi * infnorm k) pow (LENGTH l) /\
                   !z. z IN interval(lift a,lift b) PCROSS (:real^N)
                       ==> iterated_partial l
                             (\z. cos(&2 * pi * (k dot sndcart z)) % A 0 (drop(fstcart z)) +
                                  sin(&2 * pi * (k dot sndcart z)) % B 0 (drop(fstcart z))) z =
                           cos(&2 * pi * (k dot sndcart z)) %
                             (c1 % (if sw then B else A) i (drop(fstcart z))) +
                           sin(&2 * pi * (k dot sndcart z)) %
                             (c2 % (if sw then A else B) i (drop(fstcart z)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `q = &1 + &2 * pi * infnorm(k:real^N)` THEN
  SUBGOAL_THEN `&1 <= q /\ &2 * pi * infnorm(k:real^N) <= q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    SUBGOAL_THEN `&0 <= &2 * pi * infnorm(k:real^N)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PI_POS_LE; INFNORM_POS_LE];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 <= q pow n /\ q pow n <= q pow (SUC n)` ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_pow] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(interval(lift a,lift b) PCROSS (:real^N))` ASSUME_TAC THENL
   [SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN interval(lift a,lift b) PCROSS (:real^N)
        ==> a < drop(fstcart z) /\ drop(fstcart z) < b /\
            lift(drop(fstcart z)) = fstcart z`
  (LABEL_TAC "ZP") THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART] THEN SIMP_TAC[];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; LENGTH; iterated_partial] THENL
   [MAP_EVERY EXISTS_TAC [`0`; `&1`; `&1`; `F`] THEN
    REWRITE_TAC[LE_REFL; real_pow; REAL_ABS_NUM; REAL_LE_REFL; VECTOR_MUL_LID];
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `c2:real`
    (X_CHOOSE_THEN `sw:bool` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F")))))))) THEN
  ABBREV_TAC `X = if sw then (B:num->real->real^K) else A` THEN
  ABBREV_TAC `Y = if sw then (A:num->real->real^K) else B` THEN
  SUBGOAL_THEN
   `!j t. a < t /\ t < b
          ==> ((\w. (X:num->real->real^K) j (drop w)) has_vector_derivative X (SUC j) t)
                (at (lift t)) /\
              ((\w. (Y:num->real->real^K) j (drop w)) has_vector_derivative Y (SUC j) t)
                (at (lift t))`
  (LABEL_TAC "XY") THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN interval(lift a,lift b) PCROSS (:real^N)
        ==> partial_derivative h
              (iterated_partial t
                (\z:real^(1,N)finite_sum. cos(&2 * pi * ((k:real^N) dot sndcart z)) %
                                         (A:num->real->real^K) 0 (drop(fstcart z)) +
                     sin(&2 * pi * (k dot sndcart z)) % B 0 (drop(fstcart z)))) z =
            (if h = 1
             then cos(&2 * pi * (k dot sndcart z)) % (c1 % X (SUC i) (drop(fstcart z))) +
                  sin(&2 * pi * (k dot sndcart z)) % (c2 % Y (SUC i) (drop(fstcart z)))
             else cos(&2 * pi * (k dot sndcart z)) %
                    ((&2 * pi * k$(h - 1)) % (c2 % (Y:num->real->real^K) i (drop(fstcart z)))) +
                  sin(&2 * pi * (k dot sndcart z)) %
                    (--(&2 * pi * k$(h - 1)) % (c1 % X i (drop(fstcart z)))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w0:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `partial_derivative h
        (\z:real^(1,N)finite_sum. cos(&2 * pi * ((k:real^N) dot sndcart z)) %
               (\s. c1 % (X:num->real->real^K) i s) (drop(fstcart z)) +
             sin(&2 * pi * (k dot sndcart z)) %
               (\s. c2 % (Y:num->real->real^K) i s) (drop(fstcart z))) w0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS (:real^N)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "F" (fun th -> ASM_SIMP_TAC[th]) THEN
      MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "ZP" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME
      `(w0:real^(1,N)finite_sum) IN interval(lift a,lift b) PCROSS (:real^N)`))) THEN
    MP_TAC(ISPECL [`k:real^N`; `\s. c1 % (X:num->real->real^K) i s`;
                   `\s. c2 % (Y:num->real->real^K) i s`;
                   `c1 % (X:num->real->real^K) (SUC i) (drop(fstcart(w0:real^(1,N)finite_sum)))`;
                   `c2 % (Y:num->real->real^K) (SUC i) (drop(fstcart(w0:real^(1,N)finite_sum)))`;
                   `w0:real^(1,N)finite_sum`; `h:num`] PDE_HEAT_TERM_PARTIAL) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
      USE_THEN "XY" (MP_TAC o REWRITE_RULE[LIFT_DROP] o
        C MATCH_MP (CONJ (ASSUME `a < drop(fstcart(w0:real^(1,N)finite_sum))`)
                         (ASSUME `drop(fstcart(w0:real^(1,N)finite_sum)) < b`)) o
        SPECL [`i:num`; `drop(fstcart(w0:real^(1,N)finite_sum))`]) THEN
      SIMP_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `h = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [`SUC i`; `c1:real`; `c2:real`; `sw:bool`] THEN
    ASM_REWRITE_TAC[LE_SUC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_LE_TRANS];
      ASM_MESON_TAC[REAL_LE_TRANS];
      X_GEN_TAC `w0:real^(1,N)finite_sum` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `(&2 * pi * (k:real^N)$(h - 1)) * c2`;
                        `--(&2 * pi * (k:real^N)$(h - 1)) * c1`; `~sw`] THEN
  SUBGOAL_THEN `abs(&2 * pi * (k:real^N)$(h - 1)) <= q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * pi * infnorm(k:real^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_FT_INFNORM_COMPONENT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN REWRITE_TAC[real_pow] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN REWRITE_TAC[REAL_ABS_NEG; real_pow] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    X_GEN_TAC `w0:real^(1,N)finite_sum` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN REWRITE_TAC[COND_SWAP] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_ASSOC]]);;

(* ========================================================================= *)
(* The extension of the forcing.  Its space-time partials are Z^N-periodic   *)
(* in space at times in [0,tmax), and bounded uniformly on                   *)
(* [0,T] x R^N for T < tmax.                                                 *)
(* ========================================================================= *)

let PDE_HEAT_ITERATED_TRANSLATE_SLAB = prove
 (`!l (g:real^(1,N)finite_sum->real^K) a b (c:real^N) z.
     smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) g /\
     z IN interval(lift a,lift b) PCROSS (:real^N)
     ==> iterated_partial l (\z. g(z + pastecart (vec 0) c)) z =
         iterated_partial l g (z + pastecart (vec 0) c)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!w:real^(1,N)finite_sum.
      w IN interval(lift a,lift b) PCROSS (:real^N) ==>
      w + pastecart (vec 0) (c:real^N) IN interval(lift a,lift b) PCROSS (:real^N)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_ADD; PASTECART_IN_PCROSS; IN_UNIV;
                VECTOR_ADD_RID];
    ALL_TAC] THEN
  SPEC_TAC(`z:real^(1,N)finite_sum`,`z:real^(1,N)finite_sum`) THEN
  SPEC_TAC(`l:num list`,`l:num list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h
                (\z. iterated_partial t (g:real^(1,N)finite_sum->real^K)
                                      (z + pastecart (vec 0) (c:real^N))) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
    MATCH_MP_TAC PDE_PARTIAL_TRANSLATE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL]]);;

let PDE_HEAT_EXT_ZPER = prove
 (`!(FE:real^(1,N)finite_sum->real^K) (f:real->real^N->real^K) e tmax.
     &0 < e /\ &0 < tmax /\
     smooth_map_on (interval(lift(&0 - e),lift tmax) PCROSS (:real^N)) FE /\
     (!t y. &0 <= t /\ t < tmax ==> FE(pastecart (lift t) y) = f t y) /\
     (!t. pde_zper (f t))
     ==> !l s y i. &0 <= s /\ s < tmax /\ 1 <= i /\ i <= dimindex(:N)
                   ==> iterated_partial l FE (pastecart (lift s) (y + basis i)) =
                       iterated_partial l FE (pastecart (lift s) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `C = pastecart (vec 0) (basis i:real^N):real^(1,N)finite_sum` THEN
  SUBGOAL_THEN `!s' y'. pastecart (lift s') (y' + basis i:real^N) =
                        pastecart (lift s') y' + C:real^(1,N)finite_sum`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_RID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN interval(lift(&0),lift tmax) PCROSS (:real^N)
        ==> iterated_partial l (FE:real^(1,N)finite_sum->real^K) (z + C) =
            iterated_partial l FE z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_map_on (interval(lift(&0),lift tmax) PCROSS (:real^N))
                    (FE:real^(1,N)finite_sum->real^K)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - e),lift tmax) PCROSS (:real^N)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:num list`; `FE:real^(1,N)finite_sum->real^K`; `&0`; `tmax:real`;
                   `basis i:real^N`; `z:real^(1,N)finite_sum`]
                  PDE_HEAT_ITERATED_TRANSLATE_SLAB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `interval(lift(&0),lift tmax) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^N`] THEN STRIP_TAC THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_RID] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (is_forall o concl)) THEN
    REWRITE_TAC[pde_zper] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < s` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. iterated_partial l (FE:real^(1,N)finite_sum->real^K) (z + C)`;
                 `iterated_partial l (FE:real^(1,N)finite_sum->real^K)`;
                 `&0`; `tmax:real`; `y:real^N`] PDE_ST_RIGHT_EQ) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!w. w IN interval(lift(&0 - e),lift tmax) PCROSS (:real^N)
        ==> iterated_partial l (FE:real^(1,N)finite_sum->real^K) continuous (at w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift(&0 - e),lift tmax) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z. iterated_partial l (FE:real^(1,N)finite_sum->real^K) (z + C)) =
      iterated_partial l FE o (\z. z + C)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ADD; CONTINUOUS_AT_ID; CONTINUOUS_CONST] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_RID; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                LIFT_DROP; IN_UNIV] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    ASM_REAL_ARITH_TAC]);;

let PDE_HEAT_SLAB_JET_BOUNDED = prove
 (`!(G:real^(1,N)finite_sum->real^K) e tmax T1 p.
     &0 < e /\ &0 <= T1 /\ T1 < tmax /\
     smooth_map_on (interval(lift(&0 - e),lift tmax) PCROSS (:real^N)) G /\
     (!l s y i. &0 <= s /\ s < tmax /\ 1 <= i /\ i <= dimindex(:N)
                ==> iterated_partial l G (pastecart (lift s) (y + basis i)) =
                    iterated_partial l G (pastecart (lift s) y))
     ==> ?A. &0 <= A /\
             !l s y. LENGTH l <= p /\
                     ALL (\h. 1 <= h /\ h <= dimindex(:(1,N)finite_sum)) l /\
                     &0 <= s /\ s <= T1
                     ==> norm(iterated_partial l G (pastecart (lift s) y)) <= A`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PER"))))) THEN
  SUBGOAL_THEN
   `?B. !l s y. &0 <= s /\ s <= T1
                ==> norm(iterated_partial l (G:real^(1,N)finite_sum->real^K)
                                          (pastecart (lift s) y)) <= B l`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `l:num list` THEN
    MP_TAC(ISPECL [`iterated_partial l (G:real^(1,N)finite_sum->real^K)`;
                   `interval[lift(&0),lift T1] PCROSS interval[vec 0:real^N,vec 1]`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - e),lift tmax) PCROSS (:real^N)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
        MATCH_MP_TAC PCROSS_MONO THEN
        REWRITE_TAC[SUBSET_UNIV; SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FORALL_LIFT;
                IN_INTERVAL_1; LIFT_DROP] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BD"))) THEN
    EXISTS_TAC `B:real` THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `\x:real^N. iterated_partial l (G:real^(1,N)finite_sum->real^K)
                                (pastecart (lift s) x)` PDE_FT_PER_REDUCE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[pde_zper] THEN REPEAT STRIP_TAC THEN
      USE_THEN "PER" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^N` (STRIP_ASSUME_TAC o BETA_RULE) o
               SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "BD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `sum (pde_index_lists p (:(1,N)finite_sum))
                  (\l. abs((B:num list->real) l))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((B:num list->real) l)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_ARITH `x <= b ==> x <= abs b`]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {l:num list} (\l. abs((B:num list->real) l))` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_SING; REAL_LE_REFL];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE; REAL_ABS_POS; SING_SUBSET] THEN
    ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM]]);;

(* Coefficients of the time derivatives of the forcing. *)

let pde_hcf = new_definition
 `pde_hcf (FE:real^(1,N)finite_sum->real^K) (k:real^N) j (s:real) =
    pde_fc (\y. iterated_partial (REPLICATE j 1) FE (pastecart (lift s) y)) k`;;

let pde_hsf = new_definition
 `pde_hsf (FE:real^(1,N)finite_sum->real^K) (k:real^N) j (s:real) =
    pde_fs (\y. iterated_partial (REPLICATE j 1) FE (pastecart (lift s) y)) k`;;

let PDE_HEAT_VDERIV1 = prove
 (`!(f:real^1->real^K) x.
     f differentiable (at x)
     ==> (f has_vector_derivative partial_derivative 1 f x) (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative; partial_derivative] THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP LINEAR_FRECHET_DERIVATIVE th) THEN
                        ASSUME_TAC(REWRITE_RULE[FRECHET_DERIVATIVE_WORKS] th)) THEN
  SUBGOAL_THEN
   `(\h. drop h % frechet_derivative (f:real^1->real^K) (at x) (basis 1)) =
    frechet_derivative f (at x)`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
  SUBGOAL_THEN `lift(drop h) = drop h % basis 1:real^1` SUBST1_TAC THENL
   [REWRITE_TAC[PDE_BASIS1_REAL1; GSYM LIFT_CMUL; REAL_MUL_RID]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL]);;

let PDE_HEAT_TIME_SLICE_PARTIAL = prove
 (`!(g:real^(1,N)finite_sum->real^K) w (y:real^N).
     g differentiable (at (pastecart w y))
     ==> partial_derivative 1 (\w. g(pastecart w y)) w =
         partial_derivative 1 g (pastecart w y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\w. (g:real^(1,N)finite_sum->real^K)(pastecart w y)) =
                g o (\w. pastecart w y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `((\w:real^1. pastecart w (y:real^N)) has_derivative
                 (\h. pastecart h (vec 0))) (at w)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `\w:real^1. pastecart w (y:real^N)`;
                 `g:real^(1,N)finite_sum->real^K`; `w:real^1`]
                PARTIAL_DERIVATIVE_CHAIN) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[differentiable]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[partial_derivative] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[PDE_ST_BASIS_TIME; PDE_BASIS1_REAL1]);;

let PDE_HEAT_SMOOTH_SPACE_FN = prove
 (`!(c:real^N->real^P) (S:real^(1,N)finite_sum->bool).
     open S /\ smooth_map_on (:real^N) c ==> smooth_map_on S (\z. c(sndcart z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (c:real^N->real^P)(sndcart z)) = c o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
  ASM_REWRITE_TAC[LINEAR_SNDCART]);;

let PDE_HEAT_COEF_DERIV = prove
 (`!(H:real^(1,N)finite_sum->real^K) (c:real^N->real) a b s.
     smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) H /\
     smooth_map_on (:real^N) (\y. lift(c y)) /\ a < s /\ s < b
     ==> ((\w. integral (interval[vec 0,vec 1]) (\y. c y % H(pastecart w y)))
          has_vector_derivative
          integral (interval[vec 0,vec 1])
            (\y. c y % partial_derivative 1 H (pastecart (lift s) y))) (at (lift s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(interval(lift a,lift b) PCROSS (:real^N))` ASSUME_TAC THENL
   [SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (interval(lift a,lift b) PCROSS (:real^N))
                  (\z:real^(1,N)finite_sum. drop(lift((c:real^N->real)(sndcart z))) %
                                            (H:real^(1,N)finite_sum->real^K) z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(BETA_RULE(ISPEC `\y:real^N. lift((c:real^N->real) y)`
                                 PDE_HEAT_SMOOTH_SPACE_FN)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift a,lift b)`; `interval(lift a,lift b) PCROSS (:real^N)`;
                 `vec 0:real^N`; `vec 1:real^N`;
                 `\z:real^(1,N)finite_sum. drop(lift((c:real^N->real)(sndcart z))) %
                                           (H:real^(1,N)finite_sum->real^K) z`]
                NS_PARAM_INTEGRAL_SMOOTH) THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL; LIFT_DROP; SNDCART_PASTECART] THEN
  ANTS_TAC THENL
   [SIMP_TAC[PASTECART_IN_PCROSS; IN_UNIV]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL [`lift s`; `1`])) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `integral (interval[vec 0,vec 1])
      (\y. (c:real^N->real) y %
           partial_derivative 1 (H:real^(1,N)finite_sum->real^K) (pastecart (lift s) y)) =
    partial_derivative 1
      (\w. integral (interval[vec 0,vec 1]) (\y. c y % H(pastecart w y))) (lift s)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `pastecart (lift s) (y:real^N) IN interval(lift a,lift b) PCROSS (:real^N)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (c:real^N->real)(sndcart z) %
                                             (H:real^(1,N)finite_sum->real^K) z`;
                   `lift s`; `y:real^N`] PDE_HEAT_TIME_SLICE_PARTIAL) THEN
    REWRITE_TAC[SNDCART_PASTECART] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `interval(lift a,lift b) PCROSS (:real^N)` THEN
      ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[LIFT_DROP]) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`1`; `\z:real^(1,N)finite_sum. lift((c:real^N->real)(sndcart z))`;
                   `H:real^(1,N)finite_sum->real^K`; `pastecart (lift s) (y:real^N)`]
                  PARTIAL_DERIVATIVE_MUL) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS (:real^N)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(BETA_RULE(ISPEC `\y:real^N. lift((c:real^N->real) y)`
                                   PDE_HEAT_SMOOTH_SPACE_FN)) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`\y:real^N. lift((c:real^N->real) y)`; `pastecart (lift s) (y:real^N)`]
                  PDE_HEAT_PD_SPACE_FN) THEN
    REWRITE_TAC[SNDCART_PASTECART] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_HEAT_VDERIV1 THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `interval(lift a,lift b)` THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP]);;

let PDE_HEAT_HCF_DERIV = prove
 (`!(FE:real^(1,N)finite_sum->real^K) a b (k:real^N) j s.
     smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) FE /\ a < s /\ s < b
     ==> ((\w. pde_hcf FE k j (drop w)) has_vector_derivative pde_hcf FE k (SUC j) s)
           (at (lift s)) /\
         ((\w. pde_hsf FE k j (drop w)) has_vector_derivative pde_hsf FE k (SUC j) s)
           (at (lift s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_hcf; pde_hsf; pde_fc; pde_fs; LIFT_DROP] THEN
  REWRITE_TAC[REPLICATE; iterated_partial] THENL
   [MP_TAC(ISPECL [`iterated_partial (REPLICATE j 1) (FE:real^(1,N)finite_sum->real^K)`;
                   `\y:real^N. cos(&2 * pi * ((k:real^N) dot y))`;
                   `a:real`; `b:real`; `s:real`] PDE_HEAT_COEF_DERIV);
    MP_TAC(ISPECL [`iterated_partial (REPLICATE j 1) (FE:real^(1,N)finite_sum->real^K)`;
                   `\y:real^N. sin(&2 * pi * ((k:real^N) dot y))`;
                   `a:real`; `b:real`; `s:real`] PDE_HEAT_COEF_DERIV)] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV;
               PDE_FT_SMOOTH_LIFT_COS_SIN]);;

let PDE_HEAT_SLICE_SMOOTH = prove
 (`!(G:real^(1,N)finite_sum->real^K) a b s.
     smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) G /\ a < s /\ s < b
     ==> smooth_map_on (:real^N) (\y. G(pastecart (lift s) y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^N. (G:real^(1,N)finite_sum->real^K)(pastecart (lift s) y)) =
                G o (\y. pastecart (lift s) y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (:real^N)` THEN
  ASM_SIMP_TAC[OPEN_UNIV; OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

let PDE_HEAT_HCF_BOUND = prove
 (`!(FE:real^(1,N)finite_sum->real^K) (f:real->real^N->real^K) e tmax T1 j p.
     &0 < e /\ &0 < tmax /\ &0 <= T1 /\ T1 < tmax /\
     smooth_map_on (interval(lift(&0 - e),lift tmax) PCROSS (:real^N)) FE /\
     (!t y. &0 <= t /\ t < tmax ==> FE(pastecart (lift t) y) = f t y) /\
     (!t. pde_zper (f t))
     ==> ?A. &0 <= A /\
             !s (k:real^N) m.
               &0 <= s /\ s <= T1 /\ k IN pde_shell m
               ==> norm(pde_hcf FE k j s) + norm(pde_hsf FE k j s) <=
                   (if m = 0 then &2 * A else (&2 * A) / (&2 * pi * &m) pow p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`FE:real^(1,N)finite_sum->real^K`; `f:real->real^N->real^K`;
                 `e:real`; `tmax:real`] PDE_HEAT_EXT_ZPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "PER") THEN
  MP_TAC(ISPECL [`FE:real^(1,N)finite_sum->real^K`; `e:real`; `tmax:real`; `T1:real`;
                 `p + j:num`] PDE_HEAT_SLAB_JET_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A"))) THEN
  EXISTS_TAC `A:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `k:real^N`; `m:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `u = \y:real^N. iterated_partial (REPLICATE j 1)
                               (FE:real^(1,N)finite_sum->real^K) (pastecart (lift s) y)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (u:real^N->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    MATCH_MP_TAC(ISPECL [`iterated_partial (REPLICATE j 1) (FE:real^(1,N)finite_sum->real^K)`;
                         `&0 - e`; `tmax:real`; `s:real`] PDE_HEAT_SLICE_SMOOTH) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_zper (u:real^N->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[pde_zper] THEN REPEAT STRIP_TAC THEN
    USE_THEN "PER" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l y. LENGTH l <= p /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
          ==> norm(iterated_partial l (u:real^N->real^K) y) <= A`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "u" THEN
    MP_TAC(ISPECL [`l:num list`;
                   `iterated_partial (REPLICATE j 1) (FE:real^(1,N)finite_sum->real^K)`;
                   `interval(lift(&0 - e),lift tmax) PCROSS (:real^N)`;
                   `lift s`; `y:real^N`] PDE_ST_SLICE_ITERATED) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV;
                   PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM ITERATED_PARTIAL_APPEND] THEN
    USE_THEN "A" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE; ALL_APPEND; ALL_MAP;
                o_DEF] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:N)) l` THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN SIMP_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC PDE_FT_ALL_REPLICATE THEN REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_hcf (FE:real^(1,N)finite_sum->real^K) k j s = pde_fc u k /\
                pde_hsf FE k j s = pde_fs u k` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pde_hcf; pde_hsf] THEN EXPAND_TAC "u" THEN REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `(k:real^N) IN pde_shell 0` THEN REWRITE_TAC[PDE_FT_SHELL_0] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`0`; `u:real^N->real^K`; `vec 0:real^N`; `1`; `A:real`]
                  PDE_FT_COEFF_DECAY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PDE_FT_ZLAT_CLAUSES; LE_REFL; DIMINDEX_GE_1] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[REPLICATE; LENGTH; ALL; LE_0];
      REWRITE_TAC[real_pow; REAL_MUL_RID] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC PDE_FT_COEFF_SHELL_BOUND THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* The time coefficient families of the heat solution.  For a mode with      *)
(* eigenvalue lam, initial coefficient a and forcing coefficients ph j (the  *)
(* j-th time derivative), pde_hduh gives the Duhamel solution of             *)
(* c' = -lam c + ph 0 and its successive derivatives.                        *)
(* ========================================================================= *)

let pde_hduh = define
 `(!lam (a:real^K) (ph:num->real->real^K) t.
      pde_hduh lam a ph 0 t =
        exp(--(lam * t)) %
        (a + integral (interval[lift(&0),lift t]) (\w. exp(lam * drop w) % ph 0 (drop w)))) /\
  (!lam a ph j t.
      pde_hduh lam a ph (SUC j) t = --lam % pde_hduh lam a ph j t + ph j t)`;;

let PDE_HEAT_VDERIV_MUL = prove
 (`!(f:real->real) f' (g:real^1->real^K) g' t.
     (f has_real_derivative f') (atreal t) /\ (g has_vector_derivative g') (at (lift t))
     ==> ((\w. f(drop w) % g w) has_vector_derivative (f t % g' + f' % g(lift t)))
         (at (lift t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(f:real->real) o drop`; `\h:real^1. drop h * f'`; `g:real^1->real^K`;
                 `\h:real^1. drop h % (g':real^K)`; `lift t`] HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(lift o (\h:real^1. drop h * f')) = (\h. drop h % lift f')`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ASM_REWRITE_TAC[o_ASSOC]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN
  GEN_TAC THEN REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let PDE_HEAT_FTC = prove
 (`!(h:real^1->real^K) c t.
     &0 < t /\ t < c /\ h continuous_on interval[lift(&0),lift c]
     ==> ((\w. integral (interval[lift(&0),w]) h) has_vector_derivative h(lift t))
         (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^1->real^K`; `lift(&0)`; `lift c`] INTEGRAL_HAS_VECTOR_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `lift t`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `interval(lift(&0),lift c)` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET)) THEN
  REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_OPEN THEN
  REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC);;

let PDE_HEAT_EXP_CONT = prove
 (`!c (w:real^1). (lift o (\w. exp(c * drop w))) continuous (at w)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
  EXISTS_TAC `lift((c * &1) * exp(c * drop w))` THEN
  MP_TAC(INST [`drop w`,`t:real`]
   (REAL_DIFF_CONV `((\t. exp(c * t)) has_real_derivative f') (atreal t)`)) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; LIFT_DROP; o_DEF]);;

let PDE_HDUH_DERIV = prove
 (`!lam (a:real^K) (ph:num->real->real^K) a0 b.
     a0 < &0 /\
     (!j s. a0 < s /\ s < b
            ==> ((\w. ph j (drop w)) has_vector_derivative ph (SUC j) s) (at (lift s)))
     ==> !j t. &0 < t /\ t < b
               ==> ((\w. pde_hduh lam a ph j (drop w)) has_vector_derivative
                    pde_hduh lam a ph (SUC j) t) (at (lift t))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PH")) THEN
  INDUCT_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[CONJUNCT2 pde_hduh] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      USE_THEN "PH" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ABBREV_TAC `h = \w:real^1. exp(lam * drop w) % (ph:num->real->real^K) 0 (drop w)` THEN
  SUBGOAL_THEN `!w:real^1. a0 < drop w /\ drop w < b ==> (h:real^1->real^K) continuous (at w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
    REWRITE_TAC[PDE_HEAT_EXP_CONT] THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `(ph:num->real->real^K) (SUC 0) (drop w)` THEN
    USE_THEN "PH" (MP_TAC o REWRITE_RULE[LIFT_DROP] o
      C MATCH_MP (CONJ (ASSUME `a0 < drop(w:real^1)`) (ASSUME `drop(w:real^1) < b`)) o
      SPECL [`0`; `drop(w:real^1)`]) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_hduh lam (a:real^K) ph (SUC 0) t =
    exp(--(lam * t)) % (h:real^1->real^K)(lift t) +
    (exp(--(lam * t)) * --lam) %
    (a + integral (interval[lift(&0),lift t]) h)`
  SUBST1_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[pde_hduh; LIFT_DROP; VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_ARITH `--(lam * t) + lam * t = &0`; REAL_EXP_0] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. pde_hduh lam (a:real^K) ph 0 (drop w)) =
    (\w. exp(--(lam * drop w)) % (a + integral (interval[lift(&0),w]) h))`
  SUBST1_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[FUN_EQ_THM; pde_hduh; LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\t:real. exp(--(lam * t))`; `exp(--(lam * t)) * --lam`;
    `\w:real^1. (a:real^K) + integral (interval[lift(&0),w]) h`;
    `(h:real^1->real^K)(lift t)`; `t:real`] PDE_HEAT_VDERIV_MUL)) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_LID] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC PDE_HEAT_FTC THEN EXISTS_TAC `(t + b) / &2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC]);;

let PDE_HDUH_CONT = prove
 (`!lam (a:real^K) (ph:num->real->real^K) a0 b c.
     a0 < &0 /\ &0 < c /\ c < b /\
     (!j s. a0 < s /\ s < b
            ==> ((\w. ph j (drop w)) has_vector_derivative ph (SUC j) s) (at (lift s)))
     ==> !j. (\w. pde_hduh lam a ph j (drop w)) continuous_on interval[lift(&0),lift c]`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PH")))) THEN
  SUBGOAL_THEN
   `!j. (\w. (ph:num->real->real^K) j (drop w)) continuous_on interval[lift(&0),lift c]`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `(ph:num->real->real^K) (SUC j) s` THEN
    USE_THEN "PH" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[pde_hduh; LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ARITH `--(lam * x) = --lam * x`] THEN
      REWRITE_TAC[PDE_HEAT_EXP_CONT];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[PDE_HEAT_EXP_CONT];
    REWRITE_TAC[pde_hduh] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CMUL]]);;

let PDE_HDUH_BOUND = prove
 (`!lam (a:real^K) (ph:num->real->real^K) T1 D.
     &0 <= lam /\ &0 <= T1 /\ norm a <= D /\
     (\w. ph 0 (drop w)) continuous_on interval[lift(&0),lift T1]
     ==> !j. (!i s. i <= j /\ &0 <= s /\ s <= T1 ==> norm(ph i s) <= D)
             ==> !t. &0 <= t /\ t <= T1
                     ==> norm(pde_hduh lam a ph j t) <=
                         (&1 + lam) pow j * (&j + &1) * ((&1 + T1) * D)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[LE] THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[pde_hduh; real_pow; REAL_MUL_LID; REAL_ADD_LID] THEN
    ABBREV_TAC `h = \w:real^1. exp(lam * drop w) % (ph:num->real->real^K) 0 (drop w)` THEN
    SUBGOAL_THEN
     `norm(integral (interval[lift(&0),lift t]) (h:real^1->real^K)) <= (exp(lam * t) * D) * t`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`h:real^1->real^K`; `lift(&0)`; `lift t`;
                     `integral (interval[lift(&0),lift t]) (h:real^1->real^K)`;
                     `exp(lam * t) * D`] HAS_INTEGRAL_BOUND) THEN
      SIMP_TAC[CONTENT_1; LIFT_DROP; ASSUME `&0 <= t`; REAL_SUB_RZERO] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
        REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
        MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN EXPAND_TAC "h" THEN
        MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REWRITE_TAC[PDE_HEAT_EXP_CONT];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `interval[lift(&0),lift T1]` THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "h" THEN
        REWRITE_TAC[LIFT_DROP; NORM_MUL; REAL_ABS_EXP] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN
        REWRITE_TAC[REAL_EXP_POS_LE; NORM_POS_LE; REAL_EXP_MONO_LE] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL] THEN
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_EXP] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(lam * t)) * norm(a:real^K) +
                exp(--(lam * t)) * ((exp(lam * t) * D) * t)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(i:real^K) <= b ==> norm(a + i) <= norm a + b`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL2; REAL_MUL_LID] THEN
    SUBGOAL_THEN `exp(--(lam * t)) <= &1` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      REWRITE_TAC[REAL_NEG_LE0] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(--(lam * t)) * norm(a:real^K) <= D` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * norm(a:real^K)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
        ASM_REWRITE_TAC[REAL_MUL_LID]];
      ALL_TAC] THEN
    SUBGOAL_THEN `D * t <= D * T1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    DISCH_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[pde_hduh] THEN
  ABBREV_TAC `C = &1 + lam` THEN
  ABBREV_TAC `Q = (&1 + T1) * D` THEN
  SUBGOAL_THEN `&1 <= C /\ lam <= C /\ D <= Q /\ &0 <= Q` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C"; "Q"] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= C pow j /\ &1 <= C pow (SUC j)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lam * norm(pde_hduh lam (a:real^K) ph j t) + norm(ph j t:real^K)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `norm(x:real^K) = l ==> norm(x + y) <= l + norm y`) THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_NEG] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[REAL_ABS_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((ph:num->real->real^K) j t) <= D` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lam * norm(pde_hduh lam (a:real^K) ph j t) <= C * (C pow j * (&j + &1) * Q)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `D <= C pow (SUC j) * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * Q` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_LID];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `C pow (SUC j) * (&(SUC j) + &1) * Q =
    C * (C pow j * (&j + &1) * Q) + C pow (SUC j) * Q`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The heat solution.  Modes of the solution: eigenvalue 4 pi^2 |k|^2,       *)
(* cosine and sine time families pde_hA, pde_hB (Duhamel with the            *)
(* coefficients of u0 and of the forcing extension FE), terms, shell sums    *)
(* and the series pde_hsol.                                                  *)
(* ========================================================================= *)

let pde_heig = new_definition
 `pde_heig (k:real^N) = &4 * pi pow 2 * (k dot k)`;;

let pde_hA = new_definition
 `pde_hA (FE:real^(1,N)finite_sum->real^K) (u0:real^N->real^K) (k:real^N) =
    pde_hduh (pde_heig k) (pde_fc u0 k) (pde_hcf FE k)`;;

let pde_hB = new_definition
 `pde_hB (FE:real^(1,N)finite_sum->real^K) (u0:real^N->real^K) (k:real^N) =
    pde_hduh (pde_heig k) (pde_fs u0 k) (pde_hsf FE k)`;;

let pde_hterm = new_definition
 `pde_hterm (FE:real^(1,N)finite_sum->real^K) (u0:real^N->real^K) (k:real^N) =
    \z. cos(&2 * pi * (k dot sndcart z)) % pde_hA FE u0 k 0 (drop(fstcart z)) +
        sin(&2 * pi * (k dot sndcart z)) % pde_hB FE u0 k 0 (drop(fstcart z))`;;

let pde_hsh = new_definition
 `pde_hsh (FE:real^(1,N)finite_sum->real^K) (u0:real^N->real^K) m =
    \z. vsum (pde_shell m) (\k. pde_hterm FE u0 k z)`;;

let pde_hsol = new_definition
 `pde_hsol (FE:real^(1,N)finite_sum->real^K) (u0:real^N->real^K) (t:real) (y:real^N) =
    infsum (from 0) (\m. pde_hsh FE u0 m (pastecart (lift t) y))`;;

(* The standing hypotheses. *)

let pde_hdata = new_definition
 `pde_hdata tmax e (FE:real^(1,N)finite_sum->real^K) (f:real->real^N->real^K)
            (u0:real^N->real^K) <=>
    &0 < tmax /\ &0 < e /\
    smooth_map_on (interval(lift(&0 - e),lift tmax) PCROSS (:real^N)) FE /\
    (!t y. &0 <= t /\ t < tmax ==> FE(pastecart (lift t) y) = f t y) /\
    (!t. pde_zper (f t)) /\ smooth_map_on (:real^N) u0 /\ pde_zper u0`;;

let PDE_HEAT_HEIG_POS = prove
 (`!k:real^N. &0 <= pde_heig k`,
  GEN_TAC THEN REWRITE_TAC[pde_heig] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE; DOT_POS_LE]);;

let PDE_HEAT_FAM_DERIV = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0.
     pde_hdata tmax e FE f u0
     ==> !k j t. &0 < t /\ t < tmax
                 ==> ((\w. pde_hA FE u0 k j (drop w)) has_vector_derivative
                      pde_hA FE u0 k (SUC j) t) (at (lift t)) /\
                     ((\w. pde_hB FE u0 k j (drop w)) has_vector_derivative
                      pde_hB FE u0 k (SUC j) t) (at (lift t))`,
  REWRITE_TAC[pde_hdata; pde_hA; pde_hB] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `k:real^N` THEN
  SUBGOAL_THEN
   `!j s. &0 - e < s /\ s < tmax
          ==> ((\w. pde_hcf (FE:real^(1,N)finite_sum->real^K) (k:real^N) j (drop w))
               has_vector_derivative pde_hcf FE k (SUC j) s) (at (lift s)) /\
              ((\w. pde_hsf FE k j (drop w)) has_vector_derivative pde_hsf FE k (SUC j) s)
                (at (lift s))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PDE_HEAT_HCF_DERIV THEN
    MAP_EVERY EXISTS_TAC [`&0 - e`; `tmax:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`pde_heig(k:real^N)`; `pde_fc (u0:real^N->real^K) k`;
                 `pde_hcf (FE:real^(1,N)finite_sum->real^K) k`; `&0 - e`; `tmax:real`]
                PDE_HDUH_DERIV) THEN
  MP_TAC(ISPECL [`pde_heig(k:real^N)`; `pde_fs (u0:real^N->real^K) k`;
                 `pde_hsf (FE:real^(1,N)finite_sum->real^K) k`; `&0 - e`; `tmax:real`]
                PDE_HDUH_DERIV) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> &0 - e < &0`]);;

let PDE_HEAT_FAM_CONT = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 c.
     pde_hdata tmax e FE f u0 /\ &0 < c /\ c < tmax
     ==> !k j. (\w. pde_hA FE u0 k j (drop w)) continuous_on interval[lift(&0),lift c] /\
               (\w. pde_hB FE u0 k j (drop w)) continuous_on interval[lift(&0),lift c]`,
  REWRITE_TAC[pde_hdata; pde_hA; pde_hB] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `k:real^N` THEN
  SUBGOAL_THEN
   `!j s. &0 - e < s /\ s < tmax
          ==> ((\w. pde_hcf (FE:real^(1,N)finite_sum->real^K) (k:real^N) j (drop w))
               has_vector_derivative pde_hcf FE k (SUC j) s) (at (lift s)) /\
              ((\w. pde_hsf FE k j (drop w)) has_vector_derivative pde_hsf FE k (SUC j) s)
                (at (lift s))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PDE_HEAT_HCF_DERIV THEN
    MAP_EVERY EXISTS_TAC [`&0 - e`; `tmax:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`pde_heig(k:real^N)`; `pde_fc (u0:real^N->real^K) k`;
                 `pde_hcf (FE:real^(1,N)finite_sum->real^K) k`; `&0 - e`; `tmax:real`;
                 `c:real`] PDE_HDUH_CONT) THEN
  MP_TAC(ISPECL [`pde_heig(k:real^N)`; `pde_fs (u0:real^N->real^K) k`;
                 `pde_hsf (FE:real^(1,N)finite_sum->real^K) k`; `&0 - e`; `tmax:real`;
                 `c:real`] PDE_HDUH_CONT) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> &0 - e < &0`]);;

(* Bounds for the time families, uniform on [0,T1] with decay in the shell. *)

let PDE_HEAT_U0_COEFF_BOUND = prove
 (`!(u0:real^N->real^K) p.
     smooth_map_on (:real^N) u0 /\ pde_zper u0
     ==> ?A. &0 <= A /\
             !k m. k IN pde_shell m
                   ==> norm(pde_fc u0 k) + norm(pde_fs u0 k) <=
                       (if m = 0 then &2 * A else (&2 * A) / (&2 * pi * &m) pow p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u0:real^N->real^K`; `p:num`] PDE_ZPER_JET_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `A:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N`; `m:num`] THEN DISCH_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `(k:real^N) IN pde_shell 0` THEN REWRITE_TAC[PDE_FT_SHELL_0] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`0`; `u0:real^N->real^K`; `vec 0:real^N`; `1`; `A:real`]
                  PDE_FT_COEFF_DECAY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PDE_FT_ZLAT_CLAUSES; LE_REFL; DIMINDEX_GE_1] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[REPLICATE; LENGTH; ALL; LE_0];
      REWRITE_TAC[real_pow; REAL_MUL_RID] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC PDE_FT_COEFF_SHELL_BOUND THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let PDE_HEAT_FAM_BOUND = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 T1 L p.
     pde_hdata tmax e FE f u0 /\ &0 <= T1 /\ T1 < tmax
     ==> ?C. &0 <= C /\
             !k m i t. k IN pde_shell m /\ i <= L /\ &0 <= t /\ t <= T1
                       ==> norm(pde_hA FE u0 k i t) + norm(pde_hB FE u0 k i t) <=
                           (&1 + pde_heig k) pow L * C *
                           (if m = 0 then &1 else inv((&2 * pi * &m) pow p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_hdata]) THEN
  MP_TAC(ISPECL [`u0:real^N->real^K`; `p:num`] PDE_HEAT_U0_COEFF_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Au:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "U0"))) THEN
  SUBGOAL_THEN
   `?Aj. !j. &0 <= Aj j /\
             !s (k:real^N) m.
               &0 <= s /\ s <= T1 /\ k IN pde_shell m
               ==> norm(pde_hcf (FE:real^(1,N)finite_sum->real^K) k j s) +
                   norm(pde_hsf FE k j s) <=
                   (if m = 0 then &2 * Aj j else (&2 * Aj j) / (&2 * pi * &m) pow p)`
  (X_CHOOSE_THEN `Aj:num->real` (LABEL_TAC "AJ")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
    MATCH_MP_TAC PDE_HEAT_HCF_BOUND THEN
    MAP_EVERY EXISTS_TAC [`f:real->real^N->real^K`; `e:real`; `tmax:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `As = Au + sum(0..L) (\j. (Aj:num->real) j)` THEN
  SUBGOAL_THEN `&0 <= As /\ Au <= As /\ !j. j <= L ==> (Aj:num->real) j <= As`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "As" THEN
    SUBGOAL_THEN `&0 <= sum(0..L) (\j. (Aj:num->real) j)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      USE_THEN "AJ" (fun th -> SIMP_TAC[th]);
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(Aj:num->real) j <= sum(0..L) (\j. Aj j)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum {j:num} (\j. (Aj:num->real) j)` THEN
      CONJ_TAC THENL [REWRITE_TAC[SUM_SING; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; LE_0] THEN
      USE_THEN "AJ" (fun th -> SIMP_TAC[th]);
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `&2 * (&L + &1) * (&1 + T1) * (&2 * As)` THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N`; `m:num`; `i:num`; `t:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `fm = if m = 0 then &1 else inv((&2 * pi * &m) pow p)` THEN
  SUBGOAL_THEN `&0 <= fm` ASSUME_TAC THENL
   [EXPAND_TAC "fm" THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PI_POS_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!B. (if m = 0 then &2 * B else (&2 * B) / (&2 * pi * &m) pow p) = (&2 * B) * fm`
  (LABEL_TAC "FM") THENL
   [GEN_TAC THEN EXPAND_TAC "fm" THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_MUL_RID; real_div];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 * Au) * fm <= (&2 * As) * fm /\
    (!j. j <= L ==> (&2 * (Aj:num->real) j) * fm <= (&2 * As) * fm)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; REPEAT STRIP_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POS];
    ALL_TAC] THEN
  ABBREV_TAC `D = (&2 * As) * fm` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(pde_fc (u0:real^N->real^K) k) <= D /\ norm(pde_fs u0 k) <= D`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "U0" (MP_TAC o C MATCH_MP (ASSUME `(k:real^N) IN pde_shell m`) o
                   SPECL [`k:real^N`; `m:num`]) THEN
    USE_THEN "FM" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPEC `pde_fc (u0:real^N->real^K) k` NORM_POS_LE) THEN
    MP_TAC(ISPEC `pde_fs (u0:real^N->real^K) k` NORM_POS_LE) THEN
    UNDISCH_TAC `(&2 * Au) * fm <= D` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i' s. i' <= L /\ &0 <= s /\ s <= T1
           ==> norm(pde_hcf (FE:real^(1,N)finite_sum->real^K) k i' s) <= D /\
               norm(pde_hsf FE k i' s) <= D`
  (LABEL_TAC "PHB") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "AJ" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `&0 <= s`) (CONJ (ASSUME `s <= T1`)
            (ASSUME `(k:real^N) IN pde_shell m`))) o
      SPECL [`s:real`; `k:real^N`; `m:num`] o CONJUNCT2 o SPEC `i':num`) THEN
    USE_THEN "FM" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(&2 * (Aj:num->real) i') * fm <= D` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `D:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `pde_hcf (FE:real^(1,N)finite_sum->real^K) k i' s` NORM_POS_LE) THEN
    MP_TAC(ISPEC `pde_hsf (FE:real^(1,N)finite_sum->real^K) k i' s` NORM_POS_LE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. pde_hcf (FE:real^(1,N)finite_sum->real^K) k 0 (drop w)) continuous_on
      interval[lift(&0),lift T1] /\
    (\w. pde_hsf (FE:real^(1,N)finite_sum->real^K) k 0 (drop w)) continuous_on
      interval[lift(&0),lift T1]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    MP_TAC(ISPECL [`FE:real^(1,N)finite_sum->real^K`; `&0 - e`; `tmax:real`;
                   `k:real^N`; `0`; `s:real`] PDE_HEAT_HCF_DERIV) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; MESON_TAC[]]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`pde_heig(k:real^N)`; `pde_fc (u0:real^N->real^K) k`;
                 `pde_hcf (FE:real^(1,N)finite_sum->real^K) k`; `T1:real`; `D:real`]
                PDE_HDUH_BOUND) THEN
  MP_TAC(ISPECL [`pde_heig(k:real^N)`; `pde_fs (u0:real^N->real^K) k`;
                 `pde_hsf (FE:real^(1,N)finite_sum->real^K) k`; `T1:real`; `D:real`]
                PDE_HDUH_BOUND) THEN
  ASM_REWRITE_TAC[PDE_HEAT_HEIG_POS] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "PHB" (MP_TAC o SPECL [`i':num`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "PHB" (MP_TAC o SPECL [`i':num`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  REWRITE_TAC[pde_hA; pde_hB] THEN
  ABBREV_TAC `lc = &1 + pde_heig(k:real^N)` THEN
  SUBGOAL_THEN `&1 <= lc` ASSUME_TAC THENL
   [EXPAND_TAC "lc" THEN MP_TAC(ISPEC `k:real^N` PDE_HEAT_HEIG_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lc pow i * (&i + &1) * ((&1 + T1) * D) <=
                lc pow L * (&L + &1) * ((&1 + T1) * D)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lc pow L * (&2 * (&L + &1) * (&1 + T1) * (&2 * As)) * fm =
                &2 * (lc pow L * (&L + &1) * ((&1 + T1) * D))` SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Closed forms of the iterated partials of the terms. *)

let pde_hform = new_definition
 `pde_hform (FE:real^(1,N)finite_sum->real^K) (u0:real^N->real^K) (IX:real^N->num)
            (C1:real^N->real) (C2:real^N->real) (SW:real^N->bool) (k:real^N) z =
    cos(&2 * pi * (k dot sndcart z)) %
      (C1 k % (if SW k then pde_hB FE u0 k else pde_hA FE u0 k) (IX k) (drop(fstcart z))) +
    sin(&2 * pi * (k dot sndcart z)) %
      (C2 k % (if SW k then pde_hA FE u0 k else pde_hB FE u0 k) (IX k) (drop(fstcart z)))`;;

let PDE_HEAT_TERM_FORMS = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 l.
     pde_hdata tmax e FE f u0 /\ ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) l
     ==> ?IX C1 C2 SW.
           !k. IX k <= LENGTH l /\
               abs(C1 k) <= (&1 + &2 * pi * infnorm k) pow (LENGTH l) /\
               abs(C2 k) <= (&1 + &2 * pi * infnorm k) pow (LENGTH l) /\
               !z. z IN interval(lift(&0),lift tmax) PCROSS (:real^N)
                   ==> iterated_partial l (pde_hterm FE u0 k) z =
                       pde_hform FE u0 IX C1 C2 SW k z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pde_hform] THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `k:real^N` THEN
  MP_TAC(ISPECL [`k:real^N`; `pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k`;
                 `pde_hB (FE:real^(1,N)finite_sum->real^K) u0 k`; `&0`; `tmax:real`]
                PDE_HEAT_TERM_ITERATED) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                   `f:real->real^N->real^K`; `u0:real^N->real^K`] PDE_HEAT_FAM_DERIV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[pde_hterm]);;

let PDE_HEAT_FORM_NORM = prove
 (`!(FE:real^(1,N)finite_sum->real^K) u0 IX C1 C2 SW k z q.
     abs(C1 k) <= q /\ abs(C2 k) <= q
     ==> norm(pde_hform FE u0 IX C1 C2 SW k z) <=
         q * (norm(pde_hA FE u0 k (IX k) (drop(fstcart z))) +
              norm(pde_hB FE u0 k (IX k) (drop(fstcart z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(X:real^K) Y c1 c2. abs c1 <= q /\ abs c2 <= q
        ==> norm(cos(&2 * pi * ((k:real^N) dot sndcart(z:real^(1,N)finite_sum))) % (c1 % X) +
                 sin(&2 * pi * (k dot sndcart z)) % (c2 % Y)) <= q * (norm X + norm Y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(c1 % (X:real^K)) + norm(c2 % (Y:real^K))` THEN
    REWRITE_TAC[PDE_FT_VMODE_NORM; NORM_MUL; REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[pde_hform] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_SIMP_TAC[]);;

let PDE_HEAT_HEIG_SHELL = prove
 (`!(k:real^N) m. k IN pde_shell m
                  ==> pde_heig k <= &4 * pi pow 2 * &(dimindex(:N)) * &m pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_heig] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN
  REWRITE_TAC[dot] THEN
  MP_TAC(ISPECL [`1..dimindex(:N)`; `\i. (k:real^N)$i * k$i`; `&m pow 2`] SUM_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; IN_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `k:real^N`; `i:num`] PDE_FT_SHELL_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_POW_2; GSYM REAL_ABS_MUL] THEN
  ONCE_REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((k:real^N)$i) * abs(k$i)` THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let PDE_HEAT_SHELL_ARITH = prove
 (`!m N0 L C. 1 <= m /\ &0 <= C
     ==> &((2 * m + 1) EXP N0) *
         ((&1 + &2 * pi * &m) pow L * (&1 + &4 * pi pow 2 * &N0 * &m pow 2) pow L * C *
          inv((&2 * pi * &m) pow (3 * L + N0 + 2))) <=
         (&3 pow N0 * (&1 + &2 * pi) pow L * (&1 + &4 * pi pow 2 * &N0) pow L * C) *
         inv(&m pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `x = &m` THEN
  SUBGOAL_THEN `&1 <= x` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= x pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * pi /\ &1 <= &2 * pi` STRIP_ASSUME_TAC THENL
   [MP_TAC PDE_FT_TWO_PI_GE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 * pi pow 2 * &N0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_POW_2; REAL_LE_SQUARE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * pi * x /\ &0 <= &4 * pi pow 2 * &N0 * x pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THEN TRY(ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN NO_TAC) THEN
    TRY ASM_REAL_ARITH_TAC THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&((2 * m + 1) EXP N0) <= &3 pow N0 * x pow N0 /\
    (&1 + &2 * pi * x) pow L <= (&1 + &2 * pi) pow L * x pow L /\
    (&1 + &4 * pi pow 2 * &N0 * x pow 2) pow L <=
    (&1 + &4 * pi pow 2 * &N0) pow L * x pow (2 * L) /\
    inv((&2 * pi * x) pow (3 * L + N0 + 2)) <= inv(x pow (3 * L + N0 + 2))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL; GSYM REAL_POW_POW] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[REAL_POS] THEN EXPAND_TAC "x" THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &0 <= &1 + y`) THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&2 * pi * x <= &2 * pi * x` MP_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(&1 + &2 * pi) * x = x + (&2 * pi) * x` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &0 <= &1 + y`) THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE];
        ALL_TAC] THEN
      SUBGOAL_THEN `(&1 + &4 * pi pow 2 * &N0) * x pow 2 =
                    x pow 2 + (&4 * pi pow 2 * &N0) * x pow 2` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&3 pow N0 * x pow N0) *
              (((&1 + &2 * pi) pow L * x pow L) *
               ((&1 + &4 * pi pow 2 * &N0) pow L * x pow (2 * L)) * C *
               inv(x pow (3 * L + N0 + 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN TRY(MATCH_MP_TAC REAL_LE_INV) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN TRY(MATCH_MP_TAC REAL_LE_INV) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN `x pow (3 * L + N0 + 2) = (x pow N0 * x pow L * x pow (2 * L)) * x pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(x pow N0 = &0) /\ ~(x pow L = &0) /\ ~(x pow (2 * L) = &0) /\
                ~(x pow 2 = &0)` MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let PDE_HEAT_FORM_SHELL_BOUND = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 T1 L IX C1 C2 SW.
     pde_hdata tmax e FE f u0 /\ &0 <= T1 /\ T1 < tmax /\
     (!k. IX k <= L /\
          abs(C1 k) <= (&1 + &2 * pi * infnorm k) pow L /\
          abs(C2 k) <= (&1 + &2 * pi * infnorm k) pow L)
     ==> ?C. &0 <= C /\
             !m z. 1 <= m /\ &0 <= drop(fstcart z) /\ drop(fstcart z) <= T1
                   ==> norm(vsum (pde_shell m) (\k. pde_hform FE u0 IX C1 C2 SW k z)) <=
                       C * inv(&m pow 2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CB")))) THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`; `T1:real`; `L:num`;
                 `3 * L + dimindex(:N) + 2`] PDE_HEAT_FAM_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FB"))) THEN
  EXISTS_TAC `&3 pow dimindex(:N) * (&1 + &2 * pi) pow L *
              (&1 + &4 * pi pow 2 * &(dimindex(:N))) pow L * C0` THEN
  SUBGOAL_THEN `&0 <= &1 + &2 * pi /\ &0 <= &1 + &4 * pi pow 2 * &(dimindex(:N))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &4 * pi pow 2 * &(dimindex(:N))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_POW_2; REAL_LE_SQUARE];
      MP_TAC PDE_FT_TWO_PI_GE_1 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `z:real^(1,N)finite_sum`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(pde_shell m:real^N->bool)) *
              ((&1 + &2 * pi * &m) pow L *
               (&1 + &4 * pi pow 2 * &(dimindex(:N)) * &m pow 2) pow L * C0 *
               inv((&2 * pi * &m) pow (3 * L + dimindex(:N) + 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_BOUND THEN REWRITE_TAC[PDE_FT_SHELL_FINITE] THEN
    X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `infnorm(k:real^N) = &m` ASSUME_TAC THENL
     [UNDISCH_TAC `(k:real^N) IN pde_shell m` THEN SIMP_TAC[pde_shell; IN_ELIM_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + &2 * pi * &m) pow L *
                (norm(pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k (IX k)
                        (drop(fstcart(z:real^(1,N)finite_sum)))) +
                 norm(pde_hB FE u0 k (IX k) (drop(fstcart z))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_HEAT_FORM_NORM THEN
      USE_THEN "CB" (MP_TAC o SPEC `k:real^N`) THEN
      REWRITE_TAC[ASSUME `infnorm(k:real^N) = &m`] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN
      SUBGOAL_THEN `&0 <= &2 * pi * &m` MP_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_POS; PI_POS_LE];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + pde_heig(k:real^N)) pow L * C0 *
                (if m = 0 then &1 else inv((&2 * pi * &m) pow (3 * L + dimindex(:N) + 2)))` THEN
    CONJ_TAC THENL
     [USE_THEN "FB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "CB" (MP_TAC o SPEC `k:real^N`) THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= m ==> ~(m = 0)`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS; PI_POS_LE]] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `k:real^N` PDE_HEAT_HEIG_POS) THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`k:real^N`; `m:num`] PDE_HEAT_HEIG_SHELL) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&((2 * m + 1) EXP dimindex(:N)) *
              ((&1 + &2 * pi * &m) pow L *
               (&1 + &4 * pi pow 2 * &(dimindex(:N)) * &m pow 2) pow L * C0 *
               inv((&2 * pi * &m) pow (3 * L + dimindex(:N) + 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_OF_NUM_LE; PDE_FT_SHELL_CARD] THEN
    SUBGOAL_THEN `&0 <= &2 * pi * &m /\ &0 <= &4 * pi pow 2 * &(dimindex(:N)) * &m pow 2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_POS; PI_POS_LE; REAL_POW_2; REAL_LE_SQUARE];
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_INV) THEN TRY(MATCH_MP_TAC REAL_POW_LE) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC PDE_HEAT_SHELL_ARITH THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Smoothness of the terms and shell sums of the heat series on              *)
(* (0,tmax) x R^N, uniform bounds C / m^2 for all their iterated partials on *)
(* (0,T1) x R^N, and term-by-term differentiation of the series              *)
(* (SMOOTH_MAP_ON_SERIES).                                                   *)
(* ========================================================================= *)

let PDE_HEAT_DIMINDEX_ST = prove
 (`dimindex(:(1,N)finite_sum) = dimindex(:N) + 1`,
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ARITH_TAC);;

(* Iterated partials of finite sums on open sets. *)

let PDE_HEAT_ITERATED_PARTIAL_VSUM_OPEN = prove
 (`!l s (g:A->real^M->real^N) ss.
      open s /\ FINITE ss /\ (!a. a IN ss ==> smooth_map_on s (g a))
      ==> !x. x IN s
              ==> iterated_partial l (\x. vsum ss (\a. g a x)) x =
                  vsum ss (\a. iterated_partial l (g a) x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; ETA_AX] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h
                (\x. vsum ss (\a. iterated_partial t ((g:A->real^M->real^N) a) x)) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`h:num`; `\a:A. iterated_partial t ((g:A->real^M->real^N) a)`;
                   `ss:A->bool`; `x:real^M`] PARTIAL_DERIVATIVE_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]]);;

(* A derivative family of time functions is smooth. *)

let PDE_HEAT_FAMILY_SMOOTH = prove
 (`!(A:num->real->real^K) a b.
     (!j t. a < t /\ t < b
            ==> ((\w. A j (drop w)) has_vector_derivative A (SUC j) t) (at (lift t)))
     ==> !j. smooth_map_on (interval(lift a,lift b)) (\w. A j (drop w))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`interval(lift a,lift b)`;
                 `\(l:num list) (w:real^1). (A:num->real->real^K) (LENGTH l) (drop w)`]
                SMOOTH_MAP_ON_PARTIAL_FAMILY) THEN
  REWRITE_TAC[OPEN_INTERVAL; DIMINDEX_1] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:num list`; `x:real^1`] THEN STRIP_TAC THEN
    REWRITE_TAC[NUMSEG_SING; VSUM_SING; LENGTH] THEN
    UNDISCH_TAC `(x:real^1) IN interval(lift a,lift b)` THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`LENGTH(l:num list)`; `drop x`]) THEN
    ASM_REWRITE_TAC[LIFT_DROP; has_vector_derivative] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; drop];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `j:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `REPLICATE j 1`) THEN
  REWRITE_TAC[LENGTH_REPLICATE] THEN DISCH_THEN MATCH_MP_TAC THEN
  SPEC_TAC(`j:num`,`j:num`) THEN INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; ALL] THEN
  ARITH_TAC);;

(* Smoothness of functions of time and of products on slabs. *)

let PDE_HEAT_SMOOTH_TIME_FN = prove
 (`!(P:real^1->real^K) a b.
     smooth_map_on (interval(lift a,lift b)) P
     ==> smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) (\z. P(fstcart z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (P:real^1->real^K)(fstcart z)) = P o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
    SIMP_TAC[];
    REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
    SIMP_TAC[LINEAR_FSTCART; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]]);;

let PDE_HEAT_SMOOTH_PRODUCT = prove
 (`!(c:real^N->real) (P:real^1->real^K) a b.
     smooth_map_on (:real^N) (\y. lift(c y)) /\
     smooth_map_on (interval(lift a,lift b)) P
     ==> smooth_map_on (interval(lift a,lift b) PCROSS (:real^N))
                       (\z. c(sndcart z) % P(fstcart z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS (:real^N)`;
                 `\z:real^(1,N)finite_sum. lift((c:real^N->real)(sndcart z))`;
                 `\z:real^(1,N)finite_sum. (P:real^1->real^K)(fstcart z)`]
                SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\y:real^N. lift((c:real^N->real) y)`;
                   `interval(lift a,lift b) PCROSS (:real^N)`] PDE_HEAT_SMOOTH_SPACE_FN) THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
    MATCH_MP_TAC PDE_HEAT_SMOOTH_TIME_FN THEN ASM_REWRITE_TAC[]]);;

(* The terms and shell sums are smooth on (0,tmax) x R^N. *)

let PDE_HEAT_TERM_SMOOTH = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 k.
     pde_hdata tmax e FE f u0
     ==> smooth_map_on (interval(lift(&0),lift tmax) PCROSS (:real^N))
                       (pde_hterm FE u0 k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`] PDE_HEAT_FAM_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:real^N`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. smooth_map_on (interval(lift(&0),lift tmax))
          (\w. pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k j (drop w)) /\
        smooth_map_on (interval(lift(&0),lift tmax)) (\w. pde_hB FE u0 k j (drop w))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k`; `&0`; `tmax:real`]
                  PDE_HEAT_FAMILY_SMOOTH) THEN
    MP_TAC(ISPECL [`pde_hB (FE:real^(1,N)finite_sum->real^K) u0 k`; `&0`; `tmax:real`]
                  PDE_HEAT_FAMILY_SMOOTH) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pde_hterm] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\y:real^N. cos(&2 * pi * (k dot y))`;
                   `\w:real^1. pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k 0 (drop w)`;
                   `&0`; `tmax:real`] PDE_HEAT_SMOOTH_PRODUCT);
    MP_TAC(ISPECL [`\y:real^N. sin(&2 * pi * (k dot y))`;
                   `\w:real^1. pde_hB (FE:real^(1,N)finite_sum->real^K) u0 k 0 (drop w)`;
                   `&0`; `tmax:real`] PDE_HEAT_SMOOTH_PRODUCT)] THEN
  ASM_REWRITE_TAC[PDE_FT_SMOOTH_LIFT_COS_SIN]);;

let PDE_HEAT_HSH_SMOOTH = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 m.
     pde_hdata tmax e FE f u0
     ==> smooth_map_on (interval(lift(&0),lift tmax) PCROSS (:real^N)) (pde_hsh FE u0 m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_hsh] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PDE_FT_SHELL_FINITE; ETA_AX] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_HEAT_TERM_SMOOTH THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `f:real->real^N->real^K`] THEN ASM_REWRITE_TAC[]);;

let PDE_HEAT_HSH_ITERATED = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 m l z.
     pde_hdata tmax e FE f u0 /\ z IN interval(lift(&0),lift tmax) PCROSS (:real^N)
     ==> iterated_partial l (pde_hsh FE u0 m) z =
         vsum (pde_shell m) (\k. iterated_partial l (pde_hterm FE u0 k) z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_hsh] THEN
  MP_TAC(ISPECL [`l:num list`; `interval(lift(&0),lift tmax) PCROSS (:real^N)`;
                 `pde_hterm (FE:real^(1,N)finite_sum->real^K) u0`;
                 `pde_shell m:real^N->bool`] PDE_HEAT_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ANTS_TAC THENL
   [SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PDE_FT_SHELL_FINITE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_HEAT_TERM_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `f:real->real^N->real^K`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Bounds C / m^2 for the iterated partials of the shell sums on slabs. *)

let PDE_HEAT_HSH_BOUND = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 T1 l.
     pde_hdata tmax e FE f u0 /\ &0 <= T1 /\ T1 < tmax /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) l
     ==> ?C. &0 <= C /\
             !m z. 1 <= m /\ z IN interval(lift(&0),lift T1) PCROSS (:real^N)
                   ==> norm(iterated_partial l (pde_hsh FE u0 m) z) <= C * inv(&m pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`; `l:num list`]
                PDE_HEAT_TERM_FORMS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `IX:real^N->num` (X_CHOOSE_THEN `C1:real^N->real`
    (X_CHOOSE_THEN `C2:real^N->real` (X_CHOOSE_THEN `SW:real^N->bool` (LABEL_TAC "TF"))))) THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`; `T1:real`;
                 `LENGTH(l:num list)`; `IX:real^N->num`; `C1:real^N->real`;
                 `C2:real^N->real`; `SW:real^N->bool`] PDE_HEAT_FORM_SHELL_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CB")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`w:real^1`; `y:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`; `m:num`; `l:num list`;
                 `pastecart (w:real^1) (y:real^N)`] PDE_HEAT_HSH_ITERATED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vsum (pde_shell m)
                 (\k. pde_hform (FE:real^(1,N)finite_sum->real^K) u0 IX C1 C2 SW k
                                (pastecart (w:real^1) (y:real^N))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "TF" (MP_TAC o SPEC `k:real^N`) THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    USE_THEN "CB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[FSTCART_PASTECART] THEN
    ASM_REAL_ARITH_TAC]);;

(* Term-by-term differentiation of the series on the slab (0,T1) x R^N. *)

let PDE_HEAT_SOL_SERIES_T1 = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 T1.
     pde_hdata tmax e FE f u0 /\ &0 < T1 /\ T1 < tmax
     ==> smooth_map_on (interval(lift(&0),lift T1) PCROSS (:real^N))
                       (\z. infsum (from 0) (\m. pde_hsh FE u0 m z)) /\
         !l z. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
               z IN interval(lift(&0),lift T1) PCROSS (:real^N)
               ==> ((\m. iterated_partial l (pde_hsh FE u0 m) z) sums
                    iterated_partial l (\z. infsum (from 0) (\m. pde_hsh FE u0 m z)) z)
                   (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SERIES THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(&0),lift tmax) PCROSS (:real^N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC PDE_HEAT_HSH_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`e:real`; `f:real->real^N->real^K`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[PDE_HEAT_DIMINDEX_ST] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`; `T1:real`; `l:num list`]
                PDE_HEAT_HSH_BOUND) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\n. C * inv(&n pow 2)` THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[PDE_FT_ZETA2_SUMMABLE] THEN ASM_SIMP_TAC[]);;

(* The solution candidate is smooth on (0,tmax) x R^N, with the series of   *)
(* iterated partials there.                                                  *)

let PDE_HEAT_SOL_SERIES = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0.
     pde_hdata tmax e FE f u0
     ==> smooth_map_on (interval(lift(&0),lift tmax) PCROSS (:real^N))
                       (\z. infsum (from 0) (\m. pde_hsh FE u0 m z)) /\
         !l z. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
               z IN interval(lift(&0),lift tmax) PCROSS (:real^N)
               ==> ((\m. iterated_partial l (pde_hsh FE u0 m) z) sums
                    iterated_partial l (\z. infsum (from 0) (\m. pde_hsh FE u0 m z)) z)
                   (from 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!z. z IN interval(lift(&0),lift tmax) PCROSS (:real^N)
        ==> ?T1. &0 < T1 /\ T1 < tmax /\
                 z IN interval(lift(&0),lift T1) PCROSS (:real^N)`
  (LABEL_TAC "LOC") THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN
    EXISTS_TAC `(drop w + tmax) / &2` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "LOC" (X_CHOOSE_THEN `T1:real` STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(z:real^(1,N)finite_sum) IN interval(lift(&0),lift tmax) PCROSS (:real^N)`)) THEN
    EXISTS_TAC `interval(lift(&0),lift T1) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                   `f:real->real^N->real^K`; `u0:real^N->real^K`; `T1:real`]
                  PDE_HEAT_SOL_SERIES_T1) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`l:num list`; `z:real^(1,N)finite_sum`] THEN STRIP_TAC THEN
    USE_THEN "LOC" (X_CHOOSE_THEN `T1:real` STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(z:real^(1,N)finite_sum) IN interval(lift(&0),lift tmax) PCROSS (:real^N)`)) THEN
    MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                   `f:real->real^N->real^K`; `u0:real^N->real^K`; `T1:real`]
                  PDE_HEAT_SOL_SERIES_T1) THEN
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Continuity up to t = 0.  The series of the closed forms converges         *)
(* uniformly on [0,T1] x R^N (M-test), so every iterated partial of the      *)
(* solution candidate has a continuous extension to [0,tmax) x R^N; the      *)
(* classical regularity pde_upto_classical.                                  *)
(* ========================================================================= *)

(* The M-test on a set, with bounds from some index on. *)

let PDE_HEAT_MTEST_ON = prove
 (`!(g:num->real^M->real^N) b s N0.
     (!m. g m continuous_on s) /\ summable (from 0) (\m. lift(b m)) /\
     (!m y. N0 <= m /\ y IN s ==> norm(g m y) <= b m)
     ==> (!y. y IN s ==> ((\m. g m y) sums infsum (from 0) (\m. g m y)) (from 0)) /\
         (\y. infsum (from 0) (\m. g m y)) continuous_on s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\(y:real^M) (m:num). (g:num->real^M->real^N) m y`; `b:num->real`;
                 `\y:real^M. y IN s`; `from 0`] SERIES_COMPARISON_UNIFORM) THEN
  REWRITE_TAC[FROM_INTER_NUMSEG; IN_FROM; LE_0] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; GSYM summable] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `N0:num` THEN ASM_SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (LABEL_TAC "U"))] THEN
  SUBGOAL_THEN
   `!y. y IN s ==> ((\m. (g:num->real^M->real^N) m y) sums l y) (from 0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[sums; FROM_INTER_NUMSEG; LIM_SEQUENTIALLY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "U" (MP_TAC o C MATCH_MP (ASSUME `&0 < e`)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN s ==> infsum (from 0) (\m. (g:num->real^M->real^N) m y) = l y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `l:real^M->real^N` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(ISPEC `sequentially` CONTINUOUS_UNIFORM_LIMIT) THEN
  EXISTS_TAC `\n y. vsum(0..n) (\m. (g:num->real^M->real^N) m y)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "U" (MP_TAC o C MATCH_MP (ASSUME `&0 < e`)) THEN
    REWRITE_TAC[dist] THEN MESON_TAC[]]);;

(* Continuity of products of functions of space and of time on closed slabs. *)

let PDE_HEAT_CONT_PRODUCT = prove
 (`!(c:real^N->real) (P:real^1->real^K) T1.
     (\y. lift(c y)) continuous_on (:real^N) /\
     P continuous_on interval[lift(&0),lift T1]
     ==> (\z. c(sndcart z) % P(fstcart z)) continuous_on
         (interval[lift(&0),lift T1] PCROSS (:real^N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`interval[lift(&0),lift T1] PCROSS (:real^N)`;
                 `\z:real^(1,N)finite_sum. (c:real^N->real)(sndcart z)`;
                 `\z:real^(1,N)finite_sum. (P:real^1->real^K)(fstcart z)`]
                CONTINUOUS_ON_MUL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `lift o (\z:real^(1,N)finite_sum. (c:real^N->real)(sndcart z)) =
                  (\y. lift(c y)) o sndcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (P:real^1->real^K)(fstcart z)) = P o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    ASM_REWRITE_TAC[IMAGE_FSTCART_PCROSS; UNIV_NOT_EMPTY]]);;

let PDE_HEAT_FORM_CONT = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 IX C1 C2 SW T1 k.
     pde_hdata tmax e FE f u0 /\ &0 < T1 /\ T1 < tmax
     ==> (\z. pde_hform FE u0 IX C1 C2 SW k z) continuous_on
         (interval[lift(&0),lift T1] PCROSS (:real^N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`; `T1:real`]
                PDE_HEAT_FAM_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:real^N`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. (\w. (if SW (k:real^N) then pde_hB (FE:real^(1,N)finite_sum->real^K) u0 k
             else pde_hA FE u0 k) j (drop w)) continuous_on interval[lift(&0),lift T1] /\
        (\w. (if SW k then pde_hA FE u0 k else pde_hB FE u0 k) j (drop w))
          continuous_on interval[lift(&0),lift T1]`
  ASSUME_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pde_hform] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\y:real^N. cos(&2 * pi * (k dot y))`;
                   `\w:real^1. (C1:real^N->real) k %
                       (if SW (k:real^N) then pde_hB (FE:real^(1,N)finite_sum->real^K) u0 k
                        else pde_hA FE u0 k) (IX k) (drop w)`;
                   `T1:real`] PDE_HEAT_CONT_PRODUCT);
    MP_TAC(ISPECL [`\y:real^N. sin(&2 * pi * (k dot y))`;
                   `\w:real^1. (C2:real^N->real) k %
                       (if SW (k:real^N) then pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k
                        else pde_hB FE u0 k) (IX k) (drop w)`;
                   `T1:real`] PDE_HEAT_CONT_PRODUCT)] THEN
  REWRITE_TAC[PDE_FT_CONT_LIFT_COS_SIN] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[]);;

(* Uniform convergence and continuity of the series of closed forms. *)

let PDE_HEAT_FORM_SERIES_CONT = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 T1 L IX C1 C2 SW.
     pde_hdata tmax e FE f u0 /\ &0 < T1 /\ T1 < tmax /\
     (!k. IX k <= L /\
          abs(C1 k) <= (&1 + &2 * pi * infnorm k) pow L /\
          abs(C2 k) <= (&1 + &2 * pi * infnorm k) pow L)
     ==> (!z. z IN interval[lift(&0),lift T1] PCROSS (:real^N)
              ==> ((\m. vsum (pde_shell m) (\k. pde_hform FE u0 IX C1 C2 SW k z)) sums
                   infsum (from 0)
                     (\m. vsum (pde_shell m) (\k. pde_hform FE u0 IX C1 C2 SW k z)))
                  (from 0)) /\
         (\z. infsum (from 0)
                (\m. vsum (pde_shell m) (\k. pde_hform FE u0 IX C1 C2 SW k z)))
         continuous_on (interval[lift(&0),lift T1] PCROSS (:real^N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`; `T1:real`; `L:num`;
                 `IX:real^N->num`; `C1:real^N->real`; `C2:real^N->real`; `SW:real^N->bool`]
                PDE_HEAT_FORM_SHELL_BOUND) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CB"))) THEN
  MATCH_MP_TAC PDE_HEAT_MTEST_ON THEN
  EXISTS_TAC `\m. C * inv(&m pow 2)` THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[PDE_FT_ZETA2_SUMMABLE] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    REWRITE_TAC[PDE_FT_SHELL_FINITE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PDE_HEAT_FORM_CONT THEN
    MAP_EVERY EXISTS_TAC [`tmax:real`; `e:real`; `f:real->real^N->real^K`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN USE_THEN "CB" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART]]);;

(* Continuity on [0,tmax) x R^N from continuity on every [0,T1] x R^N. *)

let PDE_HEAT_CONT_LOCAL = prove
 (`!(h:real^(1,N)finite_sum->real^K) tmax.
     (!T1. &0 < T1 /\ T1 < tmax
           ==> h continuous_on (interval[lift(&0),lift T1] PCROSS (:real^N)))
     ==> h continuous_on {pastecart (lift t) y | &0 <= t /\ t < tmax /\ y IN (:real^N)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_on; FORALL_IN_GSPEC; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(t + tmax) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (y:real^N)`) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  EXISTS_TAC `min d ((tmax - t) / &2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `w:real^N`] THEN REPEAT DISCH_TAC THEN
  USE_THEN "D" MATCH_MP_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
  MP_TAC(ISPECL [`pastecart (lift s) (w:real^N)`; `pastecart (lift t) (y:real^N)`]
                PDE_ST_TIME_DIST) THEN
  REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN
  UNDISCH_TAC `dist(pastecart (lift s) (w:real^N),pastecart (lift t) y) <
               min d ((tmax - t) / &2)` THEN
  REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC);;

(* The closed forms of the empty list of partials are the terms. *)

let PDE_HEAT_TRIVIAL_FORM = prove
 (`!(FE:real^(1,N)finite_sum->real^K) u0 k z.
     pde_hform FE u0 (\k. 0) (\k. &1) (\k. &1) (\k. F) k z = pde_hterm FE u0 k z`,
  REWRITE_TAC[pde_hform; pde_hterm; VECTOR_MUL_LID]);;

let PDE_HEAT_UH = prove
 (`!(FE:real^(1,N)finite_sum->real^K) u0.
     (\z. pde_hsol FE u0 (drop(fstcart z)) (sndcart z)) =
     (\z. infsum (from 0) (\m. pde_hsh FE u0 m z))`,
  REWRITE_TAC[FUN_EQ_THM; pde_hsol; LIFT_DROP; PASTECART_FST_SND]);;

let PDE_HEAT_SOL_CONT = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0.
     pde_hdata tmax e FE f u0
     ==> (\z. infsum (from 0) (\m. pde_hsh FE u0 m z)) continuous_on
         {pastecart (lift t) y | &0 <= t /\ t < tmax /\ y IN (:real^N)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_HEAT_CONT_LOCAL THEN
  X_GEN_TAC `T1:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`; `T1:real`; `0`;
                 `\k:real^N. 0`; `\k:real^N. &1`; `\k:real^N. &1`; `\k:real^N. F`]
                PDE_HEAT_FORM_SERIES_CONT) THEN
  ASM_REWRITE_TAC[PDE_HEAT_TRIVIAL_FORM; LE_REFL; real_pow; REAL_ABS_NUM; REAL_LE_REFL] THEN
  REWRITE_TAC[pde_hsh] THEN SIMP_TAC[]);;

(* Classical regularity of the solution candidate on [0,tmax) x R^N. *)

let PDE_HEAT_CLASSICAL = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0.
     pde_hdata tmax e FE f u0
     ==> pde_upto_classical (&0) tmax (:real^N) (pde_hsol FE u0) /\
         (\w. pde_hsol FE u0 (drop(fstcart w)) (sndcart w)) continuous_on
           {pastecart (lift t) y | &0 <= t /\ t < tmax /\ y IN (:real^N)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[pde_upto_classical; PDE_HEAT_UH] THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`] PDE_HEAT_SOL_SERIES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SER")) THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`] PDE_HEAT_SOL_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`; `l:num list`]
                PDE_HEAT_TERM_FORMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM PDE_HEAT_DIMINDEX_ST]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `IX:real^N->num` (X_CHOOSE_THEN `C1:real^N->real`
    (X_CHOOSE_THEN `C2:real^N->real` (X_CHOOSE_THEN `SW:real^N->bool` (LABEL_TAC "TF"))))) THEN
  EXISTS_TAC `\z. infsum (from 0)
                    (\m. vsum (pde_shell m)
                           (\k. pde_hform (FE:real^(1,N)finite_sum->real^K) u0 IX C1 C2 SW k z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_HEAT_CONT_LOCAL THEN X_GEN_TAC `T1:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                   `f:real->real^N->real^K`; `u0:real^N->real^K`; `T1:real`;
                   `LENGTH(l:num list)`; `IX:real^N->num`; `C1:real^N->real`;
                   `C2:real^N->real`; `SW:real^N->bool`] PDE_HEAT_FORM_SERIES_CONT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN MATCH_MP_TAC SUMS_EQ THEN
  EXISTS_TAC `\m. iterated_partial l (pde_hsh (FE:real^(1,N)finite_sum->real^K) u0 m)
                                     (pastecart (lift t) (y:real^N))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                   `f:real->real^N->real^K`; `u0:real^N->real^K`; `m:num`; `l:num list`;
                   `pastecart (lift t) (y:real^N)`] PDE_HEAT_HSH_ITERATED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "TF" (MP_TAC o SPEC `k:real^N`) THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP];
    USE_THEN "SER" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP]]);;

(* ========================================================================= *)
(* The series solves the heat equation                                       *)
(* u_t = Laplacian u + f on (0,tmax) x R^N, takes the initial value u0, is   *)
(* periodic; with PDE_SEELEY this gives PDE_TORUS_HEAT.                      *)
(* ========================================================================= *)

let PDE_HEAT_ITERATED_SING = prove
 (`!(g:real^M->real^N) h. iterated_partial [h] g = partial_derivative h g`,
  REWRITE_TAC[iterated_partial]);;

(* First space partials of a term on a slab, in closed form. *)

let PDE_HEAT_TERM_PARTIAL_SLAB = prove
 (`!(k:real^N) (P:real->real^K) Q P' Q' a b i.
     (!t. a < t /\ t < b
          ==> ((\w. P(drop w)) has_vector_derivative P' t) (at (lift t)) /\
              ((\w. Q(drop w)) has_vector_derivative Q' t) (at (lift t))) /\
     1 <= i /\ i <= dimindex(:N)
     ==> !z. z IN interval(lift a,lift b) PCROSS (:real^N)
             ==> partial_derivative (1 + i)
                   (\z. cos(&2 * pi * (k dot sndcart z)) % P(drop(fstcart z)) +
                        sin(&2 * pi * (k dot sndcart z)) % Q(drop(fstcart z))) z =
                 cos(&2 * pi * (k dot sndcart z)) % ((&2 * pi * k$i) % Q(drop(fstcart z))) +
                 sin(&2 * pi * (k dot sndcart z)) % (--(&2 * pi * k$i) % P(drop(fstcart z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`w:real^1`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop w`) THEN ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^N`; `P:real->real^K`; `Q:real->real^K`;
                 `(P':real->real^K) (drop w)`; `(Q':real->real^K) (drop w)`;
                 `pastecart (w:real^1) (y:real^N)`; `1 + i`] PDE_HEAT_TERM_PARTIAL) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `~(1 + i = 1) /\ (1 + i) - 1 = i` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(* Second space partials of a term: multiplication by -(2 pi k_i)^2. *)

let PDE_HEAT_TERM_SECOND = prove
 (`!(k:real^N) (A:num->real->real^K) B a b i z.
     (!j t. a < t /\ t < b
            ==> ((\w. A j (drop w)) has_vector_derivative A (SUC j) t) (at (lift t)) /\
                ((\w. B j (drop w)) has_vector_derivative B (SUC j) t) (at (lift t))) /\
     z IN interval(lift a,lift b) PCROSS (:real^N) /\ 1 <= i /\ i <= dimindex(:N)
     ==> iterated_partial [1 + i; 1 + i]
           (\z. cos(&2 * pi * (k dot sndcart z)) % A 0 (drop(fstcart z)) +
                sin(&2 * pi * (k dot sndcart z)) % B 0 (drop(fstcart z))) z =
         --((&2 * pi * k$i) pow 2) %
           (cos(&2 * pi * (k dot sndcart z)) % A 0 (drop(fstcart z)) +
            sin(&2 * pi * (k dot sndcart z)) % B 0 (drop(fstcart z)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[iterated_partial] THEN
  MP_TAC(ISPECL [`k:real^N`; `(A:num->real->real^K) 0`; `(B:num->real->real^K) 0`;
                 `(A:num->real->real^K) (SUC 0)`; `(B:num->real->real^K) (SUC 0)`;
                 `a:real`; `b:real`; `i:num`] PDE_HEAT_TERM_PARTIAL_SLAB) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `partial_derivative (1 + i)
      (\z. cos(&2 * pi * (k dot sndcart z)) %
             ((&2 * pi * (k:real^N)$i) % (B:num->real->real^K) 0 (drop(fstcart z))) +
           sin(&2 * pi * (k dot sndcart z)) %
             (--(&2 * pi * k$i) % (A:num->real->real^K) 0 (drop(fstcart z)))) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N`;
                 `\t. (&2 * pi * (k:real^N)$i) % (B:num->real->real^K) 0 t`;
                 `\t. --(&2 * pi * (k:real^N)$i) % (A:num->real->real^K) 0 t`;
                 `\t. (&2 * pi * (k:real^N)$i) % (B:num->real->real^K) (SUC 0) t`;
                 `\t. --(&2 * pi * (k:real^N)$i) % (A:num->real->real^K) (SUC 0) t`;
                 `a:real`; `b:real`; `i:num`] PDE_HEAT_TERM_PARTIAL_SLAB) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN ASM_SIMP_TAC[];
    DISCH_THEN(MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* The heat equation for a single term. *)

let PDE_HEAT_TERM_HEAT = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 k t y.
     pde_hdata tmax e FE f u0 /\ &0 < t /\ t < tmax
     ==> partial_derivative 1 (pde_hterm FE u0 k) (pastecart (lift t) y) =
         vsum(1..dimindex(:N))
           (\i. iterated_partial [1 + i; 1 + i] (pde_hterm FE u0 k) (pastecart (lift t) y)) +
         pde_mode (f t) k y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_hdata]) THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`] PDE_HEAT_FAM_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:real^N`) THEN DISCH_TAC THEN
  REWRITE_TAC[pde_hterm] THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. iterated_partial [1 + i; 1 + i]
             (\z. cos(&2 * pi * (k dot sndcart z)) %
                    pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k 0 (drop(fstcart z)) +
                  sin(&2 * pi * (k dot sndcart z)) % pde_hB FE u0 k 0 (drop(fstcart z)))
             (pastecart (lift t) (y:real^N))) =
    --(pde_heig k) % (cos(&2 * pi * (k dot y)) % pde_hA FE u0 k 0 t +
                      sin(&2 * pi * (k dot y)) % pde_hB FE u0 k 0 t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `vsum(1..dimindex(:N))
        (\i. --((&2 * pi * (k:real^N)$i) pow 2) %
             (cos(&2 * pi * (k dot y)) % pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k 0 t +
              sin(&2 * pi * (k dot (y:real^N))) % pde_hB FE u0 k 0 t))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`k:real^N`; `pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k`;
                     `pde_hB (FE:real^(1,N)finite_sum->real^K) u0 k`; `&0`; `tmax:real`;
                     `i:num`; `pastecart (lift t) (y:real^N)`] PDE_HEAT_TERM_SECOND) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP;
                      FSTCART_PASTECART; SNDCART_PASTECART];
      REWRITE_TAC[VSUM_RMUL; pde_heig] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[SUM_NEG; dot; GSYM SUM_LMUL] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N`; `pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k 0`;
                 `pde_hB (FE:real^(1,N)finite_sum->real^K) u0 k 0`;
                 `pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k (SUC 0) t`;
                 `pde_hB (FE:real^(1,N)finite_sum->real^K) u0 k (SUC 0) t`;
                 `pastecart (lift t) (y:real^N)`; `1`] PDE_HEAT_TERM_PARTIAL) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `pde_hcf (FE:real^(1,N)finite_sum->real^K) k 0 t = pde_fc (f t) k /\
    pde_hsf FE k 0 t = pde_fs (f t) k`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[pde_hcf; pde_hsf; REPLICATE; iterated_partial] THEN
    SUBGOAL_THEN `(\y. (FE:real^(1,N)finite_sum->real^K)(pastecart (lift t) y)) =
                  (f:real->real^N->real^K) t`
    (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[pde_hA; pde_hB; CONJUNCT2 pde_hduh; pde_mode] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* The heat equation for a shell sum. *)

let PDE_HEAT_HSH_HEAT = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 m t y.
     pde_hdata tmax e FE f u0 /\ &0 < t /\ t < tmax
     ==> iterated_partial [1] (pde_hsh FE u0 m) (pastecart (lift t) y) =
         vsum(1..dimindex(:N))
           (\i. iterated_partial [1 + i; 1 + i] (pde_hsh FE u0 m) (pastecart (lift t) y)) +
         pde_fsh (f t) m y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (lift t) (y:real^N) IN interval(lift(&0),lift tmax) PCROSS (:real^N)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`; `m:num`]
                PDE_HEAT_HSH_ITERATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[pde_fsh] THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. vsum (pde_shell m)
             (\k. iterated_partial [1 + i; 1 + i] (pde_hterm (FE:real^(1,N)finite_sum->real^K) u0 k)
                                   (pastecart (lift t) (y:real^N)))) =
    vsum (pde_shell m)
      (\k. vsum(1..dimindex(:N))
             (\i. iterated_partial [1 + i; 1 + i] (pde_hterm FE u0 k) (pastecart (lift t) y)))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\i k. iterated_partial [1 + i; 1 + i]
                            (pde_hterm (FE:real^(1,N)finite_sum->real^K) u0 k)
                            (pastecart (lift t) (y:real^N))`;
                   `1..dimindex(:N)`; `pde_shell m:real^N->bool`] VSUM_SWAP) THEN
    REWRITE_TAC[FINITE_NUMSEG; PDE_FT_SHELL_FINITE];
    ALL_TAC] THEN
  SIMP_TAC[GSYM VSUM_ADD; PDE_FT_SHELL_FINITE] THEN MATCH_MP_TAC VSUM_EQ THEN
  X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN REWRITE_TAC[PDE_HEAT_ITERATED_SING] THEN
  MATCH_MP_TAC PDE_HEAT_TERM_HEAT THEN
  MAP_EVERY EXISTS_TAC [`tmax:real`; `e:real`] THEN ASM_REWRITE_TAC[]);;

(* Series of finite sums. *)

let PDE_HEAT_SERIES_VSUM = prove
 (`!(a:B->num->real^K) A s k.
     FINITE s /\ (!i. i IN s ==> (a i sums A i) k)
     ==> ((\m. vsum s (\i. a i m)) sums vsum s A) k`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; SERIES_0; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_ADD THEN ASM_SIMP_TAC[ETA_AX]);;

(* The time derivative of the solution candidate is its Laplacian plus f. *)

let PDE_HEAT_SOL_TIME = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 t y.
     pde_hdata tmax e FE f u0 /\ &0 < t /\ t < tmax
     ==> partial_derivative 1 (\z. infsum (from 0) (\m. pde_hsh FE u0 m z))
                            (pastecart (lift t) y) =
         vsum(1..dimindex(:N))
           (\i. iterated_partial [1 + i; 1 + i]
                  (\z. infsum (from 0) (\m. pde_hsh FE u0 m z)) (pastecart (lift t) y)) +
         f t y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_hdata]) THEN
  SUBGOAL_THEN `pastecart (lift t) (y:real^N) IN interval(lift(&0),lift tmax) PCROSS (:real^N)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`] PDE_HEAT_SOL_SERIES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "SER" o CONJUNCT2) THEN
  MATCH_MP_TAC SERIES_UNIQUE THEN
  EXISTS_TAC `\m. iterated_partial [1] (pde_hsh (FE:real^(1,N)finite_sum->real^K) u0 m)
                                       (pastecart (lift t) (y:real^N))` THEN
  EXISTS_TAC `from 0` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM PDE_HEAT_ITERATED_SING] THEN USE_THEN "SER" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ALL; PDE_HEAT_DIMINDEX_ST] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUMS_EQ THEN
  EXISTS_TAC `\m. vsum(1..dimindex(:N))
                    (\i. iterated_partial [1 + i; 1 + i]
                           (pde_hsh (FE:real^(1,N)finite_sum->real^K) u0 m)
                           (pastecart (lift t) (y:real^N))) +
                  pde_fsh ((f:real->real^N->real^K) t) m y` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC PDE_HEAT_HSH_HEAT THEN
    MAP_EVERY EXISTS_TAC [`tmax:real`; `e:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SERIES_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_HEAT_SERIES_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    USE_THEN "SER" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ALL; PDE_HEAT_DIMINDEX_ST] THEN ASM_ARITH_TAC;
    MP_TAC(ISPEC `(f:real->real^N->real^K) t` PDE_FT_FOURIER_SERIES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(f:real->real^N->real^K) t =
                    (\y. (FE:real^(1,N)finite_sum->real^K)(pastecart (lift t) y))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN CONV_TAC SYM_CONV THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC PDE_HEAT_SLICE_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`&0 - e`; `tmax:real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPECL [`[]:num list`; `y:real^N`]) THEN
      REWRITE_TAC[ALL; iterated_partial]]]);;

(* The operator with coefficients (mat 1, 0, 0) is the Laplacian. *)

let PDE_HEAT_LOP_LAPLACE = prove
 (`!(u:real->real^N->real^K) t y.
     pde_lop (\t y. mat 1) (\t y i. mat 0) (\t y. mat 0) u t y =
     vsum(1..dimindex(:N)) (\i. partial_derivative i (partial_derivative i (u t)) y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pde_lop; MATRIX_VECTOR_MUL_LZERO; VSUM_0; VECTOR_ADD_RID] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum(1..dimindex(:N))
                (\j. if j = i
                     then partial_derivative i
                            (partial_derivative i ((u:real->real^N->real^K) t)) y
                     else vec 0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MAT_COMPONENT] THEN
    ASM_CASES_TAC `j:num = i` THEN ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
    SUBGOAL_THEN `~(i:num = j)` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[VSUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]]);;

(* The solution candidate satisfies the heat equation on (0,tmax). *)

let PDE_HEAT_SOL_PDE = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 t y.
     pde_hdata tmax e FE f u0 /\ &0 < t /\ t < tmax
     ==> ((\s. pde_hsol FE u0 (drop s) y) has_vector_derivative
          (pde_lop (\t y. mat 1) (\t y i. mat 0) (\t y. mat 0) (pde_hsol FE u0) t y + f t y))
         (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`] PDE_HEAT_SOL_SERIES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `pastecart (lift t) (y:real^N) IN interval(lift(&0),lift tmax) PCROSS (:real^N)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> partial_derivative i
              (partial_derivative i (pde_hsol (FE:real^(1,N)finite_sum->real^K) u0 t)) y =
            iterated_partial [1 + i; 1 + i] (\z. infsum (from 0) (\m. pde_hsh FE u0 m z))
                             (pastecart (lift t) (y:real^N))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `pde_hsol (FE:real^(1,N)finite_sum->real^K) u0 t =
      (\y. infsum (from 0) (\m. pde_hsh FE u0 m (pastecart (lift t) y)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_hsol]; ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`[i; i]:num list`;
      `\z:real^(1,N)finite_sum. infsum (from 0) (\m. pde_hsh (FE:real^(1,N)finite_sum->real^K) u0 m z)`;
      `interval(lift(&0),lift tmax) PCROSS (:real^N)`; `lift t`; `y:real^N`]
     PDE_ST_SLICE_ITERATED)) THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; ALL; MAP; iterated_partial];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. pde_hsol (FE:real^(1,N)finite_sum->real^K) u0 (drop s) y) =
    (\r. infsum (from 0) (\m. pde_hsh FE u0 m (pastecart r y)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_hsol; LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\z:real^(1,N)finite_sum. infsum (from 0) (\m. pde_hsh (FE:real^(1,N)finite_sum->real^K) u0 m z)`;
    `t:real`; `y:real^N`] PDE_ST_TIME_DERIV)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift(&0),lift tmax) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PDE_HEAT_LOP_LAPLACE] THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. partial_derivative i
             (partial_derivative i (pde_hsol (FE:real^(1,N)finite_sum->real^K) u0 t)) y) =
    vsum(1..dimindex(:N))
      (\i. iterated_partial [1 + i; 1 + i] (\z. infsum (from 0) (\m. pde_hsh FE u0 m z))
                            (pastecart (lift t) (y:real^N)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PDE_HEAT_SOL_TIME THEN
  MAP_EVERY EXISTS_TAC [`tmax:real`; `e:real`] THEN ASM_REWRITE_TAC[]);;

(* Initial value and periodicity. *)

let PDE_HEAT_SOL_INIT = prove
 (`!tmax e (FE:real^(1,N)finite_sum->real^K) f u0 y.
     pde_hdata tmax e FE f u0 ==> pde_hsol FE u0 (&0) y = u0 y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_hdata]) THEN
  REWRITE_TAC[pde_hsol] THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
  MP_TAC(ISPEC `u0:real^N->real^K` PDE_FT_FOURIER_SERIES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`[]:num list`; `y:real^N`]) THEN
  REWRITE_TAC[ALL; iterated_partial] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[pde_fsh; pde_hsh; pde_hterm; pde_mode; pde_hA; pde_hB; pde_hduh;
              FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; INTEGRAL_REFL;
              REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0; VECTOR_MUL_LID; VECTOR_ADD_RID]);;

let PDE_HEAT_SOL_ZPER = prove
 (`!(FE:real^(1,N)finite_sum->real^K) u0 t. pde_zper (pde_hsol FE u0 t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_zper] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[pde_hsol] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[pde_hsh] THEN MATCH_MP_TAC VSUM_EQ THEN
  X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[pde_hterm; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  SUBGOAL_THEN `pde_zlat(k:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDE_FT_SHELL_ZLAT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N`; `pde_hA (FE:real^(1,N)finite_sum->real^K) u0 k 0 t`;
                 `pde_hB (FE:real^(1,N)finite_sum->real^K) u0 k 0 t`] PDE_FT_VMODE_ZPER) THEN
  ASM_REWRITE_TAC[pde_zper] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The flat heat equation on the torus (the main theorem of this unit). *)

let PDE_TORUS_HEAT = prove
 (`!tmax (f:real->real^N->real^K) u0.
        &0 < tmax /\ pde_upto (&0) tmax (:real^N) f /\ (!t. pde_zper (f t)) /\
        smooth_map_on (:real^N) u0 /\ pde_zper u0
        ==> ?u. pde_tsol tmax (\t y. mat 1:real^N^N) (\t y i. mat 0:real^K^K)
                         (\t y. mat 0:real^K^K) f u0 u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pde_upto]) THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FE:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pde_hdata tmax e (FE:real^(1,N)finite_sum->real^K) f u0` ASSUME_TAC THENL
   [REWRITE_TAC[pde_hdata] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `pde_hsol (FE:real^(1,N)finite_sum->real^K) u0` THEN
  REWRITE_TAC[pde_tsol; PDE_HEAT_SOL_ZPER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_SEELEY THEN
    MP_TAC(ISPECL [`tmax:real`; `e:real`; `FE:real^(1,N)finite_sum->real^K`;
                   `f:real->real^N->real^K`; `u0:real^N->real^K`] PDE_HEAT_CLASSICAL) THEN
    ASM_SIMP_TAC[OPEN_UNIV];
    X_GEN_TAC `y:real^N` THEN MATCH_MP_TAC PDE_HEAT_SOL_INIT THEN
    MAP_EVERY EXISTS_TAC [`tmax:real`; `e:real`; `f:real->real^N->real^K`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_HEAT_SOL_PDE THEN
    MAP_EVERY EXISTS_TAC [`tmax:real`; `e:real`] THEN ASM_REWRITE_TAC[]]);;

