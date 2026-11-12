(* ========================================================================= *)
(* pc_pde_rdt_tame: the Ricci-DeTurck existence, part 2, tame pointwise      *)
(* estimates on open sets of R^N: Leibniz for bilinear products with the     *)
(* full jet sum, its tame form (at most one factor of high order), and the   *)
(* tame composition bound (Faa di Bruno): a smooth function of a map K has   *)
(* derivatives of order n bounded linearly by the n-jet of K, with           *)
(* a constant that only depends on bounds of the outer function and on the   *)
(* low-order jets of K.                                                      *)
(*                                                                           *)
(* First Leibniz on open sets.                                               *)
(* ========================================================================= *)

needs "src/pc_pde_rdt.ml";;
needs "src/pc_wan_defs.ml";;
needs "src/pc_pde_menergy.ml";;
needs "src/pc_p2c_cgtrans.ml";;

prioritize_real();;
type_invention_error := true;;

let RDT_JETN_0 = prove
 (`!(f:real^N->real^P) x. pde_jetn 0 f x = norm(f x)`,
  REWRITE_TAC[pde_jetn; PDE_INDEX_LISTS_0; SUM_SING; iterated_partial]);;

let RDT_BILINEAR_STEP_OPEN = prove
 (`!(bb:real^P->real^Q->real^K) (f:real^N->real^P) g U l i x.
        bilinear bb /\ open U /\ smooth_map_on U f /\ smooth_map_on U g /\ x IN U
        ==> iterated_partial (APPEND l [i]) (\x. bb (f x) (g x)) x =
            iterated_partial l (\x. bb (partial_derivative i f x) (g x)) x +
            iterated_partial l (\x. bb (f x) (partial_derivative i g x)) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `iterated_partial l
     (\x. (bb:real^P->real^Q->real^K) (partial_derivative i (f:real^N->real^P) x)
                                      ((g:real^N->real^Q) x) +
          bb (f x) (partial_derivative i g x)) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC PDE_PARTIAL_BILINEAR THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL
     [`l:num list`; `U:real^N->bool`;
      `\x. (bb:real^P->real^Q->real^K) (partial_derivative i (f:real^N->real^P) x)
                                       ((g:real^N->real^Q) x)`;
      `\x. (bb:real^P->real^Q->real^K) ((f:real^N->real^P) x)
                                       (partial_derivative i (g:real^N->real^Q) x)`]
     PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_BILINEAR_OPEN THEN
      ASM_REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[]]]);;

(* Leibniz with the full jet sum (crude constant 2^n).                      *)

let RDT_JET_SUM_SHIFT = prove
 (`!(f:real^N->real^P) (g:real^N->real^Q) x n.
        sum(0..n) (\m. pde_jetn (SUC m) f x * pde_jetn (n - m) g x) <=
        sum(0..SUC n) (\m. pde_jetn m f x * pde_jetn (SUC n - m) g x) /\
        sum(0..n) (\m. pde_jetn m f x * pde_jetn (SUC(n - m)) g x) <=
        sum(0..SUC n) (\m. pde_jetn m f x * pde_jetn (SUC n - m) g x)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [MATCH_MP SUM_CLAUSES_LEFT (SPEC `SUC n` LE_0)] THEN
    REWRITE_TAC[ADD1; SUM_OFFSET] THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) - (i + 1) = n - i`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> b <= a + b`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PDE_JETN_POS];
    SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b /\ &0 <= c ==> a <= b + c`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PDE_JETN_POS]]]);;

let RDT_LEIBNIZ_JET = prove
 (`!(bb:real^P->real^Q->real^K) M.
     bilinear bb /\ (!x y. norm(bb x y) <= M * norm x * norm y) /\ &0 <= M
     ==> !l (U:real^N->bool) f g x.
           open U /\ smooth_map_on U f /\ smooth_map_on U g /\ x IN U /\
           ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
           ==> norm(iterated_partial l (\x. bb (f x) (g x)) x) <=
               &2 pow (LENGTH l) * M *
               sum(0..LENGTH l) (\m. pde_jetn m f x * pde_jetn (LENGTH l - m) g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!l (U:real^N->bool) (f:real^N->real^P) (g:real^N->real^Q) x.
        open U /\ smooth_map_on U f /\ smooth_map_on U g /\ x IN U /\
        ALL (\i. 1 <= i /\ i <= dimindex(:N)) (REVERSE l)
        ==> norm(iterated_partial (REVERSE l)
                   (\x. (bb:real^P->real^Q->real^K) (f x) (g x)) x) <=
            &2 pow (LENGTH l) * M *
            sum(0..LENGTH l) (\m. pde_jetn m f x * pde_jetn (LENGTH l - m) g x)`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `REVERSE(l:num list)`) THEN
    REWRITE_TAC[REVERSE_REVERSE; LENGTH_REVERSE] THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `f:real^N->real^P`; `g:real^N->real^Q`;
                               `x:real^N`]) THEN
    ASM_REWRITE_TAC[]] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[REVERSE; iterated_partial; LENGTH; real_pow; REAL_MUL_LID;
                SUM_SING_NUMSEG; SUB_0; RDT_JETN_0] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `f:real^N->real^P`; `g:real^N->real^Q`;
                       `x:real^N`] THEN
  REWRITE_TAC[REVERSE; ALL_APPEND; ALL; LENGTH] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`bb:real^P->real^Q->real^K`; `f:real^N->real^P`; `g:real^N->real^Q`;
                 `U:real^N->bool`; `REVERSE(t:num list)`; `h:num`; `x:real^N`]
    RDT_BILINEAR_STEP_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`U:real^N->bool`; `partial_derivative h (f:real^N->real^P)`;
                              `g:real^N->real^Q`; `x:real^N`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`U:real^N->bool`; `f:real^N->real^P`;
                                `partial_derivative h (g:real^N->real^Q)`; `x:real^N`]) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX] THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^P`; `g:real^N->real^Q`; `x:real^N`; `LENGTH(t:num list)`]
    RDT_JET_SUM_SHIFT) THEN
  ABBREV_TAC `n = LENGTH(t:num list)` THEN
  ABBREV_TAC `S = sum(0..SUC n) (\m. pde_jetn m (f:real^N->real^P) x *
                                     pde_jetn (SUC n - m) (g:real^N->real^Q) x)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(0..n) (\m. pde_jetn m (partial_derivative h (f:real^N->real^P)) x *
                   pde_jetn (n - m) (g:real^N->real^Q) x) <= S /\
    sum(0..n) (\m. pde_jetn m (f:real^N->real^P) x *
                   pde_jetn (n - m) (partial_derivative h (g:real^N->real^Q)) x) <= S`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `sum(0..n) (\m. pde_jetn (SUC m) (f:real^N->real^P) x *
                                 pde_jetn (n - m) (g:real^N->real^Q) x)`;
      EXISTS_TAC `sum(0..n) (\m. pde_jetn m (f:real^N->real^P) x *
                                 pde_jetn (SUC(n - m)) (g:real^N->real^Q) x)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[PDE_JETN_PARTIAL; PDE_JETN_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[PDE_JETN_PARTIAL; PDE_JETN_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a b e1 e2 e3. norm(a:real^K) <= e1 /\ norm(b:real^K) <= e2 /\ e1 + e2 <= e3
                   ==> norm(a + b) <= e3`) THEN
  MAP_EVERY EXISTS_TAC
   [`&2 pow n * M * sum(0..n) (\m. pde_jetn m (partial_derivative h (f:real^N->real^P)) x *
                                   pde_jetn (n - m) (g:real^N->real^Q) x)`;
    `&2 pow n * M * sum(0..n) (\m. pde_jetn m (f:real^N->real^P) x *
                                   pde_jetn (n - m) (partial_derivative h (g:real^N->real^Q)) x)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= &2 pow n * M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 pow n * M) *
    sum (0..n) (\m. pde_jetn m (partial_derivative h (f:real^N->real^P)) x *
                    pde_jetn (n - m) (g:real^N->real^Q) x) <= (&2 pow n * M) * S /\
    (&2 pow n * M) *
    sum (0..n) (\m. pde_jetn m (f:real^N->real^P) x *
                    pde_jetn (n - m) (partial_derivative h (g:real^N->real^Q)) x) <=
    (&2 pow n * M) * S`
  MP_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC);;

(* The tame form: in each term one factor is of order at most n / 2.        *)

let RDT_JET_SUM_TAME = prove
 (`!(f:real^N->real^P) (g:real^N->real^Q) x n.
        sum(0..n) (\m. pde_jetn m f x * pde_jetn (n - m) g x) <=
        &(n + 1) * (pde_jetn (n DIV 2) f x * pde_jetn n g x +
                    pde_jetn n f x * pde_jetn (n DIV 2) g x)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..n) (\m. pde_jetn (n DIV 2) (f:real^N->real^P) x * pde_jetn n (g:real^N->real^Q) x +
                             pde_jetn n f x * pde_jetn (n DIV 2) g x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `m <= n DIV 2` THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= z ==> x <= y + z`) THEN
      SIMP_TAC[REAL_LE_MUL; PDE_JETN_POS] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[PDE_JETN_POS] THEN CONJ_TAC THEN MATCH_MP_TAC PDE_JETN_MONO THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= z /\ &0 <= y ==> x <= y + z`) THEN
      SIMP_TAC[REAL_LE_MUL; PDE_JETN_POS] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[PDE_JETN_POS] THEN CONJ_TAC THEN MATCH_MP_TAC PDE_JETN_MONO THENL
       [ASM_ARITH_TAC;
        MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ASM_ARITH_TAC]];
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The tame composition bound.  For K smooth on U and Phi smooth on an open  *)
(* W containing K(U), every derivative of order n of Phi o K at x is bounded *)
(* by c_n jet_n(Phi)(K x) (1 + jet_(n/2+1)(K)(x))^n (1 + jet_n(K)(x)):       *)
(* linear in the top-order jet of K (Faa di Bruno; the chain rule and        *)
(* RDT_LEIBNIZ_JET in its tame form RDT_JET_SUM_TAME).                       *)
(* ------------------------------------------------------------------------- *)

let RDT_SMOOTH_COMPOSE = prove
 (`!(Phi:real^M->real^P) (K:real^N->real^M) U W.
        open U /\ open W /\ smooth_map_on U K /\ smooth_map_on W Phi /\ IMAGE K U SUBSET W
        ==> smooth_map_on U (\z. Phi(K z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^N. (Phi:real^M->real^P)((K:real^N->real^M) z)) = Phi o K`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `W:real^M->bool` THEN
  ASM_REWRITE_TAC[]);;

let RDT_BILINEAR_COMPONENT = prove
 (`!j. 1 <= j /\ j <= dimindex(:M)
       ==> bilinear (\(u:real^P) (w:real^M). w$j % u) /\
           !(u:real^P) (w:real^M). norm(w$j % u) <= &1 * norm u * norm w`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[bilinear] THEN CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[] THENL
     [MATCH_MP_TAC LINEAR_VMUL_COMPONENT THEN ASM_REWRITE_TAC[LINEAR_ID];
      MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_ID]];
    REPEAT GEN_TAC THEN REWRITE_TAC[NORM_MUL; REAL_MUL_LID] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; COMPONENT_LE_NORM]]);;

(* The chain rule in components.                                            *)

let RDT_PARTIAL_COMPOSE = prove
 (`!(Phi:real^M->real^P) (K:real^N->real^M) i y.
        K differentiable (at y) /\ Phi differentiable (at (K y))
        ==> partial_derivative i (\z. Phi(K z)) y =
            vsum(1..dimindex(:M))
              (\j. (partial_derivative i K y)$j % partial_derivative j Phi (K y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^N. (Phi:real^M->real^P)((K:real^N->real^M) z)) = Phi o K`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_CHAIN] THEN
  SUBGOAL_THEN `linear(frechet_derivative (Phi:real^M->real^P) (at ((K:real^N->real^M) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; partial_derivative]);;

let RDT_COMPOSE_STEP = prove
 (`!(Phi:real^M->real^P) (K:real^N->real^M) U W l i x.
        open U /\ open W /\ smooth_map_on U K /\ smooth_map_on W Phi /\
        IMAGE K U SUBSET W /\ x IN U
        ==> iterated_partial (APPEND l [i]) (\z. Phi(K z)) x =
            vsum(1..dimindex(:M))
              (\j. iterated_partial l
                     (\z. (partial_derivative i K z)$j % partial_derivative j Phi (K z)) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `iterated_partial l
     (\z. vsum(1..dimindex(:M))
            (\j. (partial_derivative i (K:real^N->real^M) z)$j %
                 partial_derivative j (Phi:real^M->real^P) (K z))) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RDT_PARTIAL_COMPOSE THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `U:real^N->bool`; EXISTS_TAC `W:real^M->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`l:num list`; `U:real^N->bool`;
    `\j z. (partial_derivative i (K:real^N->real^M) z)$j %
           partial_derivative j (Phi:real^M->real^P) (K z)`;
    `1..dimindex(:M)`] PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\(u:real^P) (w:real^M). w$j % u`;
                   `\z. partial_derivative j (Phi:real^M->real^P) ((K:real^N->real^M) z)`;
                   `partial_derivative i (K:real^N->real^M)`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    MP_TAC(SPEC `j:num` (INST_TYPE [`:P`,`:P`; `:M`,`:M`] RDT_BILINEAR_COMPONENT)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[IN_NUMSEG]; SIMP_TAC[]] THEN
    DISCH_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
    MATCH_MP_TAC RDT_SMOOTH_COMPOSE THEN EXISTS_TAC `W:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[]]);;

let RDT_PROD4_LE = prove
 (`!a b c d a' b' c' d'.
        &0 <= a /\ a <= a' /\ &0 <= b /\ b <= b' /\ &0 <= c /\ c <= c' /\
        &0 <= d /\ d <= d'
        ==> a * b * c * d <= a' * b' * c' * d'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let RDT_SUM_ELEMENT_LE = prove
 (`!m k (cc:num->real).
        k <= m /\ (!j. j <= m ==> &0 <= cc j) ==> cc k <= sum(0..m) cc`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{k:num}`; `0..m`; `cc:num->real`] SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[SUM_SING; FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SING_SUBSET; IN_NUMSEG; LE_0; IN_DIFF] THEN ASM_MESON_TAC[]);;

(* Jets of a composition from bounds on its derivatives.                    *)

let RDT_JETN_COMPOSE_IH = prove
 (`!m (cc:num->real).
     (!k. k <= m
          ==> &0 <= cc k /\
              !(Psi:real^M->real^P) (K:real^N->real^M) U W x l.
                 open U /\ open W /\ smooth_map_on U K /\ smooth_map_on W Psi /\
                 IMAGE K U SUBSET W /\ x IN U /\
                 LENGTH l = k /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
                 ==> norm(iterated_partial l (\z. Psi(K z)) x) <=
                     cc k * pde_jetn k Psi (K x) *
                     (&1 + pde_jetn (k DIV 2 + 1) K x) pow k * (&1 + pde_jetn k K x))
     ==> !(Psi:real^M->real^P) (K:real^N->real^M) U W x.
           open U /\ open W /\ smooth_map_on U K /\ smooth_map_on W Psi /\
           IMAGE K U SUBSET W /\ x IN U
           ==> pde_jetn m (\z. Psi(K z)) x <=
               &(CARD(pde_index_lists m (:N))) *
               (sum(0..m) cc * pde_jetn m Psi (K x) *
                (&1 + pde_jetn (m DIV 2 + 1) K x) pow m * (&1 + pde_jetn m K x))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [pde_jetn] THEN MATCH_MP_TAC SUM_BOUND THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[pde_index_lists; IN_ELIM_THM]) THEN
  USE_THEN "ih" (MP_TAC o SPEC `LENGTH(l:num list)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL
    [`Psi:real^M->real^P`; `K:real^N->real^M`; `U:real^N->bool`; `W:real^M->bool`;
     `x:real^N`; `l:num list`])) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC RDT_PROD4_LE THEN
  ASM_SIMP_TAC[PDE_JETN_POS; REAL_POW_LE; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RDT_SUM_ELEMENT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN USE_THEN "ih" (MP_TAC o SPEC `j:num`) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PDE_JETN_MONO THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + pde_jetn (m DIV 2 + 1) (K:real^N->real^M) x) pow (LENGTH(l:num list))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN
      SIMP_TAC[PDE_JETN_POS; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
      MATCH_MP_TAC PDE_JETN_MONO THEN
      MATCH_MP_TAC(ARITH_RULE `a <= b ==> a + 1 <= b + 1`) THEN
      MATCH_MP_TAC DIV_MONO THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[PDE_JETN_POS; REAL_ARITH `&0 <= x ==> &1 <= &1 + x`]];
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
    MATCH_MP_TAC PDE_JETN_MONO THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The tame composition bound RDT_COMPOSE_TAME (strong induction on the      *)
(* order; the step is the chain rule, Leibniz in its tame form, and the      *)
(* bound for the jets of the derivative of the outer map).                   *)
(* ------------------------------------------------------------------------- *)

let RDT_LIST_SNOC = prove
 (`!(l:num list) n. LENGTH l = SUC n ==> ?l' i. l = APPEND l' [i] /\ LENGTH l' = n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `REVERSE(l:num list)` list_CASES) THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_REVERSE] THEN ASM_REWRITE_TAC[NOT_SUC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num` (X_CHOOSE_THEN `t:num list` ASSUME_TAC)) THEN
  SUBGOAL_THEN `LENGTH(t:num list) = n` ASSUME_TAC THENL
   [MP_TAC(AP_TERM `LENGTH:num list->num` (ASSUME `REVERSE(l:num list) = CONS h t`)) THEN
    ASM_REWRITE_TAC[LENGTH_REVERSE; LENGTH; SUC_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`REVERSE(t:num list)`; `h:num`] THEN
  ASM_REWRITE_TAC[LENGTH_REVERSE] THEN
  SUBGOAL_THEN `l = REVERSE(REVERSE(l:num list))` SUBST1_TAC THENL
   [REWRITE_TAC[REVERSE_REVERSE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REVERSE]);;

let RDT_POS_TAC =
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_POS; PDE_JETN_POS; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`];;

let RDT_TAME_COMBINE = prove
 (`!n a b p q c1 s phi L H.
        &0 <= a /\ &0 <= b /\ &0 <= p /\ &0 <= q /\ &0 <= c1 /\ &0 <= s /\ &0 <= phi /\
        &0 <= L /\ &0 <= H /\
        a <= c1 * s * phi * (&1 + L) pow n * (&1 + L) /\ b <= H /\
        p <= c1 * s * phi * (&1 + L) pow n * H /\ q <= L
        ==> a * b + p * q <= &2 * c1 * s * phi * (&1 + L) pow (SUC n) * H`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c1 * s * phi * (&1 + L) pow n` ASSUME_TAC THENL
   [RDT_POS_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a * b <= (c1 * s * phi * (&1 + L) pow n * (&1 + L)) * H` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p * q <= (c1 * s * phi * (&1 + L) pow n * H) * (&1 + L)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN
  MAP_EVERY UNDISCH_TAC [`a * b <= (c1 * s * phi * (&1 + L) pow n * (&1 + L)) * H`;
                         `p * q <= (c1 * s * phi * (&1 + L) pow n * H) * (&1 + L)`] THEN
  REAL_ARITH_TAC);;

(* One term of the step: the chain rule summand in direction j.             *)

let RDT_COMPOSE_TERM = prove
 (`!n' (cc:num->real) (Phi:real^M->real^P) (K:real^N->real^M) U W x l' i j.
     (!k. k <= n'
          ==> &0 <= cc k /\
              !(Psi:real^M->real^P) (K:real^N->real^M) U W x l.
                 open U /\ open W /\ smooth_map_on U K /\ smooth_map_on W Psi /\
                 IMAGE K U SUBSET W /\ x IN U /\
                 LENGTH l = k /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
                 ==> norm(iterated_partial l (\z. Psi(K z)) x) <=
                     cc k * pde_jetn k Psi (K x) *
                     (&1 + pde_jetn (k DIV 2 + 1) K x) pow k * (&1 + pde_jetn k K x)) /\
     open U /\ open W /\ smooth_map_on U K /\ smooth_map_on W Phi /\
     IMAGE K U SUBSET W /\ x IN U /\
     LENGTH l' = n' /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l' /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:M)
     ==> norm(iterated_partial l'
                (\z. (partial_derivative i K z)$j % partial_derivative j Phi (K z)) x) <=
         &2 pow n' * &(n' + 1) *
         (&2 * &(CARD(pde_index_lists n' (:N))) * sum(0..n') cc *
          pde_jetn (SUC n') Phi (K x) *
          (&1 + pde_jetn (SUC n' DIV 2 + 1) K x) pow (SUC n') *
          (&1 + pde_jetn (SUC n') K x))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!k. k <= n' ==> &0 <= (cc:num->real) k` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "ih" (MP_TAC o SPEC `k:num`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U (\z. partial_derivative j (Phi:real^M->real^P) ((K:real^N->real^M) z)) /\
    smooth_map_on U (partial_derivative i (K:real^N->real^M)) /\
    smooth_map_on W (partial_derivative j (Phi:real^M->real^P))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN MATCH_MP_TAC RDT_SMOOTH_COMPOSE THEN
    EXISTS_TAC `W:real^M->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  MP_TAC(SPEC `j:num` (INST_TYPE [`:P`,`:P`; `:M`,`:M`] RDT_BILINEAR_COMPONENT)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\(u:real^P) (w:real^M). w$j % u`; `&1`] RDT_LEIBNIZ_JET) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`l':num list`; `U:real^N->bool`;
    `\z. partial_derivative j (Phi:real^M->real^P) ((K:real^N->real^M) z)`;
    `partial_derivative i (K:real^N->real^M)`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&(n' + 1) *
    (pde_jetn (n' DIV 2) (\z. partial_derivative j (Phi:real^M->real^P) ((K:real^N->real^M) z)) x *
     pde_jetn n' (partial_derivative i (K:real^N->real^M)) x +
     pde_jetn n' (\z. partial_derivative j Phi (K z)) x *
     pde_jetn (n' DIV 2) (partial_derivative i K) x)` THEN
  REWRITE_TAC[RDT_JET_SUM_TAME] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC RDT_TAME_COMBINE THEN
  SIMP_TAC[PDE_JETN_POS; REAL_POS; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* the four jet bounds *)
  SUBGOAL_THEN
   `!m. m <= n'
        ==> pde_jetn m (\z. partial_derivative j (Phi:real^M->real^P) ((K:real^N->real^M) z)) x <=
            &(CARD(pde_index_lists m (:N))) *
            (sum(0..m) cc * pde_jetn m (partial_derivative j Phi) (K x) *
             (&1 + pde_jetn (m DIV 2 + 1) K x) pow m * (&1 + pde_jetn m K x))`
  (LABEL_TAC "fj") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m:num`; `cc:num->real`] (INST_TYPE [`:P`,`:P`] RDT_JETN_COMPOSE_IH)) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "ih" (MP_TAC o SPEC `k:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `W:real^M->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. m <= n'
        ==> &(CARD(pde_index_lists m (:N))) <= &(CARD(pde_index_lists n' (:N))) /\
            sum(0..m) (cc:num->real) <= sum(0..n') cc /\
            pde_jetn m (partial_derivative j (Phi:real^M->real^P)) ((K:real^N->real^M) x) <=
            pde_jetn (SUC n') Phi (K x)`
  (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[PDE_INDEX_LISTS_MONO; PDE_INDEX_LISTS_FINITE];
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REWRITE_TAC[SUBSET; IN_NUMSEG; IN_DIFF] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_jetn (SUC m) (Phi:real^M->real^P) ((K:real^N->real^M) x)` THEN
      ASM_SIMP_TAC[PDE_JETN_PARTIAL] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `n' DIV 2 <= n' /\ n' DIV 2 <= SUC n' DIV 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [REWRITE_TAC[DIV_LE];
                    MATCH_MP_TAC DIV_MONO THEN ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* (i) *)
    USE_THEN "fj" (MP_TAC o SPEC `n' DIV 2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    USE_THEN "mono" (MP_TAC o SPEC `n' DIV 2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[LE_TRANS]; RDT_POS_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC RDT_PROD4_LE THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_POW_LE; PDE_JETN_POS; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[LE_TRANS]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&1 + pde_jetn (SUC n' DIV 2 + 1) (K:real^N->real^M) x) pow (n' DIV 2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN
        SIMP_TAC[PDE_JETN_POS; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
        MATCH_MP_TAC PDE_JETN_MONO THEN
        MP_TAC(SPECL [`n' DIV 2`; `2`] DIV_LE) THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[PDE_JETN_POS; REAL_ARITH `&0 <= x ==> &1 <= &1 + x`]];
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
      MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC];
    (* (ii) *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (SUC n') (K:real^N->real^M) x` THEN
    ASM_SIMP_TAC[PDE_JETN_PARTIAL] THEN REAL_ARITH_TAC;
    (* (iii) *)
    USE_THEN "fj" (MP_TAC o SPEC `n':num`) THEN REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    USE_THEN "mono" (MP_TAC o SPEC `n':num`) THEN REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC RDT_PROD4_LE THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    SIMP_TAC[REAL_POW_LE; PDE_JETN_POS; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[LE_TRANS]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN
      SIMP_TAC[PDE_JETN_POS; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
      MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
      MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC];
    (* (iv) *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (SUC(n' DIV 2)) (K:real^N->real^M) x` THEN
    ASM_SIMP_TAC[PDE_JETN_PARTIAL] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC]);;

let RDT_COMPOSE_TAME = prove
 (`!n. ?c. &0 <= c /\
       !(Phi:real^M->real^P) (K:real^N->real^M) U W x l.
         open U /\ open W /\ smooth_map_on U K /\ smooth_map_on W Phi /\
         IMAGE K U SUBSET W /\ x IN U /\
         LENGTH l = n /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
         ==> norm(iterated_partial l (\z. Phi(K z)) x) <=
             c * pde_jetn n Phi (K x) * (&1 + pde_jetn (n DIV 2 + 1) K x) pow n *
             (&1 + pde_jetn n K x)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ih0") THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_POS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[iterated_partial; real_pow; RDT_JETN_0; REAL_MUL_LID; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REMOVE_THEN "ih0" (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:num->real` (LABEL_TAC "ih")) THEN
  MP_TAC(SPEC `n:num` num_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n':num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `!k. k <= n' ==> &0 <= (cc:num->real) k` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "ih" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum(0..n') (cc:num->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `C1 = &(CARD(pde_index_lists n' (:N)))` THEN
  ABBREV_TAC `S = sum(0..n') (cc:num->real)` THEN
  SUBGOAL_THEN `&0 <= C1` ASSUME_TAC THENL [EXPAND_TAC "C1" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  EXISTS_TAC `&(dimindex(:M)) * &2 pow n' * &(n' + 1) * (&2 * C1 * S)` THEN
  CONJ_TAC THENL [RDT_POS_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`Phi:real^M->real^P`; `K:real^N->real^M`; `U:real^N->bool`;
                       `W:real^M->bool`; `x:real^N`; `l:num list`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l':num list` (X_CHOOSE_THEN `i:num`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) o MATCH_MP RDT_LIST_SNOC) THEN
  UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:N)) (APPEND l' [i:num])` THEN
  REWRITE_TAC[ALL_APPEND; ALL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Phi:real^M->real^P`; `K:real^N->real^M`; `U:real^N->bool`; `W:real^M->bool`;
                 `l':num list`; `i:num`; `x:real^N`] RDT_COMPOSE_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  (* the abbreviations of the final bound *)
  ABBREV_TAC `phi = pde_jetn (SUC n') (Phi:real^M->real^P) ((K:real^N->real^M) x)` THEN
  ABBREV_TAC `L = pde_jetn (SUC n' DIV 2 + 1) (K:real^N->real^M) x` THEN
  ABBREV_TAC `H = &1 + pde_jetn (SUC n') (K:real^N->real^M) x` THEN
  SUBGOAL_THEN `&0 <= phi /\ &0 <= L /\ &0 <= H` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["phi"; "L"; "H"] THEN
    SIMP_TAC[PDE_JETN_POS; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`];
    ALL_TAC] THEN
  (* the bound of one term *)
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:M)
        ==> norm(iterated_partial l'
                   (\z. (partial_derivative i (K:real^N->real^M) z)$j %
                        partial_derivative j (Phi:real^M->real^P) (K z)) x) <=
            &2 pow n' * &(n' + 1) * (&2 * C1 * S * phi * (&1 + L) pow (SUC n') * H)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`n':num`; `cc:num->real`; `Phi:real^M->real^P`; `K:real^N->real^M`;
                   `U:real^N->bool`; `W:real^M->bool`; `x:real^N`; `l':num list`;
                   `i:num`; `j:num`] RDT_COMPOSE_TERM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      USE_THEN "ih" (MP_TAC o SPEC `k:num`) THEN
      (ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN SIMP_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:M))
               (\j. norm(iterated_partial l'
                      (\z. (partial_derivative i (K:real^N->real^M) z)$j %
                           partial_derivative j (Phi:real^M->real^P) (K z)) x))` THEN
  REWRITE_TAC[VSUM_NORM_LE] THEN
  SIMP_TAC[VSUM_NORM; FINITE_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(1..dimindex(:M))) *
              (&2 pow n' * &(n' + 1) * (&2 * C1 * S * phi * (&1 + L) pow (SUC n') * H))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_BOUND THEN ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG]; ALL_TAC] THEN
  REWRITE_TAC[CARD_NUMSEG_1] THEN MAP_EVERY EXPAND_TAC ["phi"; "L"; "H"] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integrals over an open chart image U of continuous functions              *)
(* vanishing off a compact K inside U: integrability, linearity, order, and  *)
(* integration by parts (WAN_NT_INTEGRAL_PARTIAL); the chart Sobolev norms. *)
(* ------------------------------------------------------------------------- *)

let rdt_int = new_definition
 `rdt_int (U:real^N->bool) (f:real^N->real) = drop(integral U (\y. lift(f y)))`;;

let rdt_cs = new_definition
 `rdt_cs (U:real^N->bool) (K:real^N->bool) (f:real^N->real) <=>
    (\y. lift(f y)) continuous_on U /\ !y. y IN U /\ ~(y IN K) ==> f y = &0`;;

let RDT_CS_INTEGRABLE = prove
 (`!U K (f:real^N->real).
     open U /\ compact K /\ K SUBSET U /\ rdt_cs U K f
     ==> (\y. lift(f y)) integrable_on U`,
  REWRITE_TAC[rdt_cs] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. lift((f:real^N->real) y)) integrable_on K` MP_TAC THENL
   [MP_TAC(ISPECL [`\y. lift((f:real^N->real) y)`; `K:real^N->bool`]
      PDM_INTEGRABLE_CONTINUOUS_COMPACT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[integrable_on] THEN DISCH_THEN(X_CHOOSE_TAC `i:real^1`) THEN
  EXISTS_TAC `i:real^1` THEN
  MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
  EXISTS_TAC `\y. if y IN K then lift((f:real^N->real) y) else vec 0` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[LIFT_NUM];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_ON_SUPERSET THEN EXISTS_TAC `K:real^N->bool` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
  EXISTS_TAC `\y. lift((f:real^N->real) y)` THEN ASM_SIMP_TAC[]);;

let RDT_CS_ADD = prove
 (`!U K (f:real^N->real) g. rdt_cs U K f /\ rdt_cs U K g ==> rdt_cs U K (\y. f y + g y)`,
  REWRITE_TAC[rdt_cs; LIFT_ADD] THEN SIMP_TAC[CONTINUOUS_ON_ADD; REAL_ADD_LID]);;

let RDT_CS_SUB = prove
 (`!U K (f:real^N->real) g. rdt_cs U K f /\ rdt_cs U K g ==> rdt_cs U K (\y. f y - g y)`,
  REWRITE_TAC[rdt_cs; LIFT_SUB] THEN SIMP_TAC[CONTINUOUS_ON_SUB; REAL_SUB_REFL]);;

let RDT_CS_CMUL = prove
 (`!U K (f:real^N->real) c. rdt_cs U K f ==> rdt_cs U K (\y. c * f y)`,
  REWRITE_TAC[rdt_cs; LIFT_CMUL] THEN SIMP_TAC[CONTINUOUS_ON_CMUL; REAL_MUL_RZERO]);;

let RDT_INT_ADD = prove
 (`!U K (f:real^N->real) g.
     open U /\ compact K /\ K SUBSET U /\ rdt_cs U K f /\ rdt_cs U K g
     ==> rdt_int U (\y. f y + g y) = rdt_int U f + rdt_int U g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_int; LIFT_ADD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_ADD o rand o lhand o snd) THEN
  ANTS_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC RDT_CS_INTEGRABLE THEN ASM_MESON_TAC[];
                  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_ADD]]);;

let RDT_INT_SUB = prove
 (`!U K (f:real^N->real) g.
     open U /\ compact K /\ K SUBSET U /\ rdt_cs U K f /\ rdt_cs U K g
     ==> rdt_int U (\y. f y - g y) = rdt_int U f - rdt_int U g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_int; LIFT_SUB] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_SUB o rand o lhand o snd) THEN
  ANTS_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC RDT_CS_INTEGRABLE THEN ASM_MESON_TAC[];
                  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_SUB]]);;

let RDT_INT_CMUL = prove
 (`!U K (f:real^N->real) c.
     open U /\ compact K /\ K SUBSET U /\ rdt_cs U K f
     ==> rdt_int U (\y. c * f y) = c * rdt_int U f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_int; LIFT_CMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_CMUL o rand o lhand o snd) THEN
  ANTS_TAC THENL [MATCH_MP_TAC RDT_CS_INTEGRABLE THEN ASM_MESON_TAC[];
                  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_CMUL]]);;

let RDT_INT_LE = prove
 (`!U K (f:real^N->real) g.
     open U /\ compact K /\ K SUBSET U /\ rdt_cs U K f /\ rdt_cs U K g /\
     (!y. y IN U ==> f y <= g y)
     ==> rdt_int U f <= rdt_int U g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_int] THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[LIFT_DROP] THEN CONJ_TAC THEN MATCH_MP_TAC RDT_CS_INTEGRABLE THEN
  ASM_MESON_TAC[]);;

let RDT_INT_POS = prove
 (`!U K (f:real^N->real).
     open U /\ compact K /\ K SUBSET U /\ rdt_cs U K f /\ (!y. y IN U ==> &0 <= f y)
     ==> &0 <= rdt_int U f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_int] THEN
  MP_TAC(ISPECL [`\y:real^N. vec 0:real^1`; `\y. lift((f:real^N->real) y)`; `U:real^N->bool`]
    INTEGRAL_DROP_LE) THEN
  REWRITE_TAC[INTEGRAL_0; DROP_VEC; LIFT_DROP; INTEGRABLE_0] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RDT_CS_INTEGRABLE THEN ASM_MESON_TAC[]);;

(* Smooth maps vanishing off K, and their dot products, have support in K. *)

let RDT_CS_SMOOTH_DOT = prove
 (`!U K (a:real^N->real^Q) b.
     open U /\ compact K /\ smooth_map_on U a /\ smooth_map_on U b /\
     (!y. y IN U /\ ~(y IN K) ==> a y = vec 0)
     ==> rdt_cs U K (\y. a y dot b y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_cs] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `\x y. lift((x:real^Q) dot y)`; `a:real^N->real^Q`;
                   `b:real^N->real^Q`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_REWRITE_TAC[BILINEAR_DOT] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    REWRITE_TAC[];
    ASM_SIMP_TAC[DOT_LZERO]]);;

let RDT_PARTIAL_CS = prove
 (`!U K (a:real^N->real^Q) l.
     open U /\ compact K /\ (!y. y IN U /\ ~(y IN K) ==> a y = vec 0)
     ==> !y. y IN U /\ ~(y IN K) ==> iterated_partial l a y = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDM_PARTIAL_ZERO_OFF THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `K:real^N->bool`] THEN ASM_REWRITE_TAC[]);;

(* Integration by parts for a map vanishing off K.                          *)

let RDT_INT_IBP = prove
 (`!U K (a:real^N->real^Q) b k.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U a /\ smooth_map_on U b /\
     (!y. y IN U /\ ~(y IN K) ==> a y = vec 0)
     ==> rdt_int U (\y. partial_derivative k a y dot b y) =
         --(rdt_int U (\y. a y dot partial_derivative k b y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN U /\ ~(y IN K) ==> partial_derivative k (a:real^N->real^Q) y = vec 0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `a:real^N->real^Q`; `[k:num]`]
      RDT_PARTIAL_CS) THEN
    ASM_REWRITE_TAC[iterated_partial];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (partial_derivative k (a:real^N->real^Q)) /\
                smooth_map_on U (partial_derivative k (b:real^N->real^Q))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `rdt_cs U K (\y. partial_derivative k (a:real^N->real^Q) y dot (b:real^N->real^Q) y) /\
    rdt_cs U K (\y. a y dot partial_derivative k b y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN U
        ==> ((\y. lift((a:real^N->real^Q) y dot (b:real^N->real^Q) y)) has_derivative
             (\h. lift(frechet_derivative a (at y) h dot b y +
                       a y dot frechet_derivative b (at y) h))) (at y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x y. lift((x:real^Q) dot y)`; `a:real^N->real^Q`; `b:real^N->real^Q`;
                   `frechet_derivative (a:real^N->real^Q) (at y)`;
                   `frechet_derivative (b:real^N->real^Q) (at y)`; `y:real^N`]
      HAS_DERIVATIVE_BILINEAR_AT) THEN
    REWRITE_TAC[BILINEAR_DOT] THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[LIFT_ADD] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. lift((a:real^N->real^Q) y dot (b:real^N->real^Q) y)`;
                 `\y h. lift(frechet_derivative (a:real^N->real^Q) (at y) h dot b y +
                             a y dot frechet_derivative (b:real^N->real^Q) (at y) h)`;
                 `U:real^N->bool`; `K:real^N->bool`; `k:num`] WAN_NT_INTEGRAL_PARTIAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[] THEN REWRITE_TAC[GSYM partial_derivative; LIFT_ADD] THEN
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      UNDISCH_TAC `rdt_cs U K (\y. partial_derivative k (a:real^N->real^Q) y dot
                                   (b:real^N->real^Q) y)` THEN
      UNDISCH_TAC `rdt_cs U K (\y. (a:real^N->real^Q) y dot partial_derivative k
                                   (b:real^N->real^Q) y)` THEN
      SIMP_TAC[rdt_cs];
      REWRITE_TAC[] THEN ASM_SIMP_TAC[DOT_LZERO; LIFT_NUM]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM partial_derivative; LIFT_ADD] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  MP_TAC(ISPECL [`\y. lift(partial_derivative k (a:real^N->real^Q) y dot (b:real^N->real^Q) y)`;
                 `\y. lift((a:real^N->real^Q) y dot partial_derivative k (b:real^N->real^Q) y)`;
                 `U:real^N->bool`] INTEGRAL_ADD) THEN
  ANTS_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC RDT_CS_INTEGRABLE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rdt_int] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[DROP_ADD; DROP_VEC] THEN
  REAL_ARITH_TAC);;

(* Chart Sobolev norms (squared) of maps on U.                               *)

let rdt_hs = new_definition
 `rdt_hs (U:real^N->bool) (s:num) (u:real^N->real^Q) =
    sum (pde_index_lists s (:N))
        (\l. rdt_int U (\y. norm(iterated_partial l u y) pow 2))`;;

(* ------------------------------------------------------------------------- *)
(* The tame commutator [d^l, bb(f, .)] g: all Leibniz terms                  *)
(* with at least one derivative on f.                                        *)
(* ------------------------------------------------------------------------- *)

let RDT_COMMUTATOR_JET = prove
 (`!(bb:real^P->real^Q->real^K) M.
     bilinear bb /\ (!x y. norm(bb x y) <= M * norm x * norm y) /\ &0 <= M
     ==> !l (U:real^N->bool) f g x.
           open U /\ smooth_map_on U f /\ smooth_map_on U g /\ x IN U /\
           ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
           ==> norm(iterated_partial l (\x. bb (f x) (g x)) x - bb (f x) (iterated_partial l g x)) <=
               &2 pow (LENGTH l) * M *
               sum(1..LENGTH l) (\m. pde_jetn m f x * pde_jetn (LENGTH l - m) g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!l (U:real^N->bool) (f:real^N->real^P) (g:real^N->real^Q) x.
        open U /\ smooth_map_on U f /\ smooth_map_on U g /\ x IN U /\
        ALL (\i. 1 <= i /\ i <= dimindex(:N)) (REVERSE l)
        ==> norm(iterated_partial (REVERSE l) (\x. (bb:real^P->real^Q->real^K) (f x) (g x)) x -
                 bb (f x) (iterated_partial (REVERSE l) g x)) <=
            &2 pow (LENGTH l) * M *
            sum(1..LENGTH l) (\m. pde_jetn m f x * pde_jetn (LENGTH l - m) g x)`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `REVERSE(l:num list)`) THEN
    REWRITE_TAC[REVERSE_REVERSE; LENGTH_REVERSE] THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `f:real^N->real^P`; `g:real^N->real^Q`;
                               `x:real^N`]) THEN
    ASM_REWRITE_TAC[]] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[REVERSE; iterated_partial; LENGTH; VECTOR_SUB_REFL; NORM_0] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `f:real^N->real^P`; `g:real^N->real^Q`;
                       `x:real^N`] THEN
  REWRITE_TAC[REVERSE; ALL_APPEND; ALL; LENGTH] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`bb:real^P->real^Q->real^K`; `f:real^N->real^P`; `g:real^N->real^Q`;
                 `U:real^N->bool`; `REVERSE(t:num list)`; `h:num`; `x:real^N`]
    RDT_BILINEAR_STEP_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`U:real^N->bool`; `f:real^N->real^P`;
                                `partial_derivative h (g:real^N->real^Q)`; `x:real^N`]) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`bb:real^P->real^Q->real^K`; `M:real`] RDT_LEIBNIZ_JET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`REVERSE(t:num list)`; `U:real^N->bool`;
                             `partial_derivative h (f:real^N->real^P)`; `g:real^N->real^Q`;
                             `x:real^N`]) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX; LENGTH_REVERSE] THEN DISCH_TAC THEN
  ABBREV_TAC `n = LENGTH(t:num list)` THEN
  ABBREV_TAC `S = sum(1..SUC n) (\m. pde_jetn m (f:real^N->real^P) x *
                                     pde_jetn (SUC n - m) (g:real^N->real^Q) x)` THEN
  SUBGOAL_THEN
   `sum(0..n) (\m. pde_jetn m (partial_derivative h (f:real^N->real^P)) x *
                   pde_jetn (n - m) (g:real^N->real^Q) x) <= S /\
    sum(1..n) (\m. pde_jetn m (f:real^N->real^P) x *
                   pde_jetn (n - m) (partial_derivative h (g:real^N->real^Q)) x) <= S`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..n) (\m. pde_jetn (SUC m) (f:real^N->real^P) x *
                                 pde_jetn (n - m) (g:real^N->real^Q) x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[PDE_JETN_PARTIAL; PDE_JETN_POS];
        EXPAND_TAC "S" THEN
        MP_TAC(ISPECL [`1`; `\m. pde_jetn m (f:real^N->real^P) x *
                                 pde_jetn (SUC n - m) (g:real^N->real^Q) x`;
                       `0`; `n:num`] SUM_OFFSET) THEN
        REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `0 + 1 = 1`; ARITH_RULE `n + 1 = SUC n`] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD1] THEN
        REWRITE_TAC[ARITH_RULE `(n + 1) - (i + 1) = n - i`; REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(1..n) (\m. pde_jetn m (f:real^N->real^P) x *
                                 pde_jetn (SUC(n - m)) (g:real^N->real^Q) x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[PDE_JETN_PARTIAL; PDE_JETN_POS];
        EXPAND_TAC "S" THEN SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
        MATCH_MP_TAC(REAL_ARITH `a = b /\ &0 <= c ==> a <= b + c`) THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
          AP_TERM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PDE_JETN_POS]]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a b c e1 e2 e3. norm(a:real^K) <= e1 /\ norm(b - c) <= e2 /\ e1 + e2 <= e3
                     ==> norm((a + b) - c) <= e3`) THEN
  MAP_EVERY EXISTS_TAC
   [`&2 pow n * M * sum(0..n) (\m. pde_jetn m (partial_derivative h (f:real^N->real^P)) x *
                                   pde_jetn (n - m) (g:real^N->real^Q) x)`;
    `&2 pow n * M * sum(1..n) (\m. pde_jetn m (f:real^N->real^P) x *
                                   pde_jetn (n - m) (partial_derivative h (g:real^N->real^Q)) x)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= &2 pow n * M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 pow n * M) *
    sum (0..n) (\m. pde_jetn m (partial_derivative h (f:real^N->real^P)) x *
                    pde_jetn (n - m) (g:real^N->real^Q) x) <= (&2 pow n * M) * S /\
    (&2 pow n * M) *
    sum (1..n) (\m. pde_jetn m (f:real^N->real^P) x *
                    pde_jetn (n - m) (partial_derivative h (g:real^N->real^Q)) x) <=
    (&2 pow n * M) * S`
  MP_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC);;

(* The tame split of the commutator sum (m >= 1).                           *)

let RDT_COMM_SUM_TAME = prove
 (`!(f:real^N->real^P) (g:real^N->real^Q) x n.
        sum(1..n) (\m. pde_jetn m f x * pde_jetn (n - m) g x) <=
        &n * (pde_jetn (n DIV 2 + 1) f x * pde_jetn (n - 1) g x +
              pde_jetn n f x * pde_jetn (n DIV 2) g x)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..n) (\m. pde_jetn (n DIV 2 + 1) (f:real^N->real^P) x *
                             pde_jetn (n - 1) (g:real^N->real^Q) x +
                             pde_jetn n f x * pde_jetn (n DIV 2) g x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `m <= n DIV 2 + 1` THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= z ==> x <= y + z`) THEN
      SIMP_TAC[REAL_LE_MUL; PDE_JETN_POS] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[PDE_JETN_POS] THEN CONJ_TAC THEN MATCH_MP_TAC PDE_JETN_MONO THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= z /\ &0 <= y ==> x <= y + z`) THEN
      SIMP_TAC[REAL_LE_MUL; PDE_JETN_POS] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[PDE_JETN_POS] THEN CONJ_TAC THEN MATCH_MP_TAC PDE_JETN_MONO THENL
       [ASM_ARITH_TAC;
        MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ASM_ARITH_TAC]];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]);;

(* Jets of a derivative of u.                                                *)

let RDT_JETN_ITERATED = prove
 (`!m (g:real^N->real^Q) l x.
        ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
        ==> pde_jetn m (iterated_partial l g) x <= pde_jetn (m + LENGTH l) g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  REWRITE_TAC[GSYM ITERATED_PARTIAL_APPEND] THEN
  MP_TAC(ISPECL [`\l':num list. APPEND l' l`;
                 `\l':num list. norm(iterated_partial l' (g:real^N->real^Q) x)`;
                 `pde_index_lists m (:N)`] SUM_IMAGE) THEN
  ANTS_TAC THENL [SIMP_TAC[APPEND_RCANCEL]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE; NORM_POS_LE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; pde_index_lists; IN_ELIM_THM;
              LENGTH_APPEND; ALL_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* The tame product bound: the commutator of d^l with a coefficient c in a   *)
(* product with a derivative of order at most 2 of u.                        *)

let RDT_TAME_PRODUCT = prove
 (`!(bb:real^P->real^Q->real^K) M.
     bilinear bb /\ (!x y. norm(bb x y) <= M * norm x * norm y) /\ &0 <= M
     ==> !l (U:real^N->bool) (c:real^N->real^P) (u:real^N->real^Q) g x.
           open U /\ smooth_map_on U c /\ smooth_map_on U u /\ x IN U /\
           ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
           ALL (\i. 1 <= i /\ i <= dimindex(:N)) g /\ LENGTH g <= 2
           ==> norm(iterated_partial l (\x. bb (c x) (iterated_partial g u x)) x -
                    bb (c x) (iterated_partial l (iterated_partial g u) x)) <=
               &2 pow (LENGTH l) * M * &(LENGTH l) *
               (pde_jetn (LENGTH l DIV 2 + 1) c x * pde_jetn (LENGTH l + 1) u x +
                pde_jetn (LENGTH l) c x * pde_jetn (LENGTH l DIV 2 + 2) u x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RDT_COMMUTATOR_JET) THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num list`; `U:real^N->bool`; `c:real^N->real^P`;
                             `iterated_partial g (u:real^N->real^Q)`; `x:real^N`]) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  ABBREV_TAC `n = LENGTH(l:num list)` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; REAL_MUL_RZERO; REAL_MUL_LZERO;
                    REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n * (pde_jetn (n DIV 2 + 1) (c:real^N->real^P) x *
                    pde_jetn (n - 1) (iterated_partial g (u:real^N->real^Q)) x +
                    pde_jetn n c x * pde_jetn (n DIV 2) (iterated_partial g u) x)` THEN
  REWRITE_TAC[RDT_COMM_SUM_TAME] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[PDE_JETN_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `pde_jetn ((n - 1) + LENGTH(g:num list)) (u:real^N->real^Q) x`;
    EXISTS_TAC `pde_jetn (n DIV 2 + LENGTH(g:num list)) (u:real^N->real^Q) x`] THEN
  ASM_SIMP_TAC[RDT_JETN_ITERATED] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* D^l of the local second-order operator pde_lop0 A B C u is                *)
(* the principal part sum A_ij d_i d_j (d^l u) plus a remainder bounded by   *)
(* (low jets of the coefficients) jet_(n+1) u + (jet_n of the coefficients)  *)
(* jet_(n/2+2) u.                                                            *)
(* ------------------------------------------------------------------------- *)

let RDT_JETN_ENTRY = prove
 (`!m U (A:real^N->real^M^M) i j x.
     open U /\ smooth_map_on U (\x. vectorize(A x)) /\ x IN U
     ==> pde_jetn m (\x. lift(A x$i$j)) x <= pde_jetn m (\x. vectorize(A x)) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `\v:real^(M,M)finite_prod. lift((matrify v:real^M^M)$i$j)`;
                 `\x. (vectorize:real^M^M->real^(M,M)finite_prod) ((A:real^N->real^M^M) x)`;
                 `U:real^N->bool`; `x:real^N`] PDE_ITERATED_PARTIAL_LINEAR_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL] THEN
    SIMP_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT; LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIFY_VECTORIZE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NORM_LIFT; PDE_MATRIFY_ENTRY_LE]);;

(* Commuting d^l with d_i d_j on an open set.                               *)

let RDT_COMMUTE2 = prove
 (`!U (u:real^N->real^Q) l i j x.
     open U /\ smooth_map_on U u /\ x IN U /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> iterated_partial l (partial_derivative i (partial_derivative j u)) x =
         partial_derivative i (partial_derivative j (iterated_partial l u)) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `partial_derivative j (u:real^N->real^Q)`; `i:num`]
    TEXT_PARTIAL_COMMUTE_ITERATED) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`[i:num]`; `U:real^N->bool`;
                 `iterated_partial l (partial_derivative j (u:real^N->real^Q))`;
                 `partial_derivative j (iterated_partial l (u:real^N->real^Q))`; `x:real^N`]
    TEXT_ITERATED_PARTIAL_LOCAL_AT) THEN
  REWRITE_TAC[iterated_partial] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `u:real^N->real^Q`; `j:num`]
    TEXT_PARTIAL_COMMUTE_ITERATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_SIMP_TAC[]);;

(* The three kinds of terms.                                                 *)

let RDT_SMOOTH_ENTRY = prove
 (`!U (A:real^N->real^M^M) i j.
     open U /\ smooth_map_on U (\x. vectorize(A x))
     ==> smooth_map_on U (\x. lift(A x$i$j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^N. lift((A:real^N->real^M^M) x$i$j)) =
    (\v:real^(M,M)finite_prod. lift((matrify v:real^M^M)$i$j)) o (\x. vectorize(A x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL] THEN
  SIMP_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT; LIFT_ADD; LIFT_CMUL]);;

let RDT_LOP0_TERM_A = prove
 (`!l U (A:real^N->real^N^N) (u:real^N->real^Q) i j x.
     open U /\ smooth_map_on U (\x. vectorize(A x)) /\ smooth_map_on U u /\ x IN U /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> norm(iterated_partial l
                (\x. A x$i$j % partial_derivative i (partial_derivative j u) x) x -
              A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l u)) x) <=
         &2 pow (LENGTH l) * &(LENGTH l + 1) *
         (pde_jetn (LENGTH l DIV 2 + 1) (\x. vectorize(A x)) x * pde_jetn (LENGTH l + 1) u x +
          pde_jetn (LENGTH l) (\x. vectorize(A x)) x * pde_jetn (LENGTH l DIV 2 + 2) u x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on U (\x. lift((A:real^N->real^N^N) x$i$j))` ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_SMOOTH_ENTRY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\(a:real^1) (w:real^Q). drop a % w`; `&1`] RDT_TAME_PRODUCT) THEN
  REWRITE_TAC[BILINEAR_DROP_MUL; REAL_POS; NORM_MUL; REAL_MUL_LID] THEN
  ANTS_TAC THENL [REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num list`; `U:real^N->bool`;
                             `\x. lift((A:real^N->real^N^N) x$i$j)`; `u:real^N->real^Q`;
                             `[i:num; j:num]`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[ALL; LENGTH; ARITH_RULE `SUC(SUC 0) <= 2`; LIFT_DROP] THEN
  REWRITE_TAC[iterated_partial] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `u:real^N->real^Q`; `l:num list`; `i:num`; `j:num`;
                 `x:real^N`] RDT_COMMUTE2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[PDE_JETN_POS];
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[PDE_JETN_POS] THEN MATCH_MP_TAC RDT_JETN_ENTRY THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let RDT_NORM_LE_JETN = prove
 (`!m (u:real^N->real^Q) l x.
     LENGTH l <= m /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> norm(iterated_partial l u x) <= pde_jetn m u x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  MP_TAC(ISPECL [`{l:num list}`; `pde_index_lists m (:N)`;
                 `\l. norm(iterated_partial l (u:real^N->real^Q) x)`] SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[SUM_SING; PDE_INDEX_LISTS_FINITE; NORM_POS_LE; SING_SUBSET] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM]);;

let RDT_LOP0_TERM_BC = prove
 (`!l U (c:real^N->real^Q^Q) (u:real^N->real^Q) g x.
     open U /\ smooth_map_on U (\x. vectorize(c x)) /\ smooth_map_on U u /\ x IN U /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) g /\ LENGTH g <= 1
     ==> norm(iterated_partial l (\x. c x ** iterated_partial g u x) x) <=
         &2 pow (LENGTH l) * &(LENGTH l + 1) *
         (pde_jetn (LENGTH l DIV 2 + 1) (\x. vectorize(c x)) x * pde_jetn (LENGTH l + 1) u x +
          pde_jetn (LENGTH l) (\x. vectorize(c x)) x * pde_jetn (LENGTH l DIV 2 + 2) u x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(m:real^(Q,Q)finite_prod) (w:real^Q). matrify m ** w`; `&1`]
    RDT_TAME_PRODUCT) THEN
  REWRITE_TAC[BILINEAR_MATRIX_VECTOR_MUL; REAL_POS; REAL_MUL_LID; PDE_MATRIFY_MUL_NORM] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num list`; `U:real^N->bool`;
                             `\x. (vectorize:real^Q^Q->real^(Q,Q)finite_prod) ((c:real^N->real^Q^Q) x)`;
                             `u:real^N->real^Q`; `g:num list`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[MATRIFY_VECTORIZE] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `n = LENGTH(l:num list)` THEN
  ABBREV_TAC `X = pde_jetn (n DIV 2 + 1) (\x. (vectorize:real^Q^Q->real^(Q,Q)finite_prod)
                                                ((c:real^N->real^Q^Q) x)) x *
                  pde_jetn (n + 1) (u:real^N->real^Q) x +
                  pde_jetn n (\x. vectorize(c x)) x * pde_jetn (n DIV 2 + 2) u x` THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PDE_JETN_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((c:real^N->real^Q^Q) x ** iterated_partial l (iterated_partial g (u:real^N->real^Q)) x)
    <= X`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((vectorize:real^Q^Q->real^(Q,Q)finite_prod) ((c:real^N->real^Q^Q) x)) *
                norm(iterated_partial l (iterated_partial g (u:real^N->real^Q)) x)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`(vectorize:real^Q^Q->real^(Q,Q)finite_prod) ((c:real^N->real^Q^Q) x)`;
                     `iterated_partial l (iterated_partial g (u:real^N->real^Q)) x`]
        PDE_MATRIFY_MUL_NORM) THEN
      REWRITE_TAC[MATRIFY_VECTORIZE];
      ALL_TAC] THEN
    EXPAND_TAC "X" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= z ==> x <= y + z`) THEN
    SIMP_TAC[REAL_LE_MUL; PDE_JETN_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_jetn 0 (\x. (vectorize:real^Q^Q->real^(Q,Q)finite_prod)
                                  ((c:real^N->real^Q^Q) x)) x` THEN
      CONJ_TAC THENL [REWRITE_TAC[RDT_JETN_0; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC;
      REWRITE_TAC[GSYM ITERATED_PARTIAL_APPEND] THEN MATCH_MP_TAC RDT_NORM_LE_JETN THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; ALL_APPEND] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a b e1 e2 e3. norm(a - b:real^Q) <= e1 /\ norm b <= e2 /\ e1 + e2 <= e3
                   ==> norm a <= e3`) THEN
  MAP_EVERY EXISTS_TAC [`(c:real^N->real^Q^Q) x **
                         iterated_partial l (iterated_partial g (u:real^N->real^Q)) x`;
                        `&2 pow n * &n * X`;
                        `norm((c:real^N->real^Q^Q) x **
                              iterated_partial l (iterated_partial g (u:real^N->real^Q)) x)`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow n * &n * X + X` THEN
  ASM_SIMP_TAC[REAL_LE_LADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB; REAL_MUL_ASSOC;
              REAL_MUL_RID] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> c + a <= c + b`) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC);;

(* Smoothness of the pieces of pde_lop0.                                     *)

let RDT_LOP0_PIECES_SMOOTH = prove
 (`!U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C:real^N->real^Q^Q) (u:real^N->real^Q).
     open U /\ smooth_map_on U (\x. vectorize(A x)) /\
     (!i. smooth_map_on U (\x. vectorize(B x i))) /\ smooth_map_on U (\x. vectorize(C x)) /\
     smooth_map_on U u
     ==> (!i j. smooth_map_on U (\x. A x$i$j % partial_derivative i (partial_derivative j u) x)) /\
         (!i. smooth_map_on U (\x. B x i ** partial_derivative i u x)) /\
         smooth_map_on U (\x. C x ** u x) /\
         smooth_map_on U (\x. vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                            (\j. A x$i$j % partial_derivative i (partial_derivative j u) x))) /\
         smooth_map_on U (\x. vsum(1..dimindex(:N)) (\i. B x i ** partial_derivative i u x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i j. smooth_map_on U (\x. (A:real^N->real^N^N) x$i$j %
                                partial_derivative i (partial_derivative j (u:real^N->real^Q)) x)) /\
    (!i. smooth_map_on U (\x. (B:real^N->num->real^Q^Q) x i ** partial_derivative i u x)) /\
    smooth_map_on U (\x. (C:real^N->real^Q^Q) x ** u x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `\(a:real^1) (w:real^Q). drop a % w`;
                     `\x. lift((A:real^N->real^N^N) x$i$j)`;
                     `partial_derivative i (partial_derivative j (u:real^N->real^Q))`]
        SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[BILINEAR_DROP_MUL; LIFT_DROP; RDT_SMOOTH_ENTRY;
                   SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
      MP_TAC(ISPECL [`U:real^N->bool`; `\(m:real^(Q,Q)finite_prod) (w:real^Q). matrify m ** w`;
                     `\x. (vectorize:real^Q^Q->real^(Q,Q)finite_prod)
                          ((B:real^N->num->real^Q^Q) x i)`;
                     `partial_derivative i (u:real^N->real^Q)`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[BILINEAR_MATRIX_VECTOR_MUL; MATRIFY_VECTORIZE;
                   SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
      MP_TAC(ISPECL [`U:real^N->bool`; `\(m:real^(Q,Q)finite_prod) (w:real^Q). matrify m ** w`;
                     `\x. (vectorize:real^Q^Q->real^(Q,Q)finite_prod) ((C:real^N->real^Q^Q) x)`;
                     `u:real^N->real^Q`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[BILINEAR_MATRIX_VECTOR_MUL; MATRIFY_VECTORIZE; ETA_AX]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN TRY(MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX]);;

(* d^l of pde_lop0: principal part plus a tame remainder.                    *)

let RDT_LOP0_COMM_BOUND = prove
 (`!l U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C:real^N->real^Q^Q) (u:real^N->real^Q) x.
     open U /\ smooth_map_on U (\x. vectorize(A x)) /\
     (!i. smooth_map_on U (\x. vectorize(B x i))) /\ smooth_map_on U (\x. vectorize(C x)) /\
     smooth_map_on U u /\ x IN U /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> norm(iterated_partial l (pde_lop0 A B C u) x -
              vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                (\j. A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l u)) x))) <=
         &(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) *
         (&2 pow (LENGTH l) * &(LENGTH l + 1) *
          ((pde_jetn (LENGTH l DIV 2 + 1) (\x. vectorize(A x)) x +
            sum(1..dimindex(:N)) (\i. pde_jetn (LENGTH l DIV 2 + 1) (\x. vectorize(B x i)) x) +
            pde_jetn (LENGTH l DIV 2 + 1) (\x. vectorize(C x)) x) * pde_jetn (LENGTH l + 1) u x +
           (pde_jetn (LENGTH l) (\x. vectorize(A x)) x +
            sum(1..dimindex(:N)) (\i. pde_jetn (LENGTH l) (\x. vectorize(B x i)) x) +
            pde_jetn (LENGTH l) (\x. vectorize(C x)) x) * pde_jetn (LENGTH l DIV 2 + 2) u x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `A:real^N->real^N^N`; `B:real^N->num->real^Q^Q`;
                 `C:real^N->real^Q^Q`; `u:real^N->real^Q`] RDT_LOP0_PIECES_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `n = LENGTH(l:num list)` THEN
  ABBREV_TAC
   `T0 = (pde_jetn (n DIV 2 + 1) (\x. vectorize((A:real^N->real^N^N) x)) x +
          sum(1..dimindex(:N)) (\i. pde_jetn (n DIV 2 + 1)
                                     (\x. vectorize((B:real^N->num->real^Q^Q) x i)) x) +
          pde_jetn (n DIV 2 + 1) (\x. vectorize((C:real^N->real^Q^Q) x)) x) *
         pde_jetn (n + 1) (u:real^N->real^Q) x +
         (pde_jetn n (\x. vectorize(A x)) x +
          sum(1..dimindex(:N)) (\i. pde_jetn n (\x. vectorize(B x i)) x) +
          pde_jetn n (\x. vectorize(C x)) x) * pde_jetn (n DIV 2 + 2) u x` THEN
  (* each term is bounded by 2^n (n+1) T0 *)
  SUBGOAL_THEN
   `(!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> norm(iterated_partial l
                     (\x. (A:real^N->real^N^N) x$i$j %
                          partial_derivative i (partial_derivative j (u:real^N->real^Q)) x) x -
                    A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l u)) x)
               <= &2 pow n * &(n + 1) * T0) /\
    (!i. 1 <= i /\ i <= dimindex(:N)
         ==> norm(iterated_partial l (\x. (B:real^N->num->real^Q^Q) x i **
                                           partial_derivative i u x) x)
             <= &2 pow n * &(n + 1) * T0) /\
    norm(iterated_partial l (\x. (C:real^N->real^Q^Q) x ** u x) x) <= &2 pow n * &(n + 1) * T0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &2 pow n * &(n + 1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!a1 a2. a1 <= pde_jetn (n DIV 2 + 1) (\x. vectorize((A:real^N->real^N^N) x)) x +
                    sum(1..dimindex(:N)) (\i. pde_jetn (n DIV 2 + 1)
                                     (\x. vectorize((B:real^N->num->real^Q^Q) x i)) x) +
                    pde_jetn (n DIV 2 + 1) (\x. vectorize((C:real^N->real^Q^Q) x)) x /\
              a2 <= pde_jetn n (\x. vectorize(A x)) x +
                    sum(1..dimindex(:N)) (\i. pde_jetn n (\x. vectorize(B x i)) x) +
                    pde_jetn n (\x. vectorize(C x)) x
              ==> &2 pow n * &(n + 1) *
                  (a1 * pde_jetn (n + 1) (u:real^N->real^Q) x + a2 * pde_jetn (n DIV 2 + 2) u x)
                  <= &2 pow n * &(n + 1) * T0`
    (LABEL_TAC "cmp") THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      EXPAND_TAC "T0" THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[PDE_JETN_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!m i. 1 <= i /\ i <= dimindex(:N)
            ==> pde_jetn m (\x. vectorize((B:real^N->num->real^Q^Q) x i)) x <=
                sum(1..dimindex(:N)) (\i. pde_jetn m (\x. vectorize(B x i)) x)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`{i:num}`; `1..dimindex(:N)`;
                     `\i. pde_jetn m (\x. vectorize((B:real^N->num->real^Q^Q) x i)) x`]
        SUM_SUBSET_SIMPLE) THEN
      REWRITE_TAC[SUM_SING; FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; PDE_JETN_POS] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `A:real^N->real^N^N`; `u:real^N->real^Q`;
                     `i:num`; `j:num`; `x:real^N`] RDT_LOP0_TERM_A) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
      USE_THEN "cmp" MATCH_MP_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ &0 <= c ==> a <= a + b + c`) THEN
      SIMP_TAC[PDE_JETN_POS; SUM_POS_LE_NUMSEG];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `\x. (B:real^N->num->real^Q^Q) x i`;
                     `u:real^N->real^Q`; `[i:num]`; `x:real^N`] RDT_LOP0_TERM_BC) THEN
      ASM_REWRITE_TAC[ALL; LENGTH; ARITH_RULE `SUC 0 <= 1`; iterated_partial] THEN
      MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
      USE_THEN "cmp" MATCH_MP_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b /\ &0 <= x /\ &0 <= c ==> a <= x + b + c`) THEN
      ASM_SIMP_TAC[PDE_JETN_POS];
      MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `C:real^N->real^Q^Q`;
                     `u:real^N->real^Q`; `[]:num list`; `x:real^N`] RDT_LOP0_TERM_BC) THEN
      ASM_REWRITE_TAC[ALL; LENGTH; LE_0; iterated_partial; ETA_AX] THEN
      MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
      USE_THEN "cmp" MATCH_MP_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= b ==> c <= x + b + c`) THEN
      SIMP_TAC[PDE_JETN_POS; SUM_POS_LE_NUMSEG]];
    ALL_TAC] THEN
  (* linearity of d^l *)
  SUBGOAL_THEN
   `iterated_partial l (pde_lop0 A B C (u:real^N->real^Q)) x =
    vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
      (\j. iterated_partial l (\x. (A:real^N->real^N^N) x$i$j %
                                    partial_derivative i (partial_derivative j u) x) x)) +
    vsum(1..dimindex(:N)) (\i. iterated_partial l
                                 (\x. (B:real^N->num->real^Q^Q) x i ** partial_derivative i u x) x) +
    iterated_partial l (\x. (C:real^N->real^Q^Q) x ** u x) x`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `pde_lop0 A B C (u:real^N->real^Q) =
      (\x. vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
              (\j. (A:real^N->real^N^N) x$i$j % partial_derivative i (partial_derivative j u) x)) +
            (vsum(1..dimindex(:N)) (\i. (B:real^N->num->real^Q^Q) x i ** partial_derivative i u x) +
             (C:real^N->real^Q^Q) x ** u x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_lop0; VECTOR_ADD_ASSOC]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`;
      `\x. vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
              (\j. (A:real^N->real^N^N) x$i$j %
                    partial_derivative i (partial_derivative j (u:real^N->real^Q)) x))`;
      `\x. vsum(1..dimindex(:N)) (\i. (B:real^N->num->real^Q^Q) x i **
                                        partial_derivative i (u:real^N->real^Q) x) +
            (C:real^N->real^Q^Q) x ** u x`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`;
      `\x. vsum(1..dimindex(:N)) (\i. (B:real^N->num->real^Q^Q) x i **
                                        partial_derivative i (u:real^N->real^Q) x)`;
      `\x. (C:real^N->real^Q^Q) x ** (u:real^N->real^Q) x`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`;
      `\i x. (B:real^N->num->real^Q^Q) x i ** partial_derivative i (u:real^N->real^Q) x`;
      `1..dimindex(:N)`] PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`;
      `\i x. vsum(1..dimindex(:N)) (\j. (A:real^N->real^N^N) x$i$j %
                                    partial_derivative i (partial_derivative j (u:real^N->real^Q)) x)`;
      `1..dimindex(:N)`] PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`;
      `\j x. (A:real^N->real^N^N) x$i$j %
              partial_derivative i (partial_derivative j (u:real^N->real^Q)) x`;
      `1..dimindex(:N)`] PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `(a + b + c) - d:real^Q = (a - d) + b + c`] THEN
  REWRITE_TAC[GSYM VSUM_SUB_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a b c e1 e2 e3 e. norm(a:real^Q) <= e1 /\ norm(b:real^Q) <= e2 /\ norm(c:real^Q) <= e3 /\
                      e1 + e2 + e3 <= e ==> norm(a + b + c) <= e`) THEN
  ABBREV_TAC `bd = &2 pow n * &(n + 1) * T0` THEN
  MAP_EVERY EXISTS_TAC [`&(dimindex(:N)) * (&(dimindex(:N)) * bd)`; `&(dimindex(:N)) * bd`;
                        `bd:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. &(dimindex(:N)) * bd)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
       `sum(1..dimindex(:N))
          (\i. norm(vsum(1..dimindex(:N))
            (\j. iterated_partial l (\x. (A:real^N->real^N^N) x$i$j %
                    partial_derivative i (partial_derivative j (u:real^N->real^Q)) x) x -
                  A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l u)) x)))` THEN
      SIMP_TAC[VSUM_NORM; FINITE_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:N)) (\j. bd:real)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
        REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..dimindex(:N)) (\i. bd:real)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Integral helpers for the chart energy: finite sums, the                   *)
(* integral over K, the level-(s+1) norm through the dissipation, and the    *)
(* principal integration by parts.                                           *)
(* ------------------------------------------------------------------------- *)

let RDT_CS_SUM = prove
 (`!U K (f:A->real^N->real) s.
     FINITE s /\ (!k. k IN s ==> rdt_cs U K (f k))
     ==> rdt_cs U K (\y. sum s (\k. f k y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rdt_cs] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC[]]);;

let RDT_INT_SUM = prove
 (`!U K (f:A->real^N->real) s.
     open U /\ compact K /\ K SUBSET U /\ FINITE s /\ (!k. k IN s ==> rdt_cs U K (f k))
     ==> rdt_int U (\y. sum s (\k. f k y)) = sum s (\k. rdt_int U (f k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_int; LIFT_SUM; o_DEF] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_VSUM o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_CS_INTEGRABLE THEN
    EXISTS_TAC `K:real^N->bool` THEN ASM_SIMP_TAC[ETA_AX];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[DROP_VSUM; o_DEF]]);;

let RDT_INT_ON_K = prove
 (`!U K (f:real^N->real).
     open U /\ compact K /\ K SUBSET U /\ rdt_cs U K f
     ==> rdt_int U f = drop(integral K (\y. lift(f y)))`,
  REWRITE_TAC[rdt_cs; rdt_int] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN `(\y. lift((f:real^N->real) y)) integrable_on K` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y. lift((f:real^N->real) y)`; `K:real^N->bool`]
      PDM_INTEGRABLE_CONTINUOUS_COMPACT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
  EXISTS_TAC `\y. if y IN K then lift((f:real^N->real) y) else vec 0` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[LIFT_NUM];
    MATCH_MP_TAC HAS_INTEGRAL_ON_SUPERSET THEN EXISTS_TAC `K:real^N->bool` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
    EXISTS_TAC `\y. lift((f:real^N->real) y)` THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]]);;

(* Squared norms of derivatives of a map vanishing off K.                    *)

let RDT_CS_SQNORM = prove
 (`!U K (u:real^N->real^Q) l.
     open U /\ compact K /\ smooth_map_on U u /\ (!y. y IN U /\ ~(y IN K) ==> u y = vec 0)
     ==> rdt_cs U K (\y. norm(iterated_partial l u y) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on U (iterated_partial l (u:real^N->real^Q))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `iterated_partial l (u:real^N->real^Q)`;
                 `iterated_partial l (u:real^N->real^Q)`] RDT_CS_SMOOTH_DOT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC RDT_PARTIAL_CS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2; ETA_AX]);;

(* The level SUC s chart norm: the level 0 term and the derivatives.         *)

let RDT_HS_SUC = prove
 (`!U K (u:real^N->real^Q) s.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U u /\
     (!y. y IN U /\ ~(y IN K) ==> u y = vec 0)
     ==> rdt_hs U (SUC s) u =
         rdt_int U (\y. norm(u y) pow 2) +
         sum(1..dimindex(:N))
           (\i. sum (pde_index_lists s (:N))
                  (\l. rdt_int U (\y. norm(partial_derivative i (iterated_partial l u) y) pow 2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_hs; PDE_SUM_INDEX_LISTS_SUC; iterated_partial] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN
  REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; rdt_int] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `u:real^N->real^Q`; `i:num`] TEXT_PARTIAL_COMMUTE_ITERATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[]);;

let RDT_CS_NEG = prove
 (`!U K (f:real^N->real). rdt_cs U K f ==> rdt_cs U K (\y. --(f y))`,
  REWRITE_TAC[rdt_cs; LIFT_NEG] THEN SIMP_TAC[CONTINUOUS_ON_NEG; REAL_NEG_0]);;

let RDT_INT_NEG = prove
 (`!U K (f:real^N->real).
     open U /\ compact K /\ K SUBSET U /\ rdt_cs U K f
     ==> rdt_int U (\y. --(f y)) = --(rdt_int U f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `f:real^N->real`; `--(&1)`]
    RDT_INT_CMUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID]);;

let RDT_INT_EQ = prove
 (`!U (f:real^N->real) g. (!y. y IN U ==> f y = g y) ==> rdt_int U f = rdt_int U g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_int] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]);;

(* The principal integration by parts for one coefficient.                   *)

let RDT_PRINC_IBP = prove
 (`!U K (v:real^N->real^Q) (a:real^N->real) i j.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U v /\
     smooth_map_on U (\y. lift(a y)) /\ (!y. y IN U /\ ~(y IN K) ==> v y = vec 0)
     ==> rdt_int U (\y. v y dot (a y % partial_derivative i (partial_derivative j v) y)) =
         rdt_int U (\y. --(partial_derivative i v y dot (a y % partial_derivative j v y)) -
                        v y dot (drop(partial_derivative i (\y. lift(a y)) y) %
                                 partial_derivative j v y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN U /\ ~(y IN K) ==> partial_derivative i (v:real^N->real^Q) y = vec 0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `v:real^N->real^Q`; `[i:num]`]
      RDT_PARTIAL_CS) THEN
    ASM_REWRITE_TAC[iterated_partial];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U (\y. (a:real^N->real) y % partial_derivative j (v:real^N->real^Q) y) /\
    smooth_map_on U (\y. drop(partial_derivative i (\y. lift((a:real^N->real) y)) y) %
                         partial_derivative j (v:real^N->real^Q) y) /\
    smooth_map_on U (\y. (a:real^N->real) y % partial_derivative i (partial_derivative j v) y) /\
    smooth_map_on U (partial_derivative i (v:real^N->real^Q))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `\(x:real^1) (w:real^Q). drop x % w`;
                     `\y. lift((a:real^N->real) y)`; `partial_derivative j (v:real^N->real^Q)`]
        SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; LIFT_DROP];
      MP_TAC(ISPECL [`U:real^N->bool`; `\(x:real^1) (w:real^Q). drop x % w`;
                     `partial_derivative i (\y. lift((a:real^N->real) y))`;
                     `partial_derivative j (v:real^N->real^Q)`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
      MP_TAC(ISPECL [`U:real^N->bool`; `\(x:real^1) (w:real^Q). drop x % w`;
                     `\y. lift((a:real^N->real) y)`;
                     `partial_derivative i (partial_derivative j (v:real^N->real^Q))`]
        SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; LIFT_DROP];
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN U
        ==> partial_derivative i (\y. (a:real^N->real) y % partial_derivative j (v:real^N->real^Q) y) y =
            drop(partial_derivative i (\y. lift(a y)) y) % partial_derivative j v y +
            a y % partial_derivative i (partial_derivative j v) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\(x:real^1) (w:real^Q). drop x % w`; `\y. lift((a:real^N->real) y)`;
                   `partial_derivative j (v:real^N->real^Q)`; `i:num`; `y:real^N`]
      PDE_PARTIAL_BILINEAR) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; ETA_AX] THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* H1: integration by parts *)
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `v:real^N->real^Q`;
                 `\y. (a:real^N->real) y % partial_derivative j (v:real^N->real^Q) y`;
                 `i:num`] RDT_INT_IBP) THEN
  ASM_REWRITE_TAC[] THEN
  (* H2: split the derivative of the product *)
  SUBGOAL_THEN
   `rdt_int U (\y. (v:real^N->real^Q) y dot
                   partial_derivative i (\y. (a:real^N->real) y % partial_derivative j v y) y) =
    rdt_int U (\y. v y dot (drop(partial_derivative i (\y. lift(a y)) y) %
                            partial_derivative j v y)) +
    rdt_int U (\y. v y dot (a y % partial_derivative i (partial_derivative j v) y))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `rdt_int U (\y. (v:real^N->real^Q) y dot
                 (drop(partial_derivative i (\y. lift((a:real^N->real) y)) y) %
                  partial_derivative j v y) +
                 v y dot (a y % partial_derivative i (partial_derivative j v) y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RDT_INT_EQ THEN ASM_SIMP_TAC[DOT_RADD]; ALL_TAC] THEN
    MATCH_MP_TAC RDT_INT_ADD THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* H3: linearity of the right-hand side *)
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
    `\y. --(partial_derivative i (v:real^N->real^Q) y dot
            ((a:real^N->real) y % partial_derivative j v y))`;
    `\y. (v:real^N->real^Q) y dot (drop(partial_derivative i (\y. lift((a:real^N->real) y)) y) %
                                    partial_derivative j v y)`] RDT_INT_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_CS_NEG THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN
      ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
    `\y. partial_derivative i (v:real^N->real^Q) y dot
         ((a:real^N->real) y % partial_derivative j v y)`] RDT_INT_NEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  REAL_ARITH_TAC);;

let RDT_CS_EQ = prove
 (`!U K (f:real^N->real) g.
     (!y. y IN U ==> f y = g y) /\ rdt_cs U K f ==> rdt_cs U K g`,
  REWRITE_TAC[rdt_cs] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `\y. lift((f:real^N->real) y)` THEN
    ASM_SIMP_TAC[];
    ASM_MESON_TAC[]]);;

let RDT_INT_DSUM = prove
 (`!U K (f:num->num->real^N->real) n.
     open U /\ compact K /\ K SUBSET U /\ (!i j. rdt_cs U K (f i j))
     ==> rdt_int U (\y. sum(1..n) (\i. sum(1..n) (\j. f i j y))) =
         sum(1..n) (\i. sum(1..n) (\j. rdt_int U (f i j)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                 `\i y. sum(1..n) (\j. (f:num->num->real^N->real) i j y)`; `1..n`] RDT_INT_SUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RDT_CS_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                 `\j y. (f:num->num->real^N->real) i j y`; `1..n`] RDT_INT_SUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX]);;

(* The principal part of the energy after integration by parts.              *)

let RDT_ENERGY_PRINC = prove
 (`!U K (v:real^N->real^Q) (A:real^N->real^N^N) lam M delta.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U v /\
     smooth_map_on U (\x. vectorize(A x)) /\
     (!y. y IN U /\ ~(y IN K) ==> v y = vec 0) /\
     (!y w. y IN K ==> lam * norm w pow 2 <= w dot (A y ** w)) /\
     (!y. y IN K ==> pde_jetn 1 (\x. vectorize(A x)) y <= M) /\ &0 <= M /\ &0 < delta
     ==> rdt_int U (\y. &2 * (v y dot vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                      (\j. A y$i$j % partial_derivative i (partial_derivative j v) y)))) <=
         (delta - &2 * lam) *
         sum(1..dimindex(:N)) (\i. rdt_int U (\y. norm(partial_derivative i v y) pow 2)) +
         (&(dimindex(:N)) pow 3 * M pow 2 / delta) * rdt_int U (\y. norm(v y) pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `dA = \i j (y:real^N). drop(partial_derivative i (\y. lift((A:real^N->real^N^N) y$i$j)) y)` THEN
  SUBGOAL_THEN
   `!i j. smooth_map_on U (\y. lift((A:real^N->real^N^N) y$i$j))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC RDT_SMOOTH_ENTRY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN U /\ ~(y IN K) ==> !i. partial_derivative i (v:real^N->real^Q) y = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `v:real^N->real^Q`; `[i:num]`]
      RDT_PARTIAL_CS) THEN
    ASM_SIMP_TAC[iterated_partial];
    ALL_TAC] THEN
  (* the integral identity from integration by parts *)
  SUBGOAL_THEN
   `rdt_int U (\y. &2 * ((v:real^N->real^Q) y dot vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                      (\j. (A:real^N->real^N^N) y$i$j %
                           partial_derivative i (partial_derivative j v) y)))) =
    rdt_int U (\y. --(&2) * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                     (\j. A y$i$j * (partial_derivative i v y dot partial_derivative j v y))) -
                   &2 * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                     (\j. dA i j y * (v y dot partial_derivative j v y))))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `!i j. rdt_cs U K (\y. &2 * ((v:real^N->real^Q) y dot ((A:real^N->real^N^N) y$i$j %
                               partial_derivative i (partial_derivative j v) y))) /\
            rdt_cs U K (\y. &2 * (--(partial_derivative i v y dot (A y$i$j % partial_derivative j v y)) -
                               v y dot (dA i j y % partial_derivative j v y)))`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC RDT_CS_CMUL THENL
       [MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`U:real^N->bool`; `\(x:real^1) (w:real^Q). drop x % w`;
                       `\y. lift((A:real^N->real^N^N) y$i$j)`;
                       `partial_derivative i (partial_derivative j (v:real^N->real^Q))`]
          SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
        ASM_SIMP_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; LIFT_DROP];
        MATCH_MP_TAC RDT_CS_SUB THEN CONJ_TAC THENL
         [MATCH_MP_TAC RDT_CS_NEG THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN
          ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX] THEN
          MP_TAC(ISPECL [`U:real^N->bool`; `\(x:real^1) (w:real^Q). drop x % w`;
                         `\y. lift((A:real^N->real^N^N) y$i$j)`;
                         `partial_derivative j (v:real^N->real^Q)`]
            SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
          ASM_SIMP_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; LIFT_DROP];
          MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "dA" THEN
          MP_TAC(ISPECL [`U:real^N->bool`; `\(x:real^1) (w:real^Q). drop x % w`;
                         `partial_derivative i (\y. lift((A:real^N->real^N^N) y$i$j))`;
                         `partial_derivative j (v:real^N->real^Q)`]
            SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
          ASM_SIMP_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `rdt_int U (\y. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
        (\j. &2 * ((v:real^N->real^Q) y dot ((A:real^N->real^N^N) y$i$j %
                    partial_derivative i (partial_derivative j v) y)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RDT_INT_EQ THEN SIMP_TAC[DOT_RSUM; FINITE_NUMSEG; GSYM SUM_LMUL];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `rdt_int U (\y. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
        (\j. &2 * (--(partial_derivative i (v:real^N->real^Q) y dot
                       ((A:real^N->real^N^N) y$i$j % partial_derivative j v y)) -
                   v y dot (dA i j y % partial_derivative j v y)))))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
        `\i j y. &2 * ((v:real^N->real^Q) y dot ((A:real^N->real^N^N) y$i$j %
                    partial_derivative i (partial_derivative j v) y))`;
        `dimindex(:N)`] RDT_INT_DSUM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
        `\i j y. &2 * (--(partial_derivative i (v:real^N->real^Q) y dot
                       ((A:real^N->real^N^N) y$i$j % partial_derivative j v y)) -
                   v y dot (dA i j y % partial_derivative j v y))`;
        `dimindex(:N)`] RDT_INT_DSUM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
        `\y. (v:real^N->real^Q) y dot ((A:real^N->real^N^N) y$i$j %
                                        partial_derivative i (partial_derivative j v) y)`;
        `&2`] RDT_INT_CMUL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`U:real^N->bool`; `\(x:real^1) (w:real^Q). drop x % w`;
                       `\y. lift((A:real^N->real^N^N) y$i$j)`;
                       `partial_derivative i (partial_derivative j (v:real^N->real^Q))`]
          SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
        ASM_SIMP_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; LIFT_DROP];
        REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
        `\y. --(partial_derivative i (v:real^N->real^Q) y dot
                 ((A:real^N->real^N^N) y$i$j % partial_derivative j v y)) -
              v y dot (dA i j y % partial_derivative j v y)`;
        `&2`] RDT_INT_CMUL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC RDT_CS_SUB THEN CONJ_TAC THENL
         [MATCH_MP_TAC RDT_CS_NEG THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN
          ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX] THEN
          MP_TAC(ISPECL [`U:real^N->bool`; `\(x:real^1) (w:real^Q). drop x % w`;
                         `\y. lift((A:real^N->real^N^N) y$i$j)`;
                         `partial_derivative j (v:real^N->real^Q)`]
            SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
          ASM_SIMP_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; LIFT_DROP];
          MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "dA" THEN
          MP_TAC(ISPECL [`U:real^N->bool`; `\(x:real^1) (w:real^Q). drop x % w`;
                         `partial_derivative i (\y. lift((A:real^N->real^N^N) y$i$j))`;
                         `partial_derivative j (v:real^N->real^Q)`]
            SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
          ASM_SIMP_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]];
        REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN EXPAND_TAC "dA" THEN MATCH_MP_TAC RDT_PRINC_IBP THEN
      EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RDT_INT_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[DOT_RMUL] THEN
      REWRITE_TAC[REAL_ARITH `&2 * (--(a * b) - c * d) = --(&2) * (a * b) - &2 * (c * d)`] THEN
      REWRITE_TAC[SUM_SUB_NUMSEG; SUM_LMUL]];
    ALL_TAC] THEN
  (* the pointwise bound *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `rdt_int U (\y. (delta - &2 * lam) *
                   sum(1..dimindex(:N)) (\i. norm(partial_derivative i (v:real^N->real^Q) y) pow 2) +
                   (&(dimindex(:N)) pow 3 * M pow 2 / delta) * norm(v y) pow 2)` THEN
  SUBGOAL_THEN
   `!i. rdt_cs U K (\y. norm(partial_derivative i (v:real^N->real^Q) y) pow 2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `v:real^N->real^Q`;
                                `[i:num]`] RDT_CS_SQNORM) THEN
    ASM_REWRITE_TAC[iterated_partial];
    ALL_TAC] THEN
  SUBGOAL_THEN `rdt_cs U K (\y. norm((v:real^N->real^Q) y) pow 2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `v:real^N->real^Q`; `[]:num list`]
      RDT_CS_SQNORM) THEN
    ASM_REWRITE_TAC[iterated_partial; ETA_AX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RDT_INT_LE THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RDT_CS_EQ THEN
      EXISTS_TAC `\y. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
        (\j. &2 * (--(partial_derivative i (v:real^N->real^Q) y dot
                       ((A:real^N->real^N^N) y$i$j % partial_derivative j v y)) -
                   v y dot (dA i j y % partial_derivative j v y))))` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[DOT_RMUL] THEN
        REWRITE_TAC[REAL_ARITH `&2 * (--(a * b) - c * d) = --(&2) * (a * b) - &2 * (c * d)`] THEN
        REWRITE_TAC[SUM_SUB_NUMSEG; SUM_LMUL];
        ALL_TAC] THEN
      MATCH_MP_TAC RDT_CS_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC RDT_CS_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC RDT_CS_CMUL THEN MATCH_MP_TAC RDT_CS_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC RDT_CS_NEG THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX] THEN
        MP_TAC(ISPECL [`U:real^N->bool`; `\(x:real^1) (w:real^Q). drop x % w`;
                       `\y. lift((A:real^N->real^N^N) y$i$j)`;
                       `partial_derivative j (v:real^N->real^Q)`]
          SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
        ASM_SIMP_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; LIFT_DROP];
        MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "dA" THEN
        MP_TAC(ISPECL [`U:real^N->bool`; `\(x:real^1) (w:real^Q). drop x % w`;
                       `partial_derivative i (\y. lift((A:real^N->real^N^N) y$i$j))`;
                       `partial_derivative j (v:real^N->real^Q)`]
          SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
        ASM_SIMP_TAC[BILINEAR_DROP_MUL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]];
      MATCH_MP_TAC RDT_CS_ADD THEN CONJ_TAC THEN MATCH_MP_TAC RDT_CS_CMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_CS_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `(y:real^N) IN K` THENL
       [MATCH_MP_TAC PDE_PRINC_POINTWISE THEN ASM_SIMP_TAC[] THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN EXPAND_TAC "dA" THEN
        REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn 1 (\x. vectorize((A:real^N->real^N^N) x)) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn 1 (\x. lift((A:real^N->real^N^N) x$i$j)) y` THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP] THEN
          MP_TAC(ISPECL [`1`; `\x. lift((A:real^N->real^N^N) x$i$j)`; `[i:num]`; `y:real^N`]
            RDT_NORM_LE_JETN) THEN
          ASM_REWRITE_TAC[ALL; LENGTH; iterated_partial; LE_REFL; ONE];
          MATCH_MP_TAC RDT_JETN_ENTRY THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[]];
        SUBGOAL_THEN `((v:real^N->real^Q) y = vec 0) /\ (!i. partial_derivative i (v:real^N->real^Q) y = vec 0)`
        STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[DOT_LZERO; DOT_RZERO; NORM_0; REAL_MUL_RZERO; SUM_0] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC[SUM_0; REAL_MUL_RZERO; REAL_ADD_LID; REAL_LE_REFL]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
    `\y. (delta - &2 * lam) *
         sum(1..dimindex(:N)) (\i. norm(partial_derivative i (v:real^N->real^Q) y) pow 2)`;
    `\y. (&(dimindex(:N)) pow 3 * M pow 2 / delta) * norm((v:real^N->real^Q) y) pow 2`]
    RDT_INT_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RDT_CS_CMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_CS_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
    `\y. sum(1..dimindex(:N)) (\i. norm(partial_derivative i (v:real^N->real^Q) y) pow 2)`;
    `delta - &2 * lam`] RDT_INT_CMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_CS_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `\y. norm((v:real^N->real^Q) y) pow 2`;
    `&(dimindex(:N)) pow 3 * M pow 2 / delta`] RDT_INT_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
    `\i y. norm(partial_derivative i (v:real^N->real^Q) y) pow 2`; `1..dimindex(:N)`]
    RDT_INT_SUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Chart norms: positivity, monotonicity in the level, and the               *)
(* Sobolev bound for the jets of a map vanishing off K.                      *)
(* ------------------------------------------------------------------------- *)

let RDT_HS_TERM_POS = prove
 (`!U K (u:real^N->real^Q) l.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U u /\
     (!y. y IN U /\ ~(y IN K) ==> u y = vec 0)
     ==> &0 <= rdt_int U (\y. norm(iterated_partial l u y) pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_INT_POS THEN EXISTS_TAC `K:real^N->bool` THEN
  ASM_SIMP_TAC[RDT_CS_SQNORM; REAL_POW_2; REAL_LE_SQUARE]);;

let RDT_HS_POS = prove
 (`!U K (u:real^N->real^Q) s.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U u /\
     (!y. y IN U /\ ~(y IN K) ==> u y = vec 0)
     ==> &0 <= rdt_hs U s u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_hs] THEN MATCH_MP_TAC SUM_POS_LE THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RDT_HS_TERM_POS THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let RDT_HS_MONO = prove
 (`!U K (u:real^N->real^Q) s s'.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U u /\
     (!y. y IN U /\ ~(y IN K) ==> u y = vec 0) /\ s <= s'
     ==> rdt_hs U s u <= rdt_hs U s' u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_hs] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_SIMP_TAC[PDE_INDEX_LISTS_FINITE; PDE_INDEX_LISTS_MONO] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RDT_HS_TERM_POS THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let RDT_HS_TERM_LE = prove
 (`!U K (u:real^N->real^Q) s l.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U u /\
     (!y. y IN U /\ ~(y IN K) ==> u y = vec 0) /\
     LENGTH l <= s /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> rdt_int U (\y. norm(iterated_partial l u y) pow 2) <= rdt_hs U s u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_hs] THEN
  MP_TAC(ISPECL [`{l:num list}`; `pde_index_lists s (:N)`;
                 `\l. rdt_int U (\y. norm(iterated_partial l (u:real^N->real^Q) y) pow 2)`]
    SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[SUM_SING; PDE_INDEX_LISTS_FINITE; SING_SUBSET] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RDT_HS_TERM_POS THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let RDT_SOBOLEV_JETN = prove
 (`!(K:real^N->bool) m.
     compact K
     ==> ?C. &0 <= C /\
             !U (u:real^N->real^Q) y.
               open U /\ K SUBSET U /\ smooth_map_on U u /\
               (!y. y IN U /\ ~(y IN K) ==> u y = vec 0) /\ y IN U
               ==> pde_jetn m u y pow 2 <= C * rdt_hs U (dimindex(:N) + m) u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (INST_TYPE [`:Q`,`:K`] PDM_SOBOLEV_COMPACT)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&(CARD(pde_index_lists m (:N))) pow 2 * C0` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LT_IMP_LE];
                  ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= rdt_hs U (dimindex(:N) + m) (u:real^N->real^Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_HS_POS THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `u:real^N->real^Q`; `y:real^N`;
                 `C0 * rdt_hs U (dimindex(:N) + m) (u:real^N->real^Q)`] PDM_JETN_SQ_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`U:real^N->bool`; `u:real^N->real^Q`; `l:num list`;
                                  `y:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM rdt_int; GSYM rdt_hs] THEN
    MATCH_MP_TAC RDT_HS_MONO THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&(CARD(pde_index_lists m (:N))) *
               sqrt(C0 * rdt_hs U (dimindex(:N) + m) (u:real^N->real^Q))) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[PDE_JETN_POS]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  SUBGOAL_THEN `&0 <= C0 * rdt_hs U (dimindex(:N) + m) (u:real^N->real^Q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]);;

(* AM-GM against a jet sum (scalar form of PDE_JET_AMGM).                     *)

let RDT_JET_AMGM_SCALAR = prove
 (`!(u:real^N->real^Q) b c eta k x.
     &0 <= b /\ &0 <= c /\ &0 < eta
     ==> &2 * b * (c * pde_jetn k u x) <=
         eta * sum (pde_index_lists k (:N)) (\l. norm(iterated_partial l u x) pow 2) +
         &(CARD(pde_index_lists k (:N))) * (c pow 2 / eta) * b pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists k (:N))
                (\l. eta * norm(iterated_partial l (u:real^N->real^Q) x) pow 2 +
                     (c * b) pow 2 / eta)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`norm(iterated_partial l (u:real^N->real^Q) x)`; `c * b:real`;
                   `eta:real`] PDE_AMGM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SIMP_TAC[SUM_ADD; SUM_LMUL; SUM_CONST; PDE_INDEX_LISTS_FINITE] THEN
    REWRITE_TAC[real_div; REAL_POW_MUL] THEN REAL_ARITH_TAC]);;

(* The forcing term of the energy, with one derivative moved onto u at the  *)
(* top order.                                                                *)

let RDT_ENERGY_F = prove
 (`!U K (u:real^N->real^Q) Fo s l eta.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U u /\ smooth_map_on U Fo /\
     (!y. y IN U /\ ~(y IN K) ==> u y = vec 0 /\ Fo y = vec 0) /\
     l IN pde_index_lists s (:N) /\ &0 < eta
     ==> rdt_int U (\y. &2 * (iterated_partial l u y dot iterated_partial l Fo y)) <=
         eta * rdt_hs U (s + 1) u + rdt_hs U s u + (&1 + inv eta) * rdt_hs U (s - 1) Fo`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!y. y IN U /\ ~(y IN K) ==> (u:real^N->real^Q) y = vec 0) /\
                (!y. y IN U /\ ~(y IN K) ==> (Fo:real^N->real^Q) y = vec 0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rdt_hs U (s + 1) (u:real^N->real^Q) /\ &0 <= rdt_hs U s u /\
                &0 <= rdt_hs U (s - 1) (Fo:real^N->real^Q)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC RDT_HS_POS THEN EXISTS_TAC `K:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv eta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!l'. rdt_cs U K (\y. norm(iterated_partial l' (u:real^N->real^Q) y) pow 2) /\
         rdt_cs U K (\y. norm(iterated_partial l' (Fo:real^N->real^Q) y) pow 2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC RDT_CS_SQNORM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:num list) < s \/ s = 0` THENL
   [(* no integration by parts *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `rdt_int U (\y. norm(iterated_partial l (u:real^N->real^Q) y) pow 2 +
                               norm(iterated_partial l (Fo:real^N->real^Q) y) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RDT_INT_LE THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC RDT_CS_CMUL THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX] THEN
        MATCH_MP_TAC RDT_PARTIAL_CS THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC RDT_CS_ADD THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        MP_TAC(ISPEC `iterated_partial l (u:real^N->real^Q) y -
                      iterated_partial l (Fo:real^N->real^Q) y` DOT_POS_LE) THEN
        MP_TAC(ISPECL [`iterated_partial l (u:real^N->real^Q) y`;
                       `iterated_partial l (Fo:real^N->real^Q) y`] DOT_SYM) THEN
        REWRITE_TAC[NORM_POW_2; DOT_LSUB; DOT_RSUB] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                   `\y. norm(iterated_partial l (u:real^N->real^Q) y) pow 2`;
                   `\y. norm(iterated_partial l (Fo:real^N->real^Q) y) pow 2`] RDT_INT_ADD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= x /\ b <= z /\ &0 <= e * w /\ &0 <= i * z ==> a + b <= e * w + x + (&1 + i) * z`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN CONJ_TAC THEN
    MATCH_MP_TAC RDT_HS_TERM_LE THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* the top order: move one derivative from Fo onto u *)
  SUBGOAL_THEN `LENGTH(l:num list) = s /\ ~(s = 0)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `l:num list` list_CASES) THEN STRIP_TAC THENL
   [UNDISCH_TAC `LENGTH(l:num list) = s` THEN ASM_REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; LENGTH]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC o
    check (fun th -> can (find_term ((=) `ALL:(num->bool)->num list->bool`)) (concl th))) THEN
  REWRITE_TAC[iterated_partial] THEN
  SUBGOAL_THEN
   `smooth_map_on U (iterated_partial t (u:real^N->real^Q)) /\
    smooth_map_on U (iterated_partial t (Fo:real^N->real^Q)) /\
    (!y. y IN U /\ ~(y IN K) ==> iterated_partial t (Fo:real^N->real^Q) y = vec 0) /\
    (!y. y IN U /\ ~(y IN K)
         ==> partial_derivative h (iterated_partial t (u:real^N->real^Q)) y = vec 0)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_PARTIAL_CS THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM(CONJUNCT2 iterated_partial)] THEN
      MATCH_MP_TAC RDT_PARTIAL_CS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `W = iterated_partial t (u:real^N->real^Q)` THEN
  ABBREV_TAC `G = iterated_partial t (Fo:real^N->real^Q)` THEN
  SUBGOAL_THEN
   `rdt_int U (\y. &2 * (partial_derivative h (W:real^N->real^Q) y dot
                         partial_derivative h (G:real^N->real^Q) y)) =
    rdt_int U (\y. --(&2) * (G y dot partial_derivative h (partial_derivative h W) y))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `G:real^N->real^Q`;
                   `partial_derivative h (W:real^N->real^Q)`; `h:num`] RDT_INT_IBP) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                   `\y. partial_derivative h (W:real^N->real^Q) y dot
                        partial_derivative h (G:real^N->real^Q) y`; `&2`] RDT_INT_CMUL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                   `\y. (G:real^N->real^Q) y dot
                        partial_derivative h (partial_derivative h (W:real^N->real^Q)) y`;
                   `--(&2)`] RDT_INT_CMUL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     `rdt_int U (\y. partial_derivative h (W:real^N->real^Q) y dot
                     partial_derivative h (G:real^N->real^Q) y) =
      rdt_int U (\y. partial_derivative h G y dot partial_derivative h W y)`
    SUBST1_TAC THENL [MATCH_MP_TAC RDT_INT_EQ THEN SIMP_TAC[DOT_SYM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `rdt_int U (\y. eta * norm(partial_derivative h
                                    (partial_derivative h (W:real^N->real^Q)) y) pow 2 +
                             inv eta * norm((G:real^N->real^Q) y) pow 2)` THEN
  SUBGOAL_THEN
   `rdt_cs U K (\y. norm(partial_derivative h (partial_derivative h (W:real^N->real^Q)) y) pow 2) /\
    rdt_cs U K (\y. norm((G:real^N->real^Q) y) pow 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `W:real^N->real^Q`; `[h:num; h]`]
        RDT_CS_SQNORM) THEN
      REWRITE_TAC[iterated_partial] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN MATCH_MP_TAC RDT_PARTIAL_CS THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `G:real^N->real^Q`; `[]:num list`]
        RDT_CS_SQNORM) THEN
      ASM_REWRITE_TAC[iterated_partial; ETA_AX]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RDT_INT_LE THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RDT_CS_CMUL THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
      MATCH_MP_TAC RDT_CS_ADD THEN CONJ_TAC THEN MATCH_MP_TAC RDT_CS_CMUL THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * norm(partial_derivative h (partial_derivative h (W:real^N->real^Q)) y) *
                  norm((G:real^N->real^Q) y)` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`(G:real^N->real^Q) y`;
                       `partial_derivative h (partial_derivative h (W:real^N->real^Q)) y`]
          NORM_CAUCHY_SCHWARZ_ABS) THEN
        REAL_ARITH_TAC;
        MP_TAC(ISPECL [`norm(partial_derivative h (partial_derivative h (W:real^N->real^Q)) y)`;
                       `norm((G:real^N->real^Q) y)`; `eta:real`] PDE_AMGM) THEN
        ASM_REWRITE_TAC[real_div; REAL_MUL_AC]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
    `\y. eta * norm(partial_derivative h (partial_derivative h (W:real^N->real^Q)) y) pow 2`;
    `\y. inv eta * norm((G:real^N->real^Q) y) pow 2`] RDT_INT_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RDT_CS_CMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
    `\y. norm(partial_derivative h (partial_derivative h (W:real^N->real^Q)) y) pow 2`;
    `eta:real`] RDT_INT_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `\y. norm((G:real^N->real^Q) y) pow 2`;
    `inv eta:real`] RDT_INT_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `rdt_int U (\y. norm(partial_derivative h (partial_derivative h (W:real^N->real^Q)) y) pow 2)
    <= rdt_hs U (s + 1) (u:real^N->real^Q) /\
    rdt_int U (\y. norm((G:real^N->real^Q) y) pow 2) <= rdt_hs U (s - 1) (Fo:real^N->real^Q)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W"; "G"] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `u:real^N->real^Q`; `s + 1`;
                     `CONS h (CONS h (t:num list))`] RDT_HS_TERM_LE) THEN
      ASM_REWRITE_TAC[iterated_partial; LENGTH; ALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `Fo:real^N->real^Q`; `s - 1`;
                     `t:num list`] RDT_HS_TERM_LE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `e * a <= e * x /\ i * b <= i * z /\ &0 <= y /\ &0 <= z
    ==> e * a + i * b <= e * x + y + (&1 + i) * z`) THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Integrals over the compact K of continuous functions, and                 *)
(* the remainder term of the energy (the part of d^l (L u) beyond the        *)
(* principal part), estimated on K with the L^2 bound of the coefficients.  *)
(* ------------------------------------------------------------------------- *)

let RDT_INTK_INTEGRABLE = prove
 (`!K (f:real^N->real). compact K /\ (\y. lift(f y)) continuous_on K
                        ==> (\y. lift(f y)) integrable_on K`,
  MESON_TAC[PDM_INTEGRABLE_CONTINUOUS_COMPACT]);;

let RDT_INTK_ADD = prove
 (`!K (f:real^N->real) g.
     compact K /\ (\y. lift(f y)) continuous_on K /\ (\y. lift(g y)) continuous_on K
     ==> drop(integral K (\y. lift(f y + g y))) =
         drop(integral K (\y. lift(f y))) + drop(integral K (\y. lift(g y)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_ADD o rand o lhand o snd) THEN
  ANTS_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC RDT_INTK_INTEGRABLE THEN ASM_REWRITE_TAC[];
                  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_ADD]]);;

let RDT_INTK_CMUL = prove
 (`!K (f:real^N->real) c.
     compact K /\ (\y. lift(f y)) continuous_on K
     ==> drop(integral K (\y. lift(c * f y))) = c * drop(integral K (\y. lift(f y)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_CMUL o rand o lhand o snd) THEN
  ANTS_TAC THENL [MATCH_MP_TAC RDT_INTK_INTEGRABLE THEN ASM_REWRITE_TAC[];
                  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_CMUL]]);;

let RDT_INTK_LE = prove
 (`!K (f:real^N->real) g.
     compact K /\ (\y. lift(f y)) continuous_on K /\ (\y. lift(g y)) continuous_on K /\
     (!y. y IN K ==> f y <= g y)
     ==> drop(integral K (\y. lift(f y))) <= drop(integral K (\y. lift(g y)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[LIFT_DROP; RDT_INTK_INTEGRABLE]);;

let RDT_INTK_SUM = prove
 (`!K (f:A->real^N->real) s.
     compact K /\ FINITE s /\ (!k. k IN s ==> (\y. lift(f k y)) continuous_on K)
     ==> drop(integral K (\y. lift(sum s (\k. f k y)))) =
         sum s (\k. drop(integral K (\y. lift(f k y))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_VSUM o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_INTK_INTEGRABLE THEN
    ASM_SIMP_TAC[ETA_AX];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[DROP_VSUM; o_DEF]]);;

(* Continuity facts on K from smoothness on U.                               *)

let RDT_CONT_SQNORM = prove
 (`!U K (w:real^N->real^Q).
     open U /\ K SUBSET U /\ smooth_map_on U w
     ==> (\y. lift(norm(w y) pow 2)) continuous_on K`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_SQNORM_CONTINUOUS THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ETA_AX]);;

(* The pointwise bound of the remainder term.                                *)

let RDT_X_POINTWISE = prove
 (`!(u:real^N->real^Q) (v:real^Q) (X:real^Q) n y c M Lam q eta.
     &0 <= c /\ &0 <= M /\ &0 <= Lam /\ &0 <= q /\ &0 < eta /\
     norm X <= c * (M * pde_jetn n u y + q * Lam)
     ==> &2 * (v dot X) <=
         eta * sum (pde_index_lists n (:N)) (\l. norm(iterated_partial l u y) pow 2) +
         (&(CARD(pde_index_lists n (:N))) * ((c * M) pow 2 / eta) + &1) * norm v pow 2 +
         (c * Lam) pow 2 * q pow 2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * norm(v:real^Q) * norm(X:real^Q)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`v:real^Q`; `X:real^Q`] NORM_CAUCHY_SCHWARZ_ABS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * norm(v:real^Q) * ((c * M) * pde_jetn n (u:real^N->real^Q) y) +
              &2 * norm v * ((c * Lam) * q)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * (M * pde_jetn n (u:real^N->real^Q) y + q * Lam)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->real^Q`; `norm(v:real^Q)`; `c * M:real`; `eta:real`; `n:num`;
                 `y:real^N`] RDT_JET_AMGM_SCALAR) THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_MUL] THEN
  MP_TAC(ISPECL [`norm(v:real^Q)`; `(c * Lam) * q`; `&1`] PDE_AMGM) THEN
  REWRITE_TAC[REAL_LT_01; REAL_DIV_1; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC);;

(* The remainder term of the energy, integrated.                             *)

let RDT_ENERGY_X = prove
 (`!U K (u:real^N->real^Q) (X:real^N->real^Q) (Qf:real^N->real) l n c M Lam eta.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U u /\ smooth_map_on U X /\
     (!y. y IN U /\ ~(y IN K) ==> u y = vec 0 /\ X y = vec 0) /\
     (\y. lift(Qf y)) continuous_on K /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
     &0 <= c /\ &0 <= M /\ &0 <= Lam /\ &0 < eta /\
     (!y. y IN K ==> &0 <= Qf y /\ norm(X y) <= c * (M * pde_jetn n u y + Qf y * Lam))
     ==> rdt_int U (\y. &2 * (iterated_partial l u y dot X y)) <=
         eta * rdt_hs U n u +
         (&(CARD(pde_index_lists n (:N))) * ((c * M) pow 2 / eta) + &1) *
         rdt_int U (\y. norm(iterated_partial l u y) pow 2) +
         (c * Lam) pow 2 * drop(integral K (\y. lift(Qf y pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!y. y IN U /\ ~(y IN K) ==> (u:real^N->real^Q) y = vec 0) /\
                (!y. y IN U /\ ~(y IN K) ==> (X:real^N->real^Q) y = vec 0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `C1 = &(CARD(pde_index_lists n (:N))) * ((c * M) pow 2 / eta) + &1` THEN
  SUBGOAL_THEN `smooth_map_on U (iterated_partial l (u:real^N->real^Q))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]; ALL_TAC] THEN
  SUBGOAL_THEN `!l'. (\y. lift(norm(iterated_partial l' (u:real^N->real^Q) y) pow 2))
                     continuous_on K` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RDT_CONT_SQNORM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift((Qf:real^N->real) y pow 2)) continuous_on K` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  (* to an integral over K *)
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                 `\y. &2 * (iterated_partial l (u:real^N->real^Q) y dot (X:real^N->real^Q) y)`]
    RDT_INT_ON_K) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_CS_CMUL THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN
    ASM_SIMP_TAC[ETA_AX] THEN MATCH_MP_TAC RDT_PARTIAL_CS THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral K (\y. lift(eta * sum (pde_index_lists n (:N))
                                 (\l'. norm(iterated_partial l' (u:real^N->real^Q) y) pow 2) +
                              C1 * norm(iterated_partial l u y) pow 2 +
                              (c * Lam) pow 2 * (Qf:real^N->real) y pow 2)))` THEN
  SUBGOAL_THEN
   `(\y. lift(sum (pde_index_lists n (:N))
                (\l'. norm(iterated_partial l' (u:real^N->real^Q) y) pow 2))) continuous_on K`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RDT_INTK_LE THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `\x y. lift((x:real^Q) dot y)`;
                     `iterated_partial l (u:real^N->real^Q)`; `X:real^N->real^Q`]
        SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[BILINEAR_DOT; SMOOTH_MAP_ON_CONTINUOUS_ON];
      REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
      REPEAT(MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC) THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      EXPAND_TAC "C1" THEN MATCH_MP_TAC RDT_X_POINTWISE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* split the integral over K and return to U *)
  MP_TAC(ISPECL [`K:real^N->bool`;
    `\y. eta * sum (pde_index_lists n (:N))
                  (\l'. norm(iterated_partial l' (u:real^N->real^Q) y) pow 2)`;
    `\y. C1 * norm(iterated_partial l (u:real^N->real^Q) y) pow 2 +
         (c * Lam) pow 2 * (Qf:real^N->real) y pow 2`] RDT_INTK_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`K:real^N->bool`;
    `\y. C1 * norm(iterated_partial l (u:real^N->real^Q) y) pow 2`;
    `\y. (c * Lam) pow 2 * (Qf:real^N->real) y pow 2`] RDT_INTK_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_CMUL] THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`K:real^N->bool`;
    `\y. sum (pde_index_lists n (:N)) (\l'. norm(iterated_partial l' (u:real^N->real^Q) y) pow 2)`;
    `eta:real`] RDT_INTK_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `\y. norm(iterated_partial l (u:real^N->real^Q) y) pow 2`;
    `C1:real`] RDT_INTK_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `\y. (Qf:real^N->real) y pow 2`;
    `(c * Lam) pow 2`] RDT_INTK_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`;
    `\l' y. norm(iterated_partial l' (u:real^N->real^Q) y) pow 2`; `pde_index_lists n (:N)`]
    RDT_INTK_SUM) THEN
  ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!l'. drop(integral K (\y. lift(norm(iterated_partial l' (u:real^N->real^Q) y) pow 2))) =
         rdt_int U (\y. norm(iterated_partial l' u y) pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RDT_INT_ON_K THEN
    ASM_SIMP_TAC[RDT_CS_SQNORM];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM rdt_hs; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The chart energy inequality at level s for                                *)
(* d/dt u = pde_lop0 A B C0 u + Fo (sum over the index lists of length at    *)
(* most s), first per index list, then summed, with the pointwise bound of   *)
(* the lower-order part X_l = d^l(L u) - A : D^2 d^l u as a hypothesis.      *)
(* ------------------------------------------------------------------------- *)

let RDT_LOP0_SMOOTH = prove
 (`!U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C:real^N->real^Q^Q) (u:real^N->real^Q).
     open U /\ smooth_map_on U (\x. vectorize(A x)) /\
     (!i. smooth_map_on U (\x. vectorize(B x i))) /\ smooth_map_on U (\x. vectorize(C x)) /\
     smooth_map_on U u
     ==> smooth_map_on U (pde_lop0 A B C u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `A:real^N->real^N^N`; `B:real^N->num->real^Q^Q`;
                 `C:real^N->real^Q^Q`; `u:real^N->real^Q`] RDT_LOP0_PIECES_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pde_lop0 A B C (u:real^N->real^Q) =
    (\x. (vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
            (\j. A x$i$j % partial_derivative i (partial_derivative j u) x)) +
          vsum(1..dimindex(:N)) (\i. B x i ** partial_derivative i u x)) +
         C x ** u x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_lop0; VECTOR_ADD_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[]);;

let RDT_JETN_CONT = prove
 (`!U K m (f:real^N->real^Q).
     open U /\ K SUBSET U /\ smooth_map_on U f
     ==> (\y. lift(pde_jetn m f y)) continuous_on K`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX]);;

let RDT_LOP0_ZERO_OFF = prove
 (`!U K (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C:real^N->real^Q^Q) (u:real^N->real^Q).
     open U /\ compact K /\ (!y. y IN U /\ ~(y IN K) ==> u y = vec 0)
     ==> !y. y IN U /\ ~(y IN K) ==> pde_lop0 A B C u y = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. partial_derivative i (partial_derivative j (u:real^N->real^Q)) y = vec 0 /\
          partial_derivative i u y = vec 0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `u:real^N->real^Q`; `[i:num; j]`]
        RDT_PARTIAL_CS);
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `u:real^N->real^Q`; `[i:num]`]
        RDT_PARTIAL_CS)] THEN
    ASM_REWRITE_TAC[iterated_partial] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[pde_lop0; VECTOR_MUL_RZERO; MATRIX_VECTOR_MUL_RZERO; VSUM_0; VECTOR_ADD_LID]);;

let RDT_INT_ADD3 = prove
 (`!U K (f:real^N->real) g h.
     open U /\ compact K /\ K SUBSET U /\ rdt_cs U K f /\ rdt_cs U K g /\ rdt_cs U K h
     ==> rdt_int U (\y. f y + g y + h y) = rdt_int U f + rdt_int U g + rdt_int U h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `f:real^N->real`;
                 `\y. (g:real^N->real) y + h y`] RDT_INT_ADD) THEN
  ASM_SIMP_TAC[RDT_CS_ADD] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC RDT_INT_ADD THEN EXISTS_TAC `K:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* One index list l: principal part (RDT_ENERGY_PRINC with delta = lam/2),   *)
(* remainder X_l (RDT_ENERGY_X at order s+1) and forcing (RDT_ENERGY_F).    *)

let RDT_ENERGY_ONE = prove
 (`!U K (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q)
    (u:real^N->real^Q) Fo (Qf:real^N->real) s l lam M c Lam eta.
     open U /\ compact K /\ K SUBSET U /\
     smooth_map_on U (\x. vectorize(A x)) /\
     (!i. smooth_map_on U (\x. vectorize(B x i))) /\ smooth_map_on U (\x. vectorize(C0 x)) /\
     smooth_map_on U u /\ smooth_map_on U Fo /\
     (!y. y IN U /\ ~(y IN K) ==> u y = vec 0 /\ Fo y = vec 0) /\
     (!y w. y IN K ==> lam * norm w pow 2 <= w dot (A y ** w)) /\
     (!y. y IN K ==> pde_jetn 1 (\x. vectorize(A x)) y <= M) /\
     (\y. lift(Qf y)) continuous_on K /\
     &0 < lam /\ &0 <= M /\ &0 <= c /\ &0 <= Lam /\ &0 < eta /\
     l IN pde_index_lists s (:N) /\
     (!y. y IN K
          ==> &0 <= Qf y /\
              norm(iterated_partial l (pde_lop0 A B C0 u) y -
                   vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                     (\j. A y$i$j %
                          partial_derivative i (partial_derivative j (iterated_partial l u)) y)))
              <= c * (M * pde_jetn (s + 1) u y + Qf y * Lam))
     ==> rdt_int U (\y. &2 * (iterated_partial l u y dot
                              iterated_partial l (\y. pde_lop0 A B C0 u y + Fo y) y)) <=
         --(&3 / &2 * lam) *
         sum(1..dimindex(:N))
           (\i. rdt_int U (\y. norm(partial_derivative i (iterated_partial l u) y) pow 2)) +
         &2 * eta * rdt_hs U (s + 1) u +
         (&2 * &(dimindex(:N)) pow 3 * M pow 2 / lam +
          &(CARD(pde_index_lists (s + 1) (:N))) * ((c * M) pow 2 / eta) + &1) *
         rdt_int U (\y. norm(iterated_partial l u y) pow 2) +
         rdt_hs U s u +
         (c * Lam) pow 2 * drop(integral K (\y. lift(Qf y pow 2))) +
         (&1 + inv eta) * rdt_hs U (s - 1) Fo`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!y. y IN U /\ ~(y IN K) ==> (u:real^N->real^Q) y = vec 0) /\
                (!y. y IN U /\ ~(y IN K) ==> (Fo:real^N->real^Q) y = vec 0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:N)) l` ASSUME_TAC THENL
   [UNDISCH_TAC `l IN pde_index_lists s (:N)` THEN
    SIMP_TAC[pde_index_lists; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (iterated_partial l (u:real^N->real^Q))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U /\ ~(y IN K) ==> iterated_partial l (u:real^N->real^Q) y = vec 0`
  ASSUME_TAC THENL [MATCH_MP_TAC RDT_PARTIAL_CS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `A:real^N->real^N^N`; `B:real^N->num->real^Q^Q`;
                 `C0:real^N->real^Q^Q`; `iterated_partial l (u:real^N->real^Q)`]
    RDT_LOP0_PIECES_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on U (pde_lop0 A B C0 (u:real^N->real^Q))` ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_LOP0_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (iterated_partial l (pde_lop0 A B C0 (u:real^N->real^Q))) /\
                smooth_map_on U (iterated_partial l (Fo:real^N->real^Q))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]; ALL_TAC] THEN
  (* the remainder X_l is smooth and vanishes off K *)
  SUBGOAL_THEN
   `smooth_map_on U
      (\y. iterated_partial l (pde_lop0 A B C0 (u:real^N->real^Q)) y -
           vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
             (\j. (A:real^N->real^N^N) y$i$j %
                  partial_derivative i (partial_derivative j (iterated_partial l u)) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN U /\ ~(y IN K)
        ==> iterated_partial l (pde_lop0 A B C0 (u:real^N->real^Q)) y -
            vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
              (\j. (A:real^N->real^N^N) y$i$j %
                   partial_derivative i (partial_derivative j (iterated_partial l u)) y)) =
            vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `iterated_partial l (pde_lop0 A B C0 (u:real^N->real^Q)) y = vec 0`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                     `pde_lop0 A B C0 (u:real^N->real^Q)`; `l:num list`] RDT_PARTIAL_CS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_LOP0_ZERO_OFF THEN ASM_REWRITE_TAC[];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i j. partial_derivative i (partial_derivative j (iterated_partial l (u:real^N->real^Q))) y =
            vec 0`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `iterated_partial l (u:real^N->real^Q)`;
                     `[i:num; j]`] RDT_PARTIAL_CS) THEN
      ASM_REWRITE_TAC[iterated_partial] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VSUM_0; VECTOR_SUB_REFL];
    ALL_TAC] THEN
  (* the decomposition of the integrand *)
  SUBGOAL_THEN
   `rdt_int U (\y. &2 * (iterated_partial l (u:real^N->real^Q) y dot
                         iterated_partial l (\y. pde_lop0 A B C0 u y + (Fo:real^N->real^Q) y) y)) =
    rdt_int U (\y. &2 * (iterated_partial l u y dot
                         vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                           (\j. (A:real^N->real^N^N) y$i$j %
                                partial_derivative i (partial_derivative j (iterated_partial l u))
                                  y)))) +
    rdt_int U (\y. &2 * (iterated_partial l u y dot
                         (iterated_partial l (pde_lop0 A B C0 u) y -
                          vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                           (\j. A y$i$j %
                                partial_derivative i (partial_derivative j (iterated_partial l u))
                                  y))))) +
    rdt_int U (\y. &2 * (iterated_partial l u y dot iterated_partial l Fo y))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `rdt_int U (\y. &2 * (iterated_partial l (u:real^N->real^Q) y dot
                           vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                             (\j. (A:real^N->real^N^N) y$i$j %
                                  partial_derivative i (partial_derivative j (iterated_partial l u))
                                    y))) +
                     &2 * (iterated_partial l u y dot
                           (iterated_partial l (pde_lop0 A B C0 u) y -
                            vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                             (\j. A y$i$j %
                                  partial_derivative i (partial_derivative j (iterated_partial l u))
                                    y)))) +
                     &2 * (iterated_partial l u y dot iterated_partial l (Fo:real^N->real^Q) y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RDT_INT_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `pde_lop0 A B C0 (u:real^N->real^Q)`;
                     `Fo:real^N->real^Q`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_RADD; DOT_RSUB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`U:real^N->bool`; `K:real^N->bool`;
      `\y. &2 * (iterated_partial l (u:real^N->real^Q) y dot
                 vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                   (\j. (A:real^N->real^N^N) y$i$j %
                        partial_derivative i (partial_derivative j (iterated_partial l u)) y)))`;
      `\y. &2 * (iterated_partial l (u:real^N->real^Q) y dot
                 (iterated_partial l (pde_lop0 A B C0 u) y -
                  vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                   (\j. (A:real^N->real^N^N) y$i$j %
                        partial_derivative i (partial_derivative j (iterated_partial l u)) y))))`;
      `\y. &2 * (iterated_partial l (u:real^N->real^Q) y dot
                 iterated_partial l (Fo:real^N->real^Q) y)`] RDT_INT_ADD3) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC RDT_CS_CMUL THEN MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* the three bounds *)
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `iterated_partial l (u:real^N->real^Q)`;
                 `A:real^N->real^N^N`; `lam:real`; `M:real`; `lam / &2`] RDT_ENERGY_PRINC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `u:real^N->real^Q`;
    `\y. iterated_partial l (pde_lop0 A B C0 (u:real^N->real^Q)) y -
         vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
           (\j. (A:real^N->real^N^N) y$i$j %
                partial_derivative i (partial_derivative j (iterated_partial l u)) y))`;
    `Qf:real^N->real`; `l:num list`; `s + 1`; `c:real`; `M:real`; `Lam:real`; `eta:real`]
    RDT_ENERGY_X) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `u:real^N->real^Q`; `Fo:real^N->real^Q`;
                 `s:num`; `l:num list`; `eta:real`] RDT_ENERGY_F) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&(dimindex(:N)) pow 3 * M pow 2 / (lam / &2) =
                &2 * &(dimindex(:N)) pow 3 * M pow 2 / lam` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Positivity of sums and products of nonnegative terms. *)

let RDT_NN_TAC =
  REPEAT((MATCH_MP_TAC REAL_LE_ADD ORELSE MATCH_MP_TAC REAL_LE_MUL ORELSE
          MATCH_MP_TAC REAL_LE_DIV) THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LE_POW_2;
               PDE_JETN_POS; NORM_POS_LE];;

(* The sum over the index lists of length at most s.                        *)

let RDT_ENERGY_ABS = prove
 (`!s lam M c.
     &0 < lam /\ &0 <= M /\ &0 <= c
     ==> ?C. &0 <= C /\
             !U K (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q)
              (u:real^N->real^Q) Fo (Qf:real^N->real) Lam.
               open U /\ compact K /\ K SUBSET U /\
               smooth_map_on U (\x. vectorize(A x)) /\
               (!i. smooth_map_on U (\x. vectorize(B x i))) /\
               smooth_map_on U (\x. vectorize(C0 x)) /\
               smooth_map_on U u /\ smooth_map_on U Fo /\
               (!y. y IN U /\ ~(y IN K) ==> u y = vec 0 /\ Fo y = vec 0) /\
               (!y w. y IN K ==> lam * norm w pow 2 <= w dot (A y ** w)) /\
               (!y. y IN K ==> pde_jetn 1 (\x. vectorize(A x)) y <= M) /\
               (\y. lift(Qf y)) continuous_on K /\ &0 <= Lam /\
               (!y. y IN K ==> &0 <= Qf y) /\
               (!l y. l IN pde_index_lists s (:N) /\ y IN K
                      ==> norm(iterated_partial l (pde_lop0 A B C0 u) y -
                               vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                                 (\j. A y$i$j %
                                      partial_derivative i (partial_derivative j
                                        (iterated_partial l u)) y)))
                          <= c * (M * pde_jetn (s + 1) u y + Qf y * Lam))
               ==> sum (pde_index_lists s (:N))
                     (\l. rdt_int U (\y. &2 * (iterated_partial l u y dot
                                               iterated_partial l
                                                 (\y. pde_lop0 A B C0 u y + Fo y) y)))
                   <= --(lam / &2) * rdt_hs U (s + 1) u +
                      C * (rdt_hs U s u + Lam pow 2 * drop(integral K (\y. lift(Qf y pow 2))) +
                           rdt_hs U (s - 1) Fo)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Ns = &(CARD(pde_index_lists s (:N)))` THEN
  SUBGOAL_THEN `&0 <= Ns` ASSUME_TAC THENL
   [EXPAND_TAC "Ns" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  ABBREV_TAC `eta = lam / (&2 * Ns + &2)` THEN
  SUBGOAL_THEN `eta * (&2 * Ns + &2) = lam` ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eta` ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * Ns * eta <= lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `E1 = &2 * &(dimindex(:N)) pow 3 * M pow 2 / lam +
                   &(CARD(pde_index_lists (s + 1) (:N))) * ((c * M) pow 2 / eta) + &1` THEN
  SUBGOAL_THEN `&0 <= E1` ASSUME_TAC THENL [EXPAND_TAC "E1" THEN RDT_NN_TAC; ALL_TAC] THEN
  EXISTS_TAC `&3 / &2 * lam + Ns + E1 + Ns * c pow 2 + Ns * (&1 + inv eta)` THEN
  CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (pde_index_lists s (:N))
      (\l. --(&3 / &2 * lam) *
           sum(1..dimindex(:N))
             (\i. rdt_int U (\y. norm(partial_derivative i (iterated_partial l (u:real^N->real^Q))
                                        y) pow 2)) +
           &2 * eta * rdt_hs U (s + 1) u +
           E1 * rdt_int U (\y. norm(iterated_partial l u y) pow 2) +
           rdt_hs U s u +
           (c * Lam) pow 2 * drop(integral K (\y. lift((Qf:real^N->real) y pow 2))) +
           (&1 + inv eta) * rdt_hs U (s - 1) (Fo:real^N->real^Q))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    EXPAND_TAC "E1" THEN MATCH_MP_TAC RDT_ENERGY_ONE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; PDE_INDEX_LISTS_FINITE; SUM_LMUL; SUM_CONST] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM rdt_hs] THEN
  (* the dissipation *)
  SUBGOAL_THEN
   `sum (pde_index_lists s (:N))
      (\l. sum(1..dimindex(:N))
             (\i. rdt_int U (\y. norm(partial_derivative i (iterated_partial l (u:real^N->real^Q))
                                        y) pow 2))) =
    rdt_hs U (s + 1) u - rdt_int U (\y. norm(u y) pow 2)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `u:real^N->real^Q`; `s:num`]
      RDT_HS_SUC) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ADD1] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ARITH `(c + b) - c:real = b`] THEN
    MP_TAC(ISPECL [`\(l:num list) (i:num).
                      rdt_int U (\y. norm(partial_derivative i (iterated_partial l (u:real^N->real^Q))
                                           y) pow 2)`;
                   `pde_index_lists s (:N)`; `1..dimindex(:N)`] SUM_SWAP) THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE; FINITE_NUMSEG];
    ALL_TAC] THEN
  (* the facts for the final arithmetic *)
  SUBGOAL_THEN `(!y. y IN U /\ ~(y IN K) ==> (u:real^N->real^Q) y = vec 0) /\
                (!y. y IN U /\ ~(y IN K) ==> (Fo:real^N->real^Q) y = vec 0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= rdt_hs U s (u:real^N->real^Q) /\ &0 <= rdt_hs U (s + 1) u /\
    &0 <= rdt_hs U (s - 1) (Fo:real^N->real^Q) /\
    &0 <= rdt_int U (\y. norm(u y) pow 2) /\
    rdt_int U (\y. norm(u y) pow 2) <= rdt_hs U s u /\
    &0 <= drop(integral K (\y. lift((Qf:real^N->real) y pow 2)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RDT_HS_POS THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RDT_HS_POS THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RDT_HS_POS THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `u:real^N->real^Q`; `[]:num list`]
        RDT_HS_TERM_POS) THEN
      ASM_REWRITE_TAC[iterated_partial];
      MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `u:real^N->real^Q`; `s:num`;
                     `[]:num list`] RDT_HS_TERM_LE) THEN
      ASM_REWRITE_TAC[iterated_partial; LENGTH; ALL; LE_0];
      REWRITE_TAC[GSYM LIFT_DROP] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
       [MATCH_MP_TAC RDT_INTK_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
        REWRITE_TAC[REAL_LE_POW_2]]];
    ALL_TAC] THEN
  ABBREV_TAC `H0 = rdt_hs U s (u:real^N->real^Q)` THEN
  ABBREV_TAC `H1 = rdt_hs U (s + 1) (u:real^N->real^Q)` THEN
  ABBREV_TAC `HF = rdt_hs U (s - 1) (Fo:real^N->real^Q)` THEN
  ABBREV_TAC `T0 = rdt_int U (\y. norm((u:real^N->real^Q) y) pow 2)` THEN
  ABBREV_TAC `IQ = drop(integral K (\y. lift((Qf:real^N->real) y pow 2)))` THEN
  ABBREV_TAC `Cc = &3 / &2 * lam + Ns + E1 + Ns * c pow 2 + Ns * (&1 + inv eta)` THEN
  SUBGOAL_THEN `(&2 * Ns * eta) * H1 <= lam * H1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Ns * c pow 2 /\ &0 <= Ns * (&1 + inv eta) /\ &0 <= Lam pow 2 * IQ`
  STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN RDT_NN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&3 / &2 * lam + Ns + E1) * H0 <= Cc * H0 /\
    (Ns * c pow 2) * (Lam pow 2 * IQ) <= Cc * (Lam pow 2 * IQ) /\
    (Ns * (&1 + inv eta)) * HF <= Cc * HF`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Cc" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &2 * lam) * T0 <= (&3 / &2 * lam) * H0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(&2 * Ns * eta) * H1 <= lam * H1`; `(&3 / &2 * lam + Ns + E1) * H0 <= Cc * H0`;
    `(Ns * c pow 2) * (Lam pow 2 * IQ) <= Cc * (Lam pow 2 * IQ)`;
    `(Ns * (&1 + inv eta)) * HF <= Cc * HF`; `(&3 / &2 * lam) * T0 <= (&3 / &2 * lam) * H0`] THEN
  REAL_ARITH_TAC);;

(* The jet sum of the three coefficients of pde_lop0.                       *)

let rdt_cjet = new_definition
 `rdt_cjet m (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C:real^N->real^Q^Q) (y:real^N) =
    pde_jetn m (\x. vectorize(A x)) y +
    sum(1..dimindex(:N)) (\i. pde_jetn m (\x. vectorize(B x i)) y) +
    pde_jetn m (\x. vectorize(C x)) y`;;

let RDT_CJET_POS = prove
 (`!m (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C:real^N->real^Q^Q) y.
     &0 <= rdt_cjet m A B C y`,
  REWRITE_TAC[rdt_cjet] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[PDE_JETN_POS] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[PDE_JETN_POS] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[PDE_JETN_POS]);;

let RDT_CJET_MONO = prove
 (`!m m' (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C:real^N->real^Q^Q) y.
     m <= m' ==> rdt_cjet m A B C y <= rdt_cjet m' A B C y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_cjet] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[PDE_JETN_MONO] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[PDE_JETN_MONO] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[PDE_JETN_MONO]);;

let RDT_CJET_A = prove
 (`!m (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C:real^N->real^Q^Q) y.
     pde_jetn m (\x. vectorize(A x)) y <= rdt_cjet m A B C y`,
  REWRITE_TAC[rdt_cjet] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ &0 <= c ==> a <= a + b + c`) THEN
  SIMP_TAC[PDE_JETN_POS; SUM_POS_LE_NUMSEG]);;

let RDT_CJET_CONT = prove
 (`!U K (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C:real^N->real^Q^Q) m.
     open U /\ K SUBSET U /\ smooth_map_on U (\x. vectorize(A x)) /\
     (!i. smooth_map_on U (\x. vectorize(B x i))) /\ smooth_map_on U (\x. vectorize(C x))
     ==> (\y. lift(rdt_cjet m A B C y)) continuous_on K`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_cjet; LIFT_ADD; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC RDT_JETN_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC RDT_JETN_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RDT_JETN_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let RDT_LOP0_COMM_CJET = prove
 (`!l U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C:real^N->real^Q^Q) (u:real^N->real^Q) x.
     open U /\ smooth_map_on U (\x. vectorize(A x)) /\
     (!i. smooth_map_on U (\x. vectorize(B x i))) /\ smooth_map_on U (\x. vectorize(C x)) /\
     smooth_map_on U u /\ x IN U /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> norm(iterated_partial l (pde_lop0 A B C u) x -
              vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                (\j. A x$i$j % partial_derivative i (partial_derivative j (iterated_partial l u)) x))) <=
         &(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) *
         (&2 pow (LENGTH l) * &(LENGTH l + 1) *
          (rdt_cjet (LENGTH l DIV 2 + 1) A B C x * pde_jetn (LENGTH l + 1) u x +
           rdt_cjet (LENGTH l) A B C x * pde_jetn (LENGTH l DIV 2 + 2) u x))`,
  REWRITE_TAC[rdt_cjet; RDT_LOP0_COMM_BOUND]);;

(* The tame chart energy for s >= 2N+4: the remainder X_l from              *)
(* RDT_LOP0_COMM_CJET, the high jets of u by Sobolev (RDT_SOBOLEV_JETN).    *)

let RDT_CHART_ENERGY = prove
 (`!(K:real^N->bool) s lam M Qb.
     compact K /\ 2 * dimindex(:N) + 4 <= s /\ &0 < lam /\ &0 <= M /\ &0 <= Qb
     ==> ?C. &0 <= C /\
             !U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q)
              (u:real^N->real^Q) Fo.
               open U /\ K SUBSET U /\
               smooth_map_on U (\x. vectorize(A x)) /\
               (!i. smooth_map_on U (\x. vectorize(B x i))) /\
               smooth_map_on U (\x. vectorize(C0 x)) /\
               smooth_map_on U u /\ smooth_map_on U Fo /\
               (!y. y IN U /\ ~(y IN K) ==> u y = vec 0 /\ Fo y = vec 0) /\
               (!y w. y IN K ==> lam * norm w pow 2 <= w dot (A y ** w)) /\
               (!y. y IN K ==> rdt_cjet (s DIV 2 + 1) A B C0 y <= M) /\
               drop(integral K (\y. lift(rdt_cjet s A B C0 y pow 2))) <= Qb
               ==> sum (pde_index_lists s (:N))
                     (\l. rdt_int U (\y. &2 * (iterated_partial l u y dot
                                               iterated_partial l
                                                 (\y. pde_lop0 A B C0 u y + Fo y) y)))
                   <= --(lam / &2) * rdt_hs U (s + 1) u +
                      C * (rdt_hs U s u + rdt_hs U (s - 1) Fo)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `s DIV 2 + 2`] RDT_SOBOLEV_JETN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CS:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sob"))) THEN
  ABBREV_TAC `c = &(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow s * &(s + 1))` THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL [EXPAND_TAC "c" THEN RDT_NN_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:num`; `lam:real`; `M:real`; `c:real`] RDT_ENERGY_ABS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "abs"))) THEN
  EXISTS_TAC `C1 * (&1 + CS * Qb)` THEN CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!y. y IN U /\ ~(y IN K) ==> (u:real^N->real^Q) y = vec 0) /\
                (!y. y IN U /\ ~(y IN K) ==> (Fo:real^N->real^Q) y = vec 0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rdt_hs U s (u:real^N->real^Q) /\ &0 <= rdt_hs U (s - 1) (Fo:real^N->real^Q)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RDT_HS_POS THEN EXISTS_TAC `K:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Lam = sqrt(CS * rdt_hs U s (u:real^N->real^Q))` THEN
  SUBGOAL_THEN `&0 <= Lam /\ Lam pow 2 = CS * rdt_hs U s (u:real^N->real^Q)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Lam" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE; MATCH_MP_TAC SQRT_POW_2] THEN RDT_NN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dimindex(:N) + s DIV 2 + 2 <= s` ASSUME_TAC THENL
   [MP_TAC(SPECL [`s:num`; `2`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN K ==> pde_jetn (s DIV 2 + 2) (u:real^N->real^Q) y <= Lam`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "Lam" THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CS * rdt_hs U (dimindex(:N) + s DIV 2 + 2) (u:real^N->real^Q)` THEN
    CONJ_TAC THENL
     [USE_THEN "sob" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_HS_MONO THEN
      EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the bound of the remainders *)
  SUBGOAL_THEN
   `!l y. l IN pde_index_lists s (:N) /\ y IN K
          ==> norm(iterated_partial l (pde_lop0 A B C0 (u:real^N->real^Q)) y -
                   vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                     (\j. (A:real^N->real^N^N) y$i$j %
                          partial_derivative i (partial_derivative j (iterated_partial l u)) y)))
              <= c * (M * pde_jetn (s + 1) u y + rdt_cjet s A B C0 y * Lam)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `A:real^N->real^N^N`;
                   `B:real^N->num->real^Q^Q`; `C0:real^N->real^Q^Q`; `u:real^N->real^Q`;
                   `y:real^N`] RDT_LOP0_COMM_CJET) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    SUBGOAL_THEN `LENGTH(l:num list) DIV 2 <= s DIV 2` ASSUME_TAC THENL
     [MATCH_MP_TAC DIV_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `n = LENGTH(l:num list)` THEN
    SUBGOAL_THEN
     `&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow n * &(n + 1)) <= c`
    ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `rdt_cjet (n DIV 2 + 1) A B C0 y * pde_jetn (n + 1) (u:real^N->real^Q) y <=
      M * pde_jetn (s + 1) u y /\
      rdt_cjet n (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y *
      pde_jetn (n DIV 2 + 2) u y <= rdt_cjet s A B C0 y * Lam`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[RDT_CJET_POS; PDE_JETN_POS] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rdt_cjet (s DIV 2 + 1)
          (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC RDT_CJET_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC RDT_CJET_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn (s DIV 2 + 2) (u:real^N->real^Q) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow n * &(n + 1))) *
                (M * pde_jetn (s + 1) (u:real^N->real^Q) y +
                 rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                          (C0:real^N->real^Q^Q) y * Lam)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[RDT_CJET_POS; PDE_JETN_POS]];
    ALL_TAC] THEN
  USE_THEN "abs" (MP_TAC o SPECL
   [`U:real^N->bool`; `K:real^N->bool`; `A:real^N->real^N^N`; `B:real^N->num->real^Q^Q`;
    `C0:real^N->real^Q^Q`; `u:real^N->real^Q`; `Fo:real^N->real^Q`;
    `\y. rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y`;
    `Lam:real`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RDT_CJET_POS; ETA_AX] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `rdt_cjet (s DIV 2 + 1) (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                           (C0:real^N->real^Q^Q) y` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `rdt_cjet 1 (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                           (C0:real^N->real^Q^Q) y` THEN
      REWRITE_TAC[RDT_CJET_A] THEN MATCH_MP_TAC RDT_CJET_MONO THEN ARITH_TAC;
      MATCH_MP_TAC RDT_CJET_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `IQ = drop(integral K (\y. lift(rdt_cjet s (A:real^N->real^N^N)
                         (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y pow 2)))` THEN
  ABBREV_TAC `H0 = rdt_hs U s (u:real^N->real^Q)` THEN
  ABBREV_TAC `HF = rdt_hs U (s - 1) (Fo:real^N->real^Q)` THEN
  SUBGOAL_THEN `(CS * H0) * IQ <= (CS * Qb) * H0` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(CS * H0) * IQ = (CS * H0) * IQ /\ (CS * Qb) * H0 = (CS * H0) * Qb`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN RDT_NN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= CS * Qb` ASSUME_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (CS * Qb) * HF` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `C1 * (H0 + (CS * H0) * IQ + HF) <= C1 * ((&1 + CS * Qb) * (H0 + HF))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(CS * H0) * IQ <= (CS * Qb) * H0`; `&0 <= (CS * Qb) * HF`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_ASSOC]]);;

(* The level-0 chart energy of pde_lop0 alone (for differences).            *)

let RDT_HS_ZERO_FUN = prove
 (`!U s. rdt_hs U s (\y:real^N. vec 0:real^Q) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rdt_hs; rdt_int] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[TEXT_ITERATED_PARTIAL_ZERO] THEN
  REWRITE_TAC[NORM_0; LIFT_NUM; REAL_POW_ZERO; ARITH_EQ; INTEGRAL_0; DROP_VEC]);;

let RDT_CHART_ENERGY0 = prove
 (`!(K:real^N->bool) lam M.
     compact K /\ &0 < lam /\ &0 <= M
     ==> ?C. &0 <= C /\
             !U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q)
              (u:real^N->real^Q).
               open U /\ K SUBSET U /\
               smooth_map_on U (\x. vectorize(A x)) /\
               (!i. smooth_map_on U (\x. vectorize(B x i))) /\
               smooth_map_on U (\x. vectorize(C0 x)) /\
               smooth_map_on U u /\
               (!y. y IN U /\ ~(y IN K) ==> u y = vec 0) /\
               (!y w. y IN K ==> lam * norm w pow 2 <= w dot (A y ** w)) /\
               (!y. y IN K ==> rdt_cjet 1 A B C0 y <= M)
               ==> rdt_int U (\y. &2 * (u y dot pde_lop0 A B C0 u y))
                   <= --(lam / &2) * rdt_hs U 1 u + C * rdt_hs U 0 u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `lam:real`; `M:real`; `&1`] RDT_ENERGY_ABS) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "abs"))) THEN
  EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "abs" (MP_TAC o SPECL
   [`U:real^N->bool`; `K:real^N->bool`; `A:real^N->real^N^N`; `B:real^N->num->real^Q^Q`;
    `C0:real^N->real^Q^Q`; `u:real^N->real^Q`; `\y:real^N. vec 0:real^Q`;
    `\y:real^N. &0`; `&0`]) THEN
  REWRITE_TAC[PDE_INDEX_LISTS_0; IN_SING; SUM_SING; iterated_partial; VECTOR_ADD_RID;
              RDT_HS_ZERO_FUN; REAL_MUL_RZERO; REAL_ADD_RID; REAL_LE_REFL; ADD_CLAUSES;
              SMOOTH_MAP_ON_CONST; CONTINUOUS_ON_CONST; REAL_POW_ZERO; ARITH_EQ;
              REAL_MUL_LZERO; ETA_AX] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `rdt_cjet 1 (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                           (C0:real^N->real^Q^Q) y` THEN
      ASM_SIMP_TAC[RDT_CJET_A];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    REWRITE_TAC[iterated_partial; pde_lop0; REAL_MUL_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `(a + b + c) - a:real^N = b + c`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `rdt_cjet 1 (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                         (C0:real^N->real^Q^Q) y * pde_jetn 1 (u:real^N->real^Q) y` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[PDE_JETN_POS]] THEN
    REWRITE_TAC[rdt_cjet] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N))
                  (\i. norm((B:real^N->num->real^Q^Q) y i ** partial_derivative i u y)) +
                norm((C0:real^N->real^Q^Q) y ** (u:real^N->real^Q) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH `norm(a:real^N) <= x /\ norm(b) <= y ==> norm(a + b) <= x + y`) THEN
      SIMP_TAC[VSUM_NORM; FINITE_NUMSEG; REAL_LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!(M0:real^Q^Q) (w:real^Q) j. norm w <= j ==> norm(M0 ** w) <= norm(vectorize M0) * j`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(vectorize(M0:real^Q^Q)) * norm(w:real^Q)` THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`vectorize(M0:real^Q^Q)`; `w:real^Q`] PDE_MATRIFY_MUL_NORM) THEN
        REWRITE_TAC[MATRIFY_VECTORIZE];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(!i. norm(partial_derivative i (u:real^N->real^Q) y) <= pde_jetn 1 u y \/
           ~(1 <= i /\ i <= dimindex(:N))) /\
      norm((u:real^N->real^Q) y) <= pde_jetn 1 u y`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
      [GEN_TAC THEN ASM_CASES_TAC `1 <= i /\ i <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
       MP_TAC(ISPECL [`1`; `u:real^N->real^Q`; `[i:num]`; `y:real^N`] RDT_NORM_LE_JETN) THEN
       ASM_REWRITE_TAC[LENGTH; ALL; iterated_partial; ARITH_RULE `SUC 0 <= 1`];
       MP_TAC(ISPECL [`1`; `u:real^N->real^Q`; `[]:num list`; `y:real^N`] RDT_NORM_LE_JETN) THEN
       REWRITE_TAC[LENGTH; ALL; iterated_partial; LE_0]];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= x /\ &0 <= y /\ b <= z ==> a + b <= y + x + z`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(vectorize((B:real^N->num->real^Q^Q) y i)) * pde_jetn 1 (u:real^N->real^Q) y` THEN
      CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[PDE_JETN_POS] THEN
        MP_TAC(ISPECL [`1`; `\x. vectorize((B:real^N->num->real^Q^Q) x i)`; `[]:num list`;
                       `y:real^N`] RDT_NORM_LE_JETN) THEN
        REWRITE_TAC[LENGTH; ALL; iterated_partial; LE_0]];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PDE_JETN_POS];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(vectorize((C0:real^N->real^Q^Q) y)) * pde_jetn 1 (u:real^N->real^Q) y` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[PDE_JETN_POS] THEN
      MP_TAC(ISPECL [`1`; `\x. vectorize((C0:real^N->real^Q^Q) x)`; `[]:num list`;
                     `y:real^N`] RDT_NORM_LE_JETN) THEN
      REWRITE_TAC[LENGTH; ALL; iterated_partial; LE_0]];
    ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN SIMP_TAC[REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The cut-off commutator pde_mt_comm A B p W (pc_pde_mtor) as               *)
(* an operator pde_lop0 with zero principal part (coefficients rdt_cdd,     *)
(* rdt_cee built from A, B and the derivatives of p); jets of the new       *)
(* coefficients, and the H^(s-1) bound of the commutator by H^s of W.       *)
(* ------------------------------------------------------------------------- *)

(* Leibniz with the jets of the first factor bounded at the point.          *)

let RDT_JETN_BILINEAR_BOUNDED = prove
 (`!(bb:real^P->real^Q->real^K) M m (U:real^N->bool) f g x Af.
     bilinear bb /\ (!x y. norm(bb x y) <= M * norm x * norm y) /\ &0 <= M /\
     open U /\ smooth_map_on U f /\ smooth_map_on U g /\ x IN U /\
     pde_jetn m f x <= Af
     ==> pde_jetn m (\x. bb (f x) (g x)) x <=
         &(CARD(pde_index_lists m (:N))) * (&2 pow m * M * &(m + 1) * Af) * pde_jetn m g x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Af` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDE_JETN_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [pde_jetn] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists m (:N))
                (\l:num list. (&2 pow m * M * &(m + 1) * Af) * pde_jetn m (g:real^N->real^Q) x)` THEN
  CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[SUM_CONST; PDE_INDEX_LISTS_FINITE; REAL_MUL_ASSOC; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`bb:real^P->real^Q->real^K`; `M:real`] RDT_LEIBNIZ_JET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num list`; `U:real^N->bool`; `f:real^N->real^P`;
                             `g:real^N->real^Q`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 pow m * M * (&(LENGTH(l:num list) + 1) *
                               (Af * pde_jetn m (g:real^N->real^Q) x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      SIMP_TAC[REAL_LE_MUL; PDE_JETN_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..LENGTH(l:num list)) (\k. Af * pde_jetn m (g:real^N->real^Q) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[PDE_JETN_POS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_jetn m (f:real^N->real^P) x` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; REAL_LE_REFL]];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; PDE_JETN_POS; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;

(* The coefficients of the commutator as an operator with zero principal    *)
(* part.                                                                     *)

let rdt_cdd = new_definition
 `rdt_cdd (A:real^N->real^N^N) (p:real^N->real^1) (z:real^N) (j:num) =
    (matrify:real^(Q,Q)finite_prod->real^Q^Q)
    (vsum(1..dimindex(:N))
      (\i. (drop(partial_derivative i p z) * (A z$i$j + A z$j$i)) %
           vectorize(mat 1:real^Q^Q)))`;;

let rdt_cee = new_definition
 `rdt_cee (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (p:real^N->real^1) (z:real^N) =
    (matrify:real^(Q,Q)finite_prod->real^Q^Q)
    (vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
       (\j. (A z$i$j * drop(partial_derivative i (partial_derivative j p) z)) %
            vectorize(mat 1:real^Q^Q))) +
     vsum(1..dimindex(:N)) (\i. drop(partial_derivative i p z) % vectorize(B z i)))`;;

let RDT_MATRIFY_VSUM_MUL = prove
 (`!(f:A->real^(Q,Q)finite_prod) s (w:real^Q).
     FINITE s ==> (matrify(vsum s f):real^Q^Q) ** w = vsum s (\i. matrify(f i) ** w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real^(Q,Q)finite_prod. (matrify v:real^Q^Q) ** w`;
                 `f:A->real^(Q,Q)finite_prod`; `s:A->bool`] LINEAR_VSUM) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_LMUL]);;

let RDT_COMM_APART = prove
 (`!n (a:num->num->real) (d:num->real) (e:num->num->real) (X:num->real^Q) (Y:real^Q).
     vsum(1..n) (\i. vsum(1..n) (\j. a i j % (d i % X j + d j % X i + e i j % Y))) =
     vsum(1..n) (\i. vsum(1..n) (\k. (d k * (a k i + a i k)) % X i)) +
     vsum(1..n) (\i. vsum(1..n) (\j. (a i j * e i j) % Y))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_ADD_LDISTRIB; VECTOR_ADD_RDISTRIB] THEN
  SIMP_TAC[VSUM_ADD_NUMSEG; FINITE_NUMSEG] THEN
  SUBGOAL_THEN `vsum(1..n) (\i. vsum(1..n) (\j. (a i j * d i) % (X:num->real^Q) j)) =
                vsum(1..n) (\i. vsum(1..n) (\k. (d k * a k i) % X i))` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [VSUM_SWAP_NUMSEG] THEN REWRITE_TAC[REAL_MUL_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `vsum(1..n) (\i. vsum(1..n) (\j. (a i j * d j) % (X:num->real^Q) i)) =
                vsum(1..n) (\i. vsum(1..n) (\k. (d k * a i k) % X i))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_SYM]; ALL_TAC] THEN
  VECTOR_ARITH_TAC);;

let RDT_COMM_LOP0 = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^Q^Q) p (W:real^N->real^Q) z.
     pde_mt_comm A B p W z =
     pde_lop0 (\z. mat 0) (rdt_cdd A p) (rdt_cee A B p) W z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_mt_comm; pde_lop0; rdt_cdd; rdt_cee] THEN
  REWRITE_TAC[MAT_0_COMPONENT; VECTOR_MUL_LZERO; VSUM_0; VECTOR_ADD_LID] THEN
  SIMP_TAC[RDT_MATRIFY_VSUM_MUL; FINITE_NUMSEG; MATRIFY_ADD; MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN
  REWRITE_TAC[MATRIFY_CMUL; MATRIFY_VECTORIZE; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `\i j. (A:real^N->real^N^N) z$i$j`;
                 `\i. drop(partial_derivative i (p:real^N->real^1) z)`;
                 `\i j. drop(partial_derivative i (partial_derivative j (p:real^N->real^1)) z)`;
                 `\i. partial_derivative i (W:real^N->real^Q) z`; `(W:real^N->real^Q) z`]
    RDT_COMM_APART) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_MUL_SYM; REAL_ADD_SYM; VECTOR_ADD_ASSOC]);;

(* The bilinear pieces of the commutator coefficients.                      *)

let RDT_BB_D = prove
 (`!i j. bilinear (\(x:real^1) (v:real^(N,N)finite_prod).
                     (drop x * ((matrify v:real^N^N)$i$j + (matrify v)$j$i)) %
                     vectorize(mat 1:real^Q^Q)) /\
         !x v. norm((\(x:real^1) (v:real^(N,N)finite_prod).
                       (drop x * ((matrify v:real^N^N)$i$j + (matrify v)$j$i)) %
                       vectorize(mat 1:real^Q^Q)) x v) <=
               (&2 * norm(vectorize(mat 1:real^Q^Q))) * norm x * norm v`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[bilinear; linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT;
                MATRIX_CMUL_COMPONENT; DROP_ADD; DROP_CMUL] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs((matrify v:real^N^N)$i$j + (matrify v)$j$i) <=
                  &2 * norm(v:real^(N,N)finite_prod)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`v:real^(N,N)finite_prod`; `i:num`; `j:num`] PDE_MATRIFY_ENTRY_LE) THEN
      MP_TAC(ISPECL [`v:real^(N,N)finite_prod`; `j:num`; `i:num`] PDE_MATRIFY_ENTRY_LE) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; ABS_DROP] THEN
    REWRITE_TAC[REAL_ARITH `(&2 * a) * b * c = (b * (&2 * c)) * a`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]]);;

let RDT_BB_E1 = prove
 (`!i j. bilinear (\(x:real^1) (v:real^(N,N)finite_prod).
                     ((matrify v:real^N^N)$i$j * drop x) % vectorize(mat 1:real^Q^Q)) /\
         !x v. norm((\(x:real^1) (v:real^(N,N)finite_prod).
                       ((matrify v:real^N^N)$i$j * drop x) % vectorize(mat 1:real^Q^Q)) x v) <=
               norm(vectorize(mat 1:real^Q^Q)) * norm x * norm v`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[bilinear; linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT;
                MATRIX_CMUL_COMPONENT; DROP_ADD; DROP_CMUL] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`v:real^(N,N)finite_prod`; `i:num`; `j:num`] PDE_MATRIFY_ENTRY_LE) THEN
    DISCH_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; ABS_DROP] THEN
    REWRITE_TAC[REAL_ARITH `a * b * c = (b * c) * a`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[NORM_POS_LE]]);;

let RDT_BB_E2 = prove
 (`bilinear (\(x:real^1) (v:real^(Q,Q)finite_prod). drop x % v) /\
   !x v. norm((\(x:real^1) (v:real^(Q,Q)finite_prod). drop x % v) x v) <= &1 * norm x * norm v`,
  CONJ_TAC THENL
   [REWRITE_TAC[bilinear; linear; DROP_ADD; DROP_CMUL] THEN REPEAT STRIP_TAC THEN
    VECTOR_ARITH_TAC;
    REWRITE_TAC[NORM_MUL; ABS_DROP; REAL_MUL_LID; REAL_LE_REFL]]);;

(* Smoothness of the commutator coefficients.                               *)

let RDT_COMM_COEFF_SMOOTH = prove
 (`!U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (p:real^N->real^1).
     open U /\ smooth_map_on U (\x. vectorize(A x)) /\
     (!i. smooth_map_on U (\x. vectorize(B x i))) /\ smooth_map_on U p
     ==> smooth_map_on U (\x. vectorize((\z:real^N. mat 0:real^N^N) x)) /\
         (!j. smooth_map_on U (\x. vectorize(rdt_cdd A p x j:real^Q^Q))) /\
         smooth_map_on U (\x. vectorize(rdt_cee A B p x))`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    REWRITE_TAC[rdt_cdd; VECTORIZE_MATRIFY] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `\(x:real^1) (v:real^(N,N)finite_prod).
                       (drop x * ((matrify v:real^N^N)$i$j + (matrify v)$j$i)) %
                       vectorize(mat 1:real^Q^Q)`;
                   `partial_derivative i (p:real^N->real^1)`;
                   `\x. vectorize((A:real^N->real^N^N) x)`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_SIMP_TAC[RDT_BB_D; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; MATRIFY_VECTORIZE];
    REWRITE_TAC[rdt_cee; VECTORIZE_MATRIFY] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`;
                     `\(x:real^1) (v:real^(N,N)finite_prod).
                         ((matrify v:real^N^N)$i$j * drop x) % vectorize(mat 1:real^Q^Q)`;
                     `partial_derivative i (partial_derivative j (p:real^N->real^1))`;
                     `\x. vectorize((A:real^N->real^N^N) x)`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[RDT_BB_E1; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; MATRIFY_VECTORIZE];
      MP_TAC(ISPECL [`U:real^N->bool`;
                     `\(x:real^1) (v:real^(Q,Q)finite_prod). drop x % v`;
                     `partial_derivative i (p:real^N->real^1)`;
                     `\x. vectorize((B:real^N->num->real^Q^Q) x i)`]
        SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[RDT_BB_E2; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]]]);;

(* Jets of the commutator coefficients: linear in the jets of A and B, with  *)
(* the jets of p up to order m + 2 as a factor.                             *)

let RDT_P_JETS = prove
 (`!m (p:real^N->real^1) z Ap.
     pde_jetn (m + 2) p z <= Ap
     ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> pde_jetn m (partial_derivative i p) z <= Ap) /\
         (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                ==> pde_jetn m (partial_derivative i (partial_derivative j p)) z <= Ap)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `pde_jetn (SUC m) (p:real^N->real^1) z` THEN ASM_SIMP_TAC[PDE_JETN_PARTIAL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_jetn (m + 2) (p:real^N->real^1) z` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC;
    EXISTS_TAC `pde_jetn (SUC m) (partial_derivative j (p:real^N->real^1)) z` THEN
    ASM_SIMP_TAC[PDE_JETN_PARTIAL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (SUC(SUC m)) (p:real^N->real^1) z` THEN ASM_SIMP_TAC[PDE_JETN_PARTIAL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_jetn (m + 2) (p:real^N->real^1) z` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC]);;

let RDT_CDD_JETN = prove
 (`!m U (A:real^N->real^N^N) (p:real^N->real^1) z Ap j.
     open U /\ smooth_map_on U (\x. vectorize(A x)) /\ smooth_map_on U p /\ z IN U /\
     pde_jetn (m + 2) p z <= Ap
     ==> pde_jetn m (\x. vectorize(rdt_cdd A p x j:real^Q^Q)) z <=
         &(dimindex(:N)) *
         ((&(CARD(pde_index_lists m (:N))) * &2 pow m * &(m + 1)) *
          (&2 * norm(vectorize(mat 1:real^Q^Q))) * Ap) *
         pde_jetn m (\x. vectorize(A x)) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `p:real^N->real^1`; `z:real^N`; `Ap:real`]
    RDT_P_JETS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rdt_cdd; VECTORIZE_MATRIFY] THEN
  MP_TAC(ISPECL [`m:num`; `U:real^N->bool`; `1..dimindex(:N)`;
    `\i x. (drop(partial_derivative i (p:real^N->real^1) x) *
            ((A:real^N->real^N^N) x$i$j + A x$j$i)) % vectorize(mat 1:real^Q^Q)`; `z:real^N`] P2CT_JETN_VSUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `\(x:real^1) (v:real^(N,N)finite_prod).
                       (drop x * ((matrify v:real^N^N)$i$j + (matrify v)$j$i)) %
                       vectorize(mat 1:real^Q^Q)`;
                   `partial_derivative i (p:real^N->real^1)`;
                   `\x. vectorize((A:real^N->real^N^N) x)`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_SIMP_TAC[RDT_BB_D; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; MATRIFY_VECTORIZE; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                (\i. ((&(CARD(pde_index_lists m (:N))) * &2 pow m * &(m + 1)) *
                      (&2 * norm(vectorize(mat 1:real^Q^Q))) * Ap) *
                     pde_jetn m (\x. vectorize((A:real^N->real^N^N) x)) z)` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\(x:real^1) (v:real^(N,N)finite_prod).
                    (drop x * ((matrify v:real^N^N)$i$j + (matrify v)$j$i)) %
                    vectorize(mat 1:real^Q^Q)`;
                 `&2 * norm(vectorize(mat 1:real^Q^Q))`; `m:num`; `U:real^N->bool`;
                 `partial_derivative i (p:real^N->real^1)`;
                 `\x. vectorize((A:real^N->real^N^N) x)`; `z:real^N`; `Ap:real`]
    RDT_JETN_BILINEAR_BOUNDED) THEN
  ASM_SIMP_TAC[RDT_BB_D; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; MATRIFY_VECTORIZE; NORM_POS_LE;
               REAL_LE_MUL; REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> a <= x ==> a <= y`) THEN REAL_ARITH_TAC);;

let RDT_CEE_JETN = prove
 (`!m U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (p:real^N->real^1) z Ap.
     open U /\ smooth_map_on U (\x. vectorize(A x)) /\
     (!i. smooth_map_on U (\x. vectorize(B x i))) /\ smooth_map_on U p /\ z IN U /\
     pde_jetn (m + 2) p z <= Ap
     ==> pde_jetn m (\x. vectorize(rdt_cee A B p x)) z <=
         &(dimindex(:N)) * &(dimindex(:N)) *
         ((&(CARD(pde_index_lists m (:N))) * &2 pow m * &(m + 1)) *
          norm(vectorize(mat 1:real^Q^Q)) * Ap) *
         pde_jetn m (\x. vectorize(A x)) z +
         ((&(CARD(pde_index_lists m (:N))) * &2 pow m * &(m + 1)) * Ap) *
         sum(1..dimindex(:N)) (\i. pde_jetn m (\x. vectorize(B x i)) z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `p:real^N->real^1`; `z:real^N`; `Ap:real`]
    RDT_P_JETS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Km = &(CARD(pde_index_lists m (:N))) * &2 pow m * &(m + 1)` THEN
  SUBGOAL_THEN
   `(!i j. smooth_map_on U
             (\x. ((A:real^N->real^N^N) x$i$j *
                   drop(partial_derivative i (partial_derivative j (p:real^N->real^1)) x)) %
                  vectorize(mat 1:real^Q^Q))) /\
    (!i. smooth_map_on U
           (\x. drop(partial_derivative i (p:real^N->real^1) x) %
                vectorize((B:real^N->num->real^Q^Q) x i)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`;
                     `\(x:real^1) (v:real^(N,N)finite_prod).
                         ((matrify v:real^N^N)$i$j * drop x) % vectorize(mat 1:real^Q^Q)`;
                     `partial_derivative i (partial_derivative j (p:real^N->real^1))`;
                     `\x. vectorize((A:real^N->real^N^N) x)`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[RDT_BB_E1; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; MATRIFY_VECTORIZE];
      MP_TAC(ISPECL [`U:real^N->bool`;
                     `\(x:real^1) (v:real^(Q,Q)finite_prod). drop x % v`;
                     `partial_derivative i (p:real^N->real^1)`;
                     `\x. vectorize((B:real^N->num->real^Q^Q) x i)`]
        SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_SIMP_TAC[RDT_BB_E2; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]];
    ALL_TAC] THEN
  REWRITE_TAC[rdt_cee; VECTORIZE_MATRIFY] THEN
  MP_TAC(ISPECL [`m:num`; `U:real^N->bool`;
    `\x. vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
           (\j. ((A:real^N->real^N^N) x$i$j *
                 drop(partial_derivative i (partial_derivative j (p:real^N->real^1)) x)) %
                vectorize(mat 1:real^Q^Q)))`;
    `\x. vsum(1..dimindex(:N))
           (\i. drop(partial_derivative i (p:real^N->real^1) x) %
                vectorize((B:real^N->num->real^Q^Q) x i))`; `z:real^N`] P2CT_JETN_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `U:real^N->bool`; `1..dimindex(:N)`;
      `\i x. vsum(1..dimindex(:N))
               (\j. ((A:real^N->real^N^N) x$i$j *
                     drop(partial_derivative i (partial_derivative j (p:real^N->real^1)) x)) %
                    vectorize(mat 1:real^Q^Q))`; `z:real^N`] P2CT_JETN_VSUM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
      ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N))
                  (\i. &(dimindex(:N)) * (Km * norm(vectorize(mat 1:real^Q^Q)) * Ap) *
                       pde_jetn m (\x. vectorize((A:real^N->real^N^N) x)) z)` THEN
    CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:num`; `U:real^N->bool`; `1..dimindex(:N)`;
      `\j x. ((A:real^N->real^N^N) x$i$j *
              drop(partial_derivative i (partial_derivative j (p:real^N->real^1)) x)) %
             vectorize(mat 1:real^Q^Q)`; `z:real^N`] P2CT_JETN_VSUM) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N))
                  (\j. (Km * norm(vectorize(mat 1:real^Q^Q)) * Ap) *
                       pde_jetn m (\x. vectorize((A:real^N->real^N^N) x)) z)` THEN
    CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\(x:real^1) (v:real^(N,N)finite_prod).
                      ((matrify v:real^N^N)$i$j * drop x) % vectorize(mat 1:real^Q^Q)`;
                   `norm(vectorize(mat 1:real^Q^Q))`; `m:num`; `U:real^N->bool`;
                   `partial_derivative i (partial_derivative j (p:real^N->real^1))`;
                   `\x. vectorize((A:real^N->real^N^N) x)`; `z:real^N`; `Ap:real`]
      RDT_JETN_BILINEAR_BOUNDED) THEN
    ASM_SIMP_TAC[RDT_BB_E1; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; MATRIFY_VECTORIZE; NORM_POS_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> a <= x ==> a <= y`) THEN EXPAND_TAC "Km" THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL [`m:num`; `U:real^N->bool`; `1..dimindex(:N)`;
      `\i x. drop(partial_derivative i (p:real^N->real^1) x) %
             vectorize((B:real^N->num->real^Q^Q) x i)`; `z:real^N`] P2CT_JETN_VSUM) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\(x:real^1) (v:real^(Q,Q)finite_prod). drop x % v`;
                   `&1`; `m:num`; `U:real^N->bool`;
                   `partial_derivative i (p:real^N->real^1)`;
                   `\x. vectorize((B:real^N->num->real^Q^Q) x i)`; `z:real^N`; `Ap:real`]
      RDT_JETN_BILINEAR_BOUNDED) THEN
    ASM_SIMP_TAC[RDT_BB_E2; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; REAL_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> a <= x ==> a <= y`) THEN EXPAND_TAC "Km" THEN
    REAL_ARITH_TAC]);;

let RDT_COMM_CJET = prove
 (`!m U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q)
    (p:real^N->real^1) z Ap.
     open U /\ smooth_map_on U (\x. vectorize(A x)) /\
     (!i. smooth_map_on U (\x. vectorize(B x i))) /\ smooth_map_on U p /\ z IN U /\
     pde_jetn (m + 2) p z <= Ap
     ==> rdt_cjet m (\z. mat 0) (rdt_cdd A p) (rdt_cee A B p) z <=
         ((&(CARD(pde_index_lists m (:N))) * &2 pow m * &(m + 1)) *
          (&3 * &(dimindex(:N)) pow 2 * norm(vectorize(mat 1:real^Q^Q)) + &1)) * Ap *
         rdt_cjet m A B C0 z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Ap` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDE_JETN_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[rdt_cjet; VECTORIZE_0] THEN
  SUBGOAL_THEN `pde_jetn m (\x:real^N. vec 0:real^(N,N)finite_prod) z = &0` SUBST1_TAC THENL
   [REWRITE_TAC[pde_jetn; TEXT_ITERATED_PARTIAL_ZERO; NORM_0; SUM_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `U:real^N->bool`; `A:real^N->real^N^N`; `B:real^N->num->real^Q^Q`;
                 `p:real^N->real^1`; `z:real^N`; `Ap:real`] RDT_CEE_JETN) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. pde_jetn m (\x. vectorize(rdt_cdd (A:real^N->real^N^N) (p:real^N->real^1) x i
                                     :real^Q^Q)) z) <=
    &(dimindex(:N)) *
    (&(dimindex(:N)) *
     ((&(CARD(pde_index_lists m (:N))) * &2 pow m * &(m + 1)) *
      (&2 * norm(vectorize(mat 1:real^Q^Q))) * Ap) *
     pde_jetn m (\x. vectorize(A x)) z)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum(1..dimindex(:N))
        (\i. &(dimindex(:N)) *
             ((&(CARD(pde_index_lists m (:N))) * &2 pow m * &(m + 1)) *
              (&2 * norm(vectorize(mat 1:real^Q^Q))) * Ap) *
             pde_jetn m (\x. vectorize((A:real^N->real^N^N) x)) z)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC RDT_CDD_JETN THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= &(CARD(pde_index_lists m (:N))) * &2 pow m * &(m + 1) /\
    &0 <= norm(vectorize(mat 1:real^Q^Q)) /\
    &0 <= pde_jetn m (\x. vectorize((A:real^N->real^N^N) x)) z /\
    &0 <= sum(1..dimindex(:N)) (\i. pde_jetn m (\x. vectorize((B:real^N->num->real^Q^Q) x i)) z) /\
    &0 <= pde_jetn m (\x. vectorize((C0:real^N->real^Q^Q) x)) z /\ &0 <= &(dimindex(:N))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [RDT_NN_TAC; REWRITE_TAC[NORM_POS_LE]; REWRITE_TAC[PDE_JETN_POS];
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[PDE_JETN_POS];
      REWRITE_TAC[PDE_JETN_POS]; REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  ABBREV_TAC `Km = &(CARD(pde_index_lists m (:N))) * &2 pow m * &(m + 1)` THEN
  ABBREV_TAC `n1 = norm(vectorize(mat 1:real^Q^Q))` THEN
  ABBREV_TAC `JA = pde_jetn m (\x. vectorize((A:real^N->real^N^N) x)) z` THEN
  ABBREV_TAC `JB = sum(1..dimindex(:N))
                     (\i. pde_jetn m (\x. vectorize((B:real^N->num->real^Q^Q) x i)) z)` THEN
  ABBREV_TAC `JC = pde_jetn m (\x. vectorize((C0:real^N->real^Q^Q) x)) z` THEN
  ABBREV_TAC `Nn = &(dimindex(:N))` THEN
  SUBGOAL_THEN
   `&0 <= Km * Ap * Nn pow 2 * n1 * JB /\ &0 <= Km * Ap * Nn pow 2 * n1 * JC /\
    &0 <= Km * Ap * JA /\ &0 <= Km * Ap * JC`
  STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN RDT_NN_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

let RDT_INTK_LE_INT = prove
 (`!U K KW (g:real^N->real).
     open U /\ compact K /\ K SUBSET U /\ compact KW /\ KW SUBSET U /\ rdt_cs U KW g /\
     (!y. y IN U ==> &0 <= g y)
     ==> drop(integral K (\y. lift(g y))) <= rdt_int U g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rdt_int] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RDT_INTK_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_MESON_TAC[rdt_cs];
    MATCH_MP_TAC RDT_CS_INTEGRABLE THEN EXISTS_TAC `KW:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let RDT_COMM_LOP0_FUN = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^Q^Q) p (W:real^N->real^Q).
     pde_mt_comm A B p W = pde_lop0 (\z. mat 0) (rdt_cdd A p) (rdt_cee A B p) W`,
  REWRITE_TAC[FUN_EQ_THM; RDT_COMM_LOP0]);;

(* int_K jet_s(W)^2 <= CARD(IL s) |W|_s^2 for W vanishing off a compact KW.   *)

let RDT_INTK_JETN_SQ = prove
 (`!U K KW (W:real^N->real^Q) s.
     open U /\ compact K /\ K SUBSET U /\ compact KW /\ KW SUBSET U /\ smooth_map_on U W /\
     (!y. y IN U /\ ~(y IN KW) ==> W y = vec 0)
     ==> drop(integral K (\y. lift(pde_jetn s W y pow 2))) <=
         &(CARD(pde_index_lists s (:N))) * rdt_hs U s W`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!l. (\y. lift(norm(iterated_partial l (W:real^N->real^Q) y) pow 2))
                    continuous_on K`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RDT_CONT_SQNORM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral K (\y. lift(&(CARD(pde_index_lists s (:N))) *
                 sum (pde_index_lists s (:N))
                   (\l. norm(iterated_partial l (W:real^N->real^Q) y) pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RDT_INTK_LE THEN ASM_REWRITE_TAC[PDE_ME_JETN_SQ] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      REWRITE_TAC[o_DEF; LIFT_DROP] THEN
      MATCH_MP_TAC RDT_JETN_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_CMUL; LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real^N->bool`;
    `\y. sum (pde_index_lists s (:N)) (\l. norm(iterated_partial l (W:real^N->real^Q) y) pow 2)`;
    `&(CARD(pde_index_lists s (:N)))`] RDT_INTK_CMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MP_TAC(ISPECL [`K:real^N->bool`;
    `\l y. norm(iterated_partial l (W:real^N->real^Q) y) pow 2`; `pde_index_lists s (:N)`]
    RDT_INTK_SUM) THEN
  ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rdt_hs] THEN MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RDT_INTK_LE_INT THEN EXISTS_TAC `KW:real^N->bool` THEN
  ASM_SIMP_TAC[RDT_CS_SQNORM; REAL_LE_POW_2]);;

(* From a pointwise tame bound of all derivatives of X on K to H^m of X.     *)

let RDT_HS_FROM_POINTWISE = prove
 (`!U K KW (X:real^N->real^P) (W:real^N->real^Q) (Qf:real^N->real) m s c1 M Lam Qb.
     open U /\ compact K /\ K SUBSET U /\ compact KW /\ KW SUBSET U /\
     smooth_map_on U X /\ smooth_map_on U W /\
     (!y. y IN U /\ ~(y IN K) ==> X y = vec 0) /\
     (!y. y IN U /\ ~(y IN KW) ==> W y = vec 0) /\
     (\y. lift(Qf y)) continuous_on K /\ drop(integral K (\y. lift(Qf y pow 2))) <= Qb /\
     &0 <= c1 /\ &0 <= M /\ &0 <= Lam /\
     (!l y. l IN pde_index_lists m (:N) /\ y IN K
            ==> norm(iterated_partial l X y) <= c1 * (M * pde_jetn s W y + Qf y * Lam))
     ==> rdt_hs U m X <=
         &(CARD(pde_index_lists m (:N))) *
         (&2 * c1 pow 2 * (M pow 2 * &(CARD(pde_index_lists s (:N))) * rdt_hs U s W +
                           Lam pow 2 * Qb))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [rdt_hs] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists m (:N))
                (\l:num list. &2 * c1 pow 2 *
                   (M pow 2 * &(CARD(pde_index_lists s (:N))) * rdt_hs U s (W:real^N->real^Q) +
                    Lam pow 2 * Qb))` THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[SUM_CONST; PDE_INDEX_LISTS_FINITE; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                 `\y. norm(iterated_partial l (X:real^N->real^P) y) pow 2`] RDT_INT_ON_K) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RDT_CS_SQNORM]; REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `(\y. lift(pde_jetn s (W:real^N->real^Q) y pow 2)) continuous_on K /\
    (\y. lift((Qf:real^N->real) y pow 2)) continuous_on K /\
    (\y. lift(norm(iterated_partial l (X:real^N->real^P) y) pow 2)) continuous_on K`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      REWRITE_TAC[o_DEF; LIFT_DROP] THEN
      MATCH_MP_TAC RDT_JETN_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
      MATCH_MP_TAC RDT_CONT_SQNORM THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; ETA_AX]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral K (\y. lift((&2 * c1 pow 2 * M pow 2) *
                                         pde_jetn s (W:real^N->real^Q) y pow 2 +
                                         (&2 * c1 pow 2 * Lam pow 2) *
                                         (Qf:real^N->real) y pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RDT_INTK_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `y:real^N`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(c1 * (M * pde_jetn s (W:real^N->real^Q) y + (Qf:real^N->real) y * Lam)) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      REWRITE_TAC[REAL_POW_MUL] THEN
      MP_TAC(SPECL [`M * pde_jetn s (W:real^N->real^Q) y`; `(Qf:real^N->real) y * Lam`]
        (REAL_ARITH `!a b. &0 <= (a - b) pow 2 ==> (a + b) pow 2 <= &2 * a pow 2 + &2 * b pow 2`)) THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `c1 pow 2 * (&2 * (M * pde_jetn s (W:real^N->real^Q) y) pow 2 +
                              &2 * ((Qf:real^N->real) y * Lam) pow 2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
        REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real^N->bool`;
    `\y. (&2 * c1 pow 2 * M pow 2) * pde_jetn s (W:real^N->real^Q) y pow 2`;
    `\y. (&2 * c1 pow 2 * Lam pow 2) * (Qf:real^N->real) y pow 2`] RDT_INTK_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_CMUL] THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `\y. pde_jetn s (W:real^N->real^Q) y pow 2`;
                 `&2 * c1 pow 2 * M pow 2`] RDT_INTK_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `\y. (Qf:real^N->real) y pow 2`;
                 `&2 * c1 pow 2 * Lam pow 2`] RDT_INTK_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `KW:real^N->bool`; `W:real^N->real^Q`;
                 `s:num`] RDT_INTK_JETN_SQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= &2 * c1 pow 2 * M pow 2 /\ &0 <= &2 * c1 pow 2 * Lam pow 2`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN RDT_NN_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * c1 pow 2 * M pow 2) *
              (&(CARD(pde_index_lists s (:N))) * rdt_hs U s (W:real^N->real^Q)) +
              (&2 * c1 pow 2 * Lam pow 2) * Qb` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

let RDT_KC_MONO = prove
 (`!m s. m <= s
         ==> (&(CARD(pde_index_lists m (:N))) * &2 pow m * &(m + 1)) *
             (&3 * &(dimindex(:N)) pow 2 * norm(vectorize(mat 1:real^Q^Q)) + &1) <=
             (&(CARD(pde_index_lists s (:N))) * &2 pow s * &(s + 1)) *
             (&3 * &(dimindex(:N)) pow 2 * norm(vectorize(mat 1:real^Q^Q)) + &1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ALL_TAC; RDT_NN_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[PDE_INDEX_LISTS_MONO; PDE_INDEX_LISTS_FINITE];
    ALL_TAC] THEN
  CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;

(* The H^(s-1) bound of the cut-off commutator.                              *)

let RDT_COMM_HS = prove
 (`!(K:real^N->bool) KW s M Qb Ap.
     compact K /\ compact KW /\ 2 * dimindex(:N) + 4 <= s /\ &0 <= M /\ &0 <= Qb /\ &0 <= Ap
     ==> ?C. &0 <= C /\
             !U (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) p W.
               open U /\ K SUBSET U /\ KW SUBSET U /\
               smooth_map_on U (\x. vectorize(A x)) /\
               (!i. smooth_map_on U (\x. vectorize(B x i))) /\
               smooth_map_on U (\x. vectorize(C0 x)) /\
               smooth_map_on U p /\ smooth_map_on U W /\
               (!y. y IN U /\ ~(y IN K) ==> p y = vec 0) /\
               (!y. y IN U /\ ~(y IN KW) ==> W y = vec 0) /\
               (!y. y IN K ==> pde_jetn (s + 1) p y <= Ap) /\
               (!y. y IN K ==> rdt_cjet (s DIV 2 + 1) A B C0 y <= M) /\
               drop(integral K (\y. lift(rdt_cjet s A B C0 y pow 2))) <= Qb
               ==> rdt_hs U (s - 1) (pde_mt_comm A B p W) <= C * rdt_hs U s W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`KW:real^N->bool`; `s DIV 2 + 2`] RDT_SOBOLEV_JETN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CS:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sob"))) THEN
  ABBREV_TAC `Kc = (&(CARD(pde_index_lists s (:N))) * &2 pow s * &(s + 1)) *
                   (&3 * &(dimindex(:N)) pow 2 * norm(vectorize(mat 1:real^Q^Q)) + &1)` THEN
  ABBREV_TAC `c = &(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow s * &(s + 1))` THEN
  SUBGOAL_THEN `&0 <= Kc /\ &0 <= c` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Kc"; "c"] THEN CONJ_TAC THEN RDT_NN_TAC; ALL_TAC] THEN
  EXISTS_TAC `&(CARD(pde_index_lists (s - 1) (:N))) *
              (&2 * (c * Kc * Ap) pow 2 *
               (M pow 2 * &(CARD(pde_index_lists s (:N))) + CS * Qb))` THEN
  CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `A:real^N->real^N^N`; `B:real^N->num->real^Q^Q`;
                 `p:real^N->real^1`] RDT_COMM_COEFF_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[RDT_COMM_LOP0_FUN] THEN
  SUBGOAL_THEN
   `smooth_map_on U (pde_lop0 (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p)
                              (W:real^N->real^Q))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_LOP0_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN U /\ ~(y IN K)
        ==> pde_lop0 (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p)
                     (W:real^N->real^Q) y = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN REWRITE_TAC[GSYM RDT_COMM_LOP0] THEN
    MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN EXISTS_TAC `U DIFF (K:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rdt_hs U s (W:real^N->real^Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_HS_POS THEN EXISTS_TAC `KW:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Lam = sqrt(CS * rdt_hs U s (W:real^N->real^Q))` THEN
  SUBGOAL_THEN `&0 <= Lam /\ Lam pow 2 = CS * rdt_hs U s (W:real^N->real^Q)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Lam" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE; MATCH_MP_TAC SQRT_POW_2] THEN RDT_NN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dimindex(:N) + s DIV 2 + 2 <= s` ASSUME_TAC THENL
   [MP_TAC(SPECL [`s:num`; `2`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> pde_jetn (s DIV 2 + 2) (W:real^N->real^Q) y <= Lam`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "Lam" THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CS * rdt_hs U (dimindex(:N) + s DIV 2 + 2) (W:real^N->real^Q)` THEN
    CONJ_TAC THENL
     [USE_THEN "sob" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_HS_MONO THEN
      EXISTS_TAC `KW:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the pointwise bound *)
  SUBGOAL_THEN
   `!l y. l IN pde_index_lists (s - 1) (:N) /\ y IN K
          ==> norm(iterated_partial l
                     (pde_lop0 (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p)
                               (W:real^N->real^Q)) y) <=
              (c * Kc * Ap) *
              (M * pde_jetn s W y +
               rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                        (C0:real^N->real^Q^Q) y * Lam)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!m. m <= s - 1
          ==> rdt_cjet m (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p) y <=
              Kc * Ap * rdt_cjet m (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                   (C0:real^N->real^Q^Q) y`
    ASSUME_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`m:num`; `U:real^N->bool`; `A:real^N->real^N^N`;
                     `B:real^N->num->real^Q^Q`; `C0:real^N->real^Q^Q`; `p:real^N->real^1`;
                     `y:real^N`; `Ap:real`] RDT_COMM_CJET) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn (s + 1) (p:real^N->real^1) y` THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [EXPAND_TAC "Kc" THEN MATCH_MP_TAC RDT_KC_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[RDT_CJET_POS]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `\z:real^N. mat 0:real^N^N`;
                   `rdt_cdd (A:real^N->real^N^N) (p:real^N->real^1):real^N->num->real^Q^Q`;
                   `rdt_cee (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (p:real^N->real^1)`;
                   `W:real^N->real^Q`; `y:real^N`] RDT_LOP0_COMM_CJET) THEN
    ASM_REWRITE_TAC[MAT_0_COMPONENT; VECTOR_MUL_LZERO; VSUM_0; VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    ABBREV_TAC `n = LENGTH(l:num list)` THEN
    SUBGOAL_THEN `n DIV 2 + 1 <= s - 1 /\ n DIV 2 + 1 <= s DIV 2 + 1 /\ n <= s - 1 /\
                  n + 1 <= s /\ n DIV 2 + 2 <= s DIV 2 + 2` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `n DIV 2 <= s DIV 2` ASSUME_TAC THENL
       [MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `rdt_cjet (n DIV 2 + 1) (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p) y *
      pde_jetn (n + 1) (W:real^N->real^Q) y <= (Kc * Ap * M) * pde_jetn s W y /\
      rdt_cjet n (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p) y *
      pde_jetn (n DIV 2 + 2) W y <=
      (Kc * Ap * rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                          (C0:real^N->real^Q^Q) y) * Lam`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[RDT_CJET_POS; PDE_JETN_POS] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `Kc * Ap * rdt_cjet (n DIV 2 + 1) (A:real^N->real^N^N)
                      (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `rdt_cjet (s DIV 2 + 1) (A:real^N->real^N^N)
                      (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y` THEN
        ASM_SIMP_TAC[RDT_CJET_MONO];
        MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `Kc * Ap * rdt_cjet n (A:real^N->real^N^N)
                      (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC RDT_CJET_MONO THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `pde_jetn (s DIV 2 + 2) (W:real^N->real^Q) y` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow n * &(n + 1)) <= c`
    ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ASM_ARITH_TAC];
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * (&2 pow n * &(n + 1))) *
                ((Kc * Ap * M) * pde_jetn s (W:real^N->real^Q) y +
                 (Kc * Ap * rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                     (C0:real^N->real^Q^Q) y) * Lam)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * ((Kc * Ap * M) * pde_jetn s (W:real^N->real^Q) y +
                     (Kc * Ap * rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q)
                                         (C0:real^N->real^Q^Q) y) * Lam)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[PDE_JETN_POS] THEN ASM_REWRITE_TAC[] THEN RDT_NN_TAC THEN
      REWRITE_TAC[RDT_CJET_POS];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `KW:real^N->bool`;
    `pde_lop0 (\z:real^N. mat 0:real^N^N) (rdt_cdd A p) (rdt_cee A B p) (W:real^N->real^Q)`;
    `W:real^N->real^Q`;
    `\y. rdt_cjet s (A:real^N->real^N^N) (B:real^N->num->real^Q^Q) (C0:real^N->real^Q^Q) y`;
    `s - 1`; `s:num`; `c * Kc * Ap`; `M:real`; `Lam:real`; `Qb:real`]
    RDT_HS_FROM_POINTWISE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_CJET_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      RDT_NN_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC);;

