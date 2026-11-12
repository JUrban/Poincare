(* ========================================================================= *)
(* pc_pde_rdt_st: the Ricci-DeTurck existence, part 9.  The space-time jets  *)
(* of the frozen-coefficient iterates: sub-jet calculus                      *)
(* (Leibniz and composition with the derivatives collected along             *)
(* subsequences), the time trade d/dt G_(k+1) = L(G_k) G_(k+1) + R(G_k) in   *)
(* the charts, bounds of all space-time jets uniform in the iteration, and   *)
(* their uniform Cauchy property (mean value theorem in time).               *)
(* ========================================================================= *)

needs "src/pc_pde_rdt_conv.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Calculus of sub-jets (pde_subjet of pc_pde_texist: the norms              *)
(* of the derivatives of f along all subsequences of a list).  Locality,    *)
(* sums, bilinear products and compositions with smooth maps:                *)
(*   subjet l B(f,g) <= M subjet l f subjet l g,                             *)
(*   subjet l (Phi o K) <= (1 + M)^n jetn n Phi (K x) (1 + subjet l K)^n.    *)
(* ------------------------------------------------------------------------- *)

let RDT_SUBJET_LOCAL = prove
 (`!l s (f:real^M->real^N) g x.
     open s /\ x IN s /\ (!y. y IN s ==> f y = g y)
     ==> pde_subjet l f x = pde_subjet l g x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pde_subjet] THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`[h:num]`; `s:real^M->bool`; `f:real^M->real^N`; `g:real^M->real^N`]
    TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
  ASM_REWRITE_TAC[iterated_partial] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RDT_SUBJET_ZERO = prove
 (`!l x. pde_subjet l (\x:real^M. vec 0:real^N) x = &0`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[pde_subjet; NORM_0] THEN
  SUBGOAL_THEN `partial_derivative h (\x:real^M. vec 0:real^N) = (\x. vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; PARTIAL_DERIVATIVE_CONST]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID]);;

let RDT_SUBJET_ADD = prove
 (`!l s (f:real^M->real^N) g x.
     open s /\ smooth_map_on s f /\ smooth_map_on s g /\ x IN s
     ==> pde_subjet l (\x. f x + g x) x <= pde_subjet l f x + pde_subjet l g x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pde_subjet] THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_TRIANGLE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c d e f. a <= c + d /\ b <= e + f ==> a + b <= (c + e) + (d + f)`) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_subjet t (\y. partial_derivative h (f:real^M->real^N) y +
                               partial_derivative h g y) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC RDT_SUBJET_LOCAL THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`[h:num]`; `s:real^M->bool`; `f:real^M->real^N`; `g:real^M->real^N`]
      PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
    ASM_REWRITE_TAC[iterated_partial] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]]);;

let RDT_SUBJET_VSUM = prove
 (`!l s (f:A->real^M->real^N) t x.
     open s /\ FINITE t /\ (!a. a IN t ==> smooth_map_on s (f a)) /\ x IN s
     ==> pde_subjet l (\x. vsum t (\a. f a x)) x <= sum t (\a. pde_subjet l (f a) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `!a. a IN t ==> smooth_map_on s ((f:A->real^M->real^N) a)` THEN
  UNDISCH_TAC `FINITE (t:A->bool)` THEN SPEC_TAC(`t:A->bool`,`t:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES; SUM_CLAUSES; RDT_SUBJET_ZERO; REAL_LE_REFL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b:A`; `t:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; SUM_CLAUSES] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_subjet l (f (b:A):real^M->real^N) x +
              pde_subjet l (\x. vsum t (\a. (f:A->real^M->real^N) a x)) x` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`l:num list`; `s:real^M->bool`; `(f:A->real^M->real^N) b`;
                   `\x. vsum t (\a. (f:A->real^M->real^N) a x)`; `x:real^M`] RDT_SUBJET_ADD) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_SIMP_TAC[];
    REWRITE_TAC[REAL_LE_LADD] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

let RDT_SUBJET_BILINEAR = prove
 (`!(bb:real^P->real^Q->real^K) M l s (f:real^M->real^P) (g:real^M->real^Q) x.
     bilinear bb /\ (!u v. norm(bb u v) <= M * norm u * norm v) /\ &0 <= M /\
     open s /\ smooth_map_on s f /\ smooth_map_on s g /\ x IN s
     ==> pde_subjet l (\x. bb (f x) (g x)) x <=
         M * pde_subjet l f x * pde_subjet l g x`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[pde_subjet] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on s (partial_derivative h (f:real^M->real^P)) /\
    smooth_map_on s (partial_derivative h (g:real^M->real^Q))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_subjet t (partial_derivative h (\x. (bb:real^P->real^Q->real^K)
                                                ((f:real^M->real^P) x) ((g:real^M->real^Q) x))) x =
    pde_subjet t (\x. bb (partial_derivative h f x) (g x) + bb (f x) (partial_derivative h g x)) x`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RDT_SUBJET_LOCAL THEN EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN MATCH_MP_TAC PDE_PARTIAL_BILINEAR THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `M * pde_subjet t (f:real^M->real^P) x * pde_subjet t (g:real^M->real^Q) x +
              (M * pde_subjet t (partial_derivative h f) x * pde_subjet t g x +
               M * pde_subjet t f x * pde_subjet t (partial_derivative h g) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_subjet t (\x. (bb:real^P->real^Q->real^K)
                                    (partial_derivative h (f:real^M->real^P) x)
                                    ((g:real^M->real^Q) x)) x +
                pde_subjet t (\x. bb (f x) (partial_derivative h g x)) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RDT_SUBJET_ADD THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_BILINEAR_OPEN THEN
      ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:num list`; `partial_derivative h (f:real^M->real^P)`; `x:real^M`]
    PDE_SUBJET_POS) THEN
  MP_TAC(ISPECL [`t:num list`; `partial_derivative h (g:real^M->real^Q)`; `x:real^M`]
    PDE_SUBJET_POS) THEN
  MP_TAC(ISPECL [`t:num list`; `f:real^M->real^P`; `x:real^M`] PDE_SUBJET_POS) THEN
  MP_TAC(ISPECL [`t:num list`; `g:real^M->real^Q`; `x:real^M`] PDE_SUBJET_POS) THEN
  ABBREV_TAC `a1 = pde_subjet t (f:real^M->real^P) x` THEN
  ABBREV_TAC `a2 = pde_subjet t (partial_derivative h (f:real^M->real^P)) x` THEN
  ABBREV_TAC `b1 = pde_subjet t (g:real^M->real^Q) x` THEN
  ABBREV_TAC `b2 = pde_subjet t (partial_derivative h (g:real^M->real^Q)) x` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= M * a2 * b2` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RDT_SUBJET_MONO_CONS = prove
 (`!h l (f:real^M->real^N) x. pde_subjet l f x <= pde_subjet (CONS h l) f x`,
  REWRITE_TAC[pde_subjet; REAL_LE_ADDR; PDE_SUBJET_POS]);;

let RDT_SUBJET_COMPOSE = prove
 (`!l (Phi:real^M->real^P) (K:real^Q->real^M) U W x.
     open U /\ open W /\ smooth_map_on U K /\ smooth_map_on W Phi /\ IMAGE K U SUBSET W /\
     x IN U /\ ALL (\i. 1 <= i /\ i <= dimindex(:Q)) l
     ==> pde_subjet l (\z. Phi(K z)) x <=
         (&1 + &(dimindex(:M))) pow (LENGTH l) * pde_jetn (LENGTH l) Phi (K x) *
         (&1 + pde_subjet l K x) pow (LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pde_subjet; LENGTH; real_pow; ALL] THENL
   [REWRITE_TAC[RDT_JETN_0; REAL_MUL_LID; REAL_MUL_RID; REAL_LE_REFL]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `n = LENGTH(t:num list)` THEN
  ABBREV_TAC `dM = &(dimindex(:M))` THEN
  SUBGOAL_THEN `&0 <= dM` ASSUME_TAC THENL [EXPAND_TAC "dM" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  ABBREV_TAC `S = pde_subjet t (K:real^Q->real^M) x + pde_subjet t (partial_derivative h K) x` THEN
  SUBGOAL_THEN `&0 <= S /\ pde_subjet t (K:real^Q->real^M) x <= S /\
                pde_subjet t (partial_derivative h (K:real^Q->real^M)) x <= S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MP_TAC(ISPECL [`t:num list`; `K:real^Q->real^M`; `x:real^Q`]
      PDE_SUBJET_POS) THEN
    MP_TAC(ISPECL [`t:num list`; `partial_derivative h (K:real^Q->real^M)`; `x:real^Q`]
      PDE_SUBJET_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `J = pde_jetn (SUC n) (Phi:real^M->real^P) (K(x:real^Q))` THEN
  SUBGOAL_THEN `&0 <= J` ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC[PDE_JETN_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. (Phi:real^M->real^P) ((K:real^Q->real^M) z))` ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_SMOOTH_COMPOSE THEN EXISTS_TAC `W:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + pde_subjet t (K:real^Q->real^M) x) pow n <= (&1 + S) pow n`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:num list`; `K:real^Q->real^M`; `x:real^Q`] PDE_SUBJET_POS) THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the first part *)
  SUBGOAL_THEN
   `pde_subjet t (\z. (Phi:real^M->real^P) ((K:real^Q->real^M) z)) x <=
    (&1 + dM) pow n * J * (&1 + S) pow n`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + dM) pow n * pde_jetn n (Phi:real^M->real^P) (K(x:real^Q)) *
                (&1 + pde_subjet t (K:real^Q->real^M) x) pow n` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`U:real^Q->bool`; `W:real^M->bool`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[PDE_JETN_POS] THEN CONJ_TAC THENL
       [EXPAND_TAC "J" THEN MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN
        MP_TAC(ISPECL [`t:num list`; `K:real^Q->real^M`; `x:real^Q`] PDE_SUBJET_POS) THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the second part *)
  SUBGOAL_THEN
   `pde_subjet t (partial_derivative h (\z. (Phi:real^M->real^P) ((K:real^Q->real^M) z))) x <=
    sum(1..dimindex(:M))
      (\j. &1 * pde_subjet t (\z. partial_derivative j Phi (K z)) x *
           pde_subjet t (partial_derivative h K) x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `pde_subjet t (\z. vsum(1..dimindex(:M))
                          (\j. (partial_derivative h (K:real^Q->real^M) z)$j %
                               partial_derivative j (Phi:real^M->real^P) (K z))) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC RDT_SUBJET_LOCAL THEN
      EXISTS_TAC `U:real^Q->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:real^Q` THEN DISCH_TAC THEN MATCH_MP_TAC RDT_PARTIAL_COMPOSE THEN
      CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
       [EXISTS_TAC `U:real^Q->bool`; EXISTS_TAC `W:real^M->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum(1..dimindex(:M))
        (\j. pde_subjet t (\z. (partial_derivative h (K:real^Q->real^M) z)$j %
                               partial_derivative j (Phi:real^M->real^P) (K z)) x)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:num list`; `U:real^Q->bool`;
                     `\j z. (partial_derivative h (K:real^Q->real^M) z)$j %
                            partial_derivative j (Phi:real^M->real^P) (K z)`;
                     `1..dimindex(:M)`; `x:real^Q`] RDT_SUBJET_VSUM) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `j:num` (INST_TYPE [`:P`,`:P`] RDT_BILINEAR_COMPONENT)) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[IN_NUMSEG]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`U:real^Q->bool`; `\(u:real^P) (w:real^M). w$j % u`;
                     `\z. partial_derivative j (Phi:real^M->real^P) ((K:real^Q->real^M) z)`;
                     `partial_derivative h (K:real^Q->real^M)`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC RDT_SMOOTH_COMPOSE THEN EXISTS_TAC `W:real^M->bool` THEN
          ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
          ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]];
        REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPEC `j:num` (INST_TYPE [`:P`,`:P`] RDT_BILINEAR_COMPONENT)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`\(u:real^P) (w:real^M). w$j % u`; `&1`; `t:num list`; `U:real^Q->bool`;
                   `\z. partial_derivative j (Phi:real^M->real^P) ((K:real^Q->real^M) z)`;
                   `partial_derivative h (K:real^Q->real^M)`; `x:real^Q`]
      RDT_SUBJET_BILINEAR) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_POS] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RDT_SMOOTH_COMPOSE THEN EXISTS_TAC `W:real^M->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:M)
        ==> pde_subjet t (\z. partial_derivative j (Phi:real^M->real^P) ((K:real^Q->real^M) z)) x
            <= (&1 + dM) pow n * J * (&1 + S) pow n`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + dM) pow n *
                pde_jetn n (partial_derivative j (Phi:real^M->real^P)) (K(x:real^Q)) *
                (&1 + pde_subjet t (K:real^Q->real^M) x) pow n` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`U:real^Q->bool`; `W:real^M->bool`] THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[PDE_JETN_POS] THEN CONJ_TAC THENL
       [EXPAND_TAC "J" THEN MATCH_MP_TAC PDE_JETN_PARTIAL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_LE THEN
        MP_TAC(ISPECL [`t:num list`; `K:real^Q->real^M`; `x:real^Q`] PDE_SUBJET_POS) THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `P = (&1 + dM) pow n * J * (&1 + S) pow n` THEN
  SUBGOAL_THEN `&0 <= P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:M))
      (\j. &1 * pde_subjet t (\z. partial_derivative j (Phi:real^M->real^P)
                                    ((K:real^Q->real^M) z)) x *
           pde_subjet t (partial_derivative h K) x) <= dM * (P * S)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:M)) (\j:num. P * S)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[PDE_SUBJET_POS];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN EXPAND_TAC "dM" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `P + dM * (P * S)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `sum(1..dimindex(:M))
          (\j. &1 * pde_subjet t (\z. partial_derivative j (Phi:real^M->real^P)
                                        ((K:real^Q->real^M) z)) x *
               pde_subjet t (partial_derivative h K) x)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((&1 + dM) * (&1 + dM) pow n) * J * ((&1 + S) * (&1 + S) pow n) = (&1 + dM) * (&1 + S) * P`
  SUBST1_TAC THENL [EXPAND_TAC "P" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= dM * P /\ &0 <= S * P /\ &0 <= dM * S * P` MP_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The space-time representative of a family in a chart and                  *)
(* the time trade: for a solution v of the linear equation with coefficient  *)
(* k and forcing f,                                                          *)
(*   d/dt V = stop(a_k, b_k, c_k) V + F   on (a,b) x U,                      *)
(* with the coefficients of the chart operator as space-time functions.      *)
(* ------------------------------------------------------------------------- *)

let RDT_ST_REP_SMOOTH = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c a b (v:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ pde_tfam_from atlas a b v /\ c IN atlas
     ==> smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
           (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (metric_local atlas c (v (drop(fstcart w))) (sndcart w)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tfam_from] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fv:real^(1,N)finite_sum->real^(N,N)finite_prod`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC TEXT_SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `Fv:real^(1,N)finite_sum->real^(N,N)finite_prod` THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
    ASM_MESON_TAC[PDM_CHART_OPEN_C];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - e),lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let RDT_TRADE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (k:real->A->real^N^N) h f v0
    (v:real->A->real^N^N) c t y.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_mlin_sol (top,atlas) a b k h f v0 v /\
     a < t /\ t < b /\ y IN IMAGE (SND c) (FST c)
     ==> partial_derivative 1
           (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (metric_local atlas c (v (drop(fstcart w))) (sndcart w)))
           (pastecart (lift t) y) =
         pde_stop (\w. pde_mlaa atlas c k (drop(fstcart w)) (sndcart w))
                  (\w i. pde_mlbt atlas c k h (drop(fstcart w)) (sndcart w) i)
                  (\w. pde_mlct atlas c k h (drop(fstcart w)) (sndcart w))
                  (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                         (metric_local atlas c (v (drop(fstcart w))) (sndcart w)))
                  (pastecart (lift t) y) +
         vectorize(metric_local atlas c (f t) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `V = \w. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (metric_local atlas (c:(A->bool)#(A->real^N))
                           ((v:real->A->real^N^N) (drop(fstcart w))) (sndcart w))` THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  SUBGOAL_THEN `open (S:real^(1,N)finite_sum->bool) /\ pastecart (lift t) (y:real^N) IN S /\
                smooth_map_on S (V:real^(1,N)finite_sum->real^(N,N)finite_prod)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "V"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      ASM_MESON_TAC[PDM_CHART_OPEN_C];
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
      MATCH_MP_TAC RDT_ST_REP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[pde_mlin_sol]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(V:real^(1,N)finite_sum->real^(N,N)finite_prod) differentiable
                (at (pastecart (lift t) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the time derivative *)
  SUBGOAL_THEN
   `partial_derivative 1 (V:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) y) =
    pde_lop0 (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t)
             (pde_mlbt atlas c k (h:A->real^N^N) t) (pde_mlct atlas c k h t)
             (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                    (metric_local atlas c ((v:real->A->real^N^N) t) y)) y +
    vectorize(metric_local atlas c ((f:real->A->real^N^N) t) y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\r. (V:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart r y)` THEN
    EXISTS_TAC `lift t` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_ST_TIME_DERIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\r. (V:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart r y)) =
      (\s. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) (drop s)) y))`
    SUBST1_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[FUN_EQ_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `f:real->A->real^N^N`;
                   `v0:A->real^N^N`; `v:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                   `t:real`; `y:real^N`] PDE_ML_SOL_CHART_LOP) THEN
    ASM_REWRITE_TAC[PDE_LOP_LOP0];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `x + z = y + z <=> x:real^N = y`] THEN
  REWRITE_TAC[pde_lop0; pde_stop; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  SUBGOAL_THEN
   `(\y. (vectorize:real^N^N->real^(N,N)finite_prod)
           (metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) t) y)) =
    (\y. (V:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) y))`
  SUBST1_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[FUN_EQ_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> partial_derivative i (\y. (V:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                         (pastecart (lift t) y)) y =
            partial_derivative (1 + i) V (pastecart (lift t) y) /\
            (!j. 1 <= j /\ j <= dimindex(:N)
                 ==> partial_derivative i (partial_derivative j
                       (\y. V (pastecart (lift t) y))) y =
                     partial_derivative (1 + i) (partial_derivative (1 + j) V)
                       (pastecart (lift t) y))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_ST_SLICE_PARTIAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`[i:num; j:num]`; `V:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `S:real^(1,N)finite_sum->bool`; `lift t`; `y:real^N`] PDE_ST_SLICE_ITERATED) THEN
    ASM_REWRITE_TAC[ALL; MAP; iterated_partial];
    ALL_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[];
    AP_TERM_TAC THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]);;

(* ------------------------------------------------------------------------- *)
(* More sub-jet calculus (linear images, pastecart, vectorized               *)
(* families), single derivatives and parabolic jets bounded by sub-jets and  *)
(* list-wise bounds, lists without time index, and space-time functions that *)
(* do not depend on time.                                                    *)
(* ------------------------------------------------------------------------- *)

let RDT_SUBJET_LINEAR = prove
 (`!(L:real^P->real^Q) BL l s (w:real^M->real^P) x.
     linear L /\ (!v. norm(L v) <= BL * norm v) /\ open s /\ smooth_map_on s w /\ x IN s
     ==> pde_subjet l (\z. L(w z)) x <= BL * pde_subjet l w x`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[pde_subjet] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_subjet t (\z. (L:real^P->real^Q) (partial_derivative h (w:real^M->real^P) z)) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC RDT_SUBJET_LOCAL THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`[h:num]`; `L:real^P->real^Q`; `w:real^M->real^P`; `s:real^M->bool`; `y:real^M`]
      PDE_ITERATED_PARTIAL_LINEAR_COMPOSE) THEN
    ASM_REWRITE_TAC[iterated_partial];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]]);;

let RDT_SUBJET_PASTECART = prove
 (`!l s (f:real^M->real^P) (g:real^M->real^Q) x.
     open s /\ smooth_map_on s f /\ smooth_map_on s g /\ x IN s
     ==> pde_subjet l (\z. pastecart (f z) (g z)) x <= pde_subjet l f x + pde_subjet l g x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. pastecart ((f:real^M->real^P) z) ((g:real^M->real^Q) z)) =
                (\z. pastecart (f z) (vec 0) + pastecart (vec 0) (g z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (\z. pastecart ((f:real^M->real^P) z) (vec 0:real^Q)) /\
                smooth_map_on s (\z. pastecart (vec 0:real^P) ((g:real^M->real^Q) z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^P`;
                     `\a:real^P. pastecart a (vec 0:real^Q)`] SMOOTH_MAP_ON_LINEAR_O);
      MP_TAC(ISPECL [`s:real^M->bool`; `g:real^M->real^Q`;
                     `\a:real^Q. pastecart (vec 0:real^P) a`] SMOOTH_MAP_ON_LINEAR_O)] THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; PASTECART_ADD; GSYM PASTECART_CMUL; VECTOR_ADD_LID; VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_subjet l (\z. pastecart ((f:real^M->real^P) z) (vec 0:real^Q)) x +
              pde_subjet l (\z. pastecart (vec 0:real^P) ((g:real^M->real^Q) z)) x` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`l:num list`; `s:real^M->bool`;
                   `\z. pastecart ((f:real^M->real^P) z) (vec 0:real^Q)`;
                   `\z. pastecart (vec 0:real^P) ((g:real^M->real^Q) z)`; `x:real^M`]
      RDT_SUBJET_ADD) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\a:real^P. pastecart a (vec 0:real^Q)`; `&1`; `l:num list`;
                   `s:real^M->bool`; `f:real^M->real^P`; `x:real^M`] RDT_SUBJET_LINEAR);
    MP_TAC(ISPECL [`\a:real^Q. pastecart (vec 0:real^P) a`; `&1`; `l:num list`;
                   `s:real^M->bool`; `g:real^M->real^Q`; `x:real^M`] RDT_SUBJET_LINEAR)] THEN
  ASM_REWRITE_TAC[NORM_PASTECART_0; REAL_MUL_LID; REAL_LE_REFL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[linear; PASTECART_ADD; GSYM PASTECART_CMUL; VECTOR_ADD_LID; VECTOR_MUL_RZERO]);;

let RDT_ITERATED_LE_SUBJET = prove
 (`!l s (f:real^M->real^N) z.
     open s /\ smooth_map_on s f /\ z IN s /\ ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
     ==> norm(iterated_partial l f z) <= pde_subjet l f z`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pde_subjet; iterated_partial; REAL_LE_REFL; ALL] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^N`; `h:num`] TEXT_PARTIAL_COMMUTE_ITERATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:num list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ x <= b ==> x <= a + b`) THEN
  REWRITE_TAC[PDE_SUBJET_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

let RDT_PJET_LE_BOUND = prove
 (`!r a (f:real^M->real^Q) z M.
     (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ pde_ntime l <= a /\
          LENGTH l <= r + a /\ LENGTH l - pde_ntime l <= r
          ==> norm(iterated_partial l f z) <= M)
     ==> pde_pjet r a f z <=
         &(CARD {l | ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ pde_ntime l <= a /\
                     LENGTH l <= r + a /\ LENGTH l - pde_ntime l <= r}) * M`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_pjet] THEN MATCH_MP_TAC SUM_BOUND THEN
  REWRITE_TAC[PDE_PJET_FINITE; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let RDT_NTIME0_MAP = prove
 (`!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ pde_ntime l = 0
       ==> ?l0. ALL (\k. 1 <= k /\ k <= dimindex(:N)) l0 /\ LENGTH l0 = LENGTH l /\
                l = MAP (\k. 1 + k) l0`,
  LIST_INDUCT_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `[]:num list` THEN REWRITE_TAC[ALL; LENGTH; MAP]; ALL_TAC] THEN
  REWRITE_TAC[ALL; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(h = 1) /\ pde_ntime t = 0` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `h = 1` THENL
     [UNDISCH_TAC `pde_ntime (CONS h t) = 0` THEN ASM_REWRITE_TAC[PDE_NTIME_CLAUSES] THEN
      ARITH_TAC;
      UNDISCH_TAC `pde_ntime (CONS h t) = 0` THEN ASM_SIMP_TAC[PDE_NTIME_CLAUSES]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CONS (h - 1) l0` THEN ASM_REWRITE_TAC[ALL; LENGTH; MAP; CONS_11] THEN
  ASM_ARITH_TAC);;

let RDT_ST_TIMEFREE = prove
 (`!U (Y:real^N->real^P) l z.
     open U /\ smooth_map_on U Y /\ z IN (:real^1) PCROSS U /\
     ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
     ==> norm(iterated_partial l (\w. Y(sndcart w)) z) <= pde_jetn (LENGTH l) Y (sndcart z)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = (:real^1) PCROSS (U:real^N->bool)` THEN
  SUBGOAL_THEN `open (S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (\w:real^(1,N)finite_sum. (Y:real^N->real^P) (sndcart w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_SMOOTH_COMPOSE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART];
      EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS;
                                      SNDCART_PASTECART] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `pde_ntime l = 0` THENL
   [MP_TAC(SPEC `l:num list` RDT_NTIME0_MAP) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l0:num list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`l0:num list`; `\w:real^(1,N)finite_sum. (Y:real^N->real^P) (sndcart w)`;
                   `S:real^(1,N)finite_sum->bool`; `fstcart(z:real^(1,N)finite_sum)`;
                   `sndcart(z:real^(1,N)finite_sum)`] PDE_ST_SLICE_ITERATED) THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND; SNDCART_PASTECART] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `LENGTH(l0:num list) = LENGTH(MAP (\k. 1 + k) l0)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC PDE_ME_TERM_LE_JETN THEN
    ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. pde_ntime l = SUC n` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `pde_ntime l - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                 `\w:real^(1,N)finite_sum. (Y:real^N->real^P) (sndcart w)`;
                 `l:num list`; `n:num`; `z:real^(1,N)finite_sum`] PDE_TIME_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':num list` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `iterated_partial l'
      (partial_derivative 1 (\w:real^(1,N)finite_sum. (Y:real^N->real^P) (sndcart w))) z = vec 0`
  (fun th -> REWRITE_TAC[th; NORM_0; PDE_JETN_POS]) THEN
  MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Y:real^N->real^P) differentiable (at (sndcart(w:real^(1,N)finite_sum)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:real^(1,N)finite_sum) IN S` THEN
    EXPAND_TAC "S" THEN ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; SNDCART_PASTECART; FSTCART_PASTECART] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[TEXT_PARTIAL_DERIVATIVE_SNDCART_COMPOSE] THEN
  REWRITE_TAC[PDE_ST_BASIS_TIME; SNDCART_PASTECART] THEN
  MP_TAC(ISPEC `frechet_derivative (Y:real^N->real^P) (at (sndcart(w:real^(1,N)finite_sum)))`
    LINEAR_0) THEN
  ANTS_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* Vectorized families of rows. *)

let RDT_VLAMBDA_VSUM = prove
 (`!(G:num->real^K) . (vectorize:real^K^P->real^(P,K)finite_prod) (lambda c. G c) =
       vsum(1..dimindex(:P))
         (\c. (vectorize:real^K^P->real^(P,K)finite_prod)
                ((lambda c'. if c' = c then G c else vec 0):real^K^P))`,
  GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_FINITE_PROD] THEN X_GEN_TAC `i:num` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[VECTORIZE_COMPONENT; VSUM_COMPONENT; DIMINDEX_FINITE_PROD] THEN
  MP_TAC(ISPECL [`dimindex(:P)`; `dimindex(:K)`; `i:num`] RDT_INDEX_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; VEC_COMPONENT] THEN
  ABBREV_TAC `r = 1 + (i - 1) DIV dimindex(:K)` THEN
  ABBREV_TAC `q = 1 + (i - 1) MOD dimindex(:K)` THEN
  SUBGOAL_THEN `(\x. if r = x then (G:num->real^K) x$q else &0) = (\x. if x = r then G r$q else &0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN
    ASM_CASES_TAC `x:num = r` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG]);;

let RDT_SUBJET_VLAMBDA = prove
 (`?B. &0 <= B /\
       !l s (G:num->real^M->real^K) z.
         open s /\ (!c. 1 <= c /\ c <= dimindex(:P) ==> smooth_map_on s (G c)) /\ z IN s
         ==> pde_subjet l (\x. (vectorize:real^K^P->real^(P,K)finite_prod) (lambda c. G c x)) z <=
             B * sum(1..dimindex(:P)) (\c. pde_subjet l (G c) z)`,
  SUBGOAL_THEN
   `!c. ?Bc. &0 < Bc /\
             !v:real^K. norm((vectorize:real^K^P->real^(P,K)finite_prod)
                              ((lambda c'. if c' = c then v else vec 0):real^K^P)) <= Bc * norm v`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LINEAR_BOUNDED_POS THEN
    REWRITE_TAC[linear; GSYM VECTORIZE_ADD; GSYM VECTORIZE_CMUL] THEN CONJ_TAC THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Bc:num->real`) THEN
  EXISTS_TAC `sum(1..dimindex(:P)) (Bc:num->real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!c. 1 <= c /\ c <= dimindex(:P)
        ==> smooth_map_on s (\x. (vectorize:real^K^P->real^(P,K)finite_prod)
                                   ((lambda c'. if c' = c then (G:num->real^M->real^K) c x
                                                else vec 0):real^K^P))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `(G:num->real^M->real^K) c`;
                   `\v:real^K. (vectorize:real^K^P->real^(P,K)finite_prod)
                                 ((lambda c'. if c' = c then v else vec 0):real^K^P)`]
      SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_SIMP_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; GSYM VECTORIZE_ADD; GSYM VECTORIZE_CMUL] THEN CONJ_TAC THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[RDT_VLAMBDA_VSUM] THEN
  MP_TAC(ISPECL [`l:num list`; `s:real^M->bool`;
                 `\c x. (vectorize:real^K^P->real^(P,K)finite_prod)
                          ((lambda c'. if c' = c then (G:num->real^M->real^K) c x
                                       else vec 0):real^K^P)`;
                 `1..dimindex(:P)`; `z:real^M`] RDT_SUBJET_VSUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `c:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Bc:num->real) c * pde_subjet l ((G:num->real^M->real^K) c) z` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\v:real^K. (vectorize:real^K^P->real^(P,K)finite_prod)
                                 ((lambda c'. if c' = c then v else vec 0):real^K^P)`;
                   `(Bc:num->real) c`; `l:num list`; `s:real^M->bool`;
                   `(G:num->real^M->real^K) c`; `z:real^M`] RDT_SUBJET_LINEAR) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[linear; GSYM VECTORIZE_ADD; GSYM VECTORIZE_CMUL] THEN CONJ_TAC THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `c:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Bc:num->real`)) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\c. pde_subjet l ((G:num->real^M->real^K) c) z`; `dimindex(:P)`; `c:num`]
    (prove(`!f:num->real n i. (!j. 1 <= j /\ j <= n ==> &0 <= f j) /\ 1 <= i /\ i <= n
                              ==> f i <= sum(1..n) f`,
           REPEAT STRIP_TAC THEN
           MP_TAC(ISPECL [`{i:num}`; `1..n`; `f:num->real`] SUM_SUBSET_SIMPLE) THEN
           ASM_SIMP_TAC[SUM_SING; FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; IN_DIFF]))) THEN
  REWRITE_TAC[PDE_SUBJET_POS] THEN ASM_REWRITE_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* The time derivative of a time-free function vanishes; sub-                *)
(* jets of compositions with a fixed smooth map with points in a compact     *)
(* set, with a uniform constant; sub-jets of the space-time operator stop.   *)
(* ------------------------------------------------------------------------- *)

let RDT_ST_TIMEFREE_D1 = prove
 (`!U (Y:real^N->real^P) w.
     open U /\ smooth_map_on U Y /\ w IN (:real^1) PCROSS U
     ==> partial_derivative 1 (\w. Y(sndcart w)) w = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(Y:real^N->real^P) differentiable (at (sndcart(w:real^(1,N)finite_sum)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:real^(1,N)finite_sum) IN (:real^1) PCROSS U` THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; SNDCART_PASTECART; FSTCART_PASTECART] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[TEXT_PARTIAL_DERIVATIVE_SNDCART_COMPOSE] THEN
  REWRITE_TAC[PDE_ST_BASIS_TIME; SNDCART_PASTECART] THEN
  MP_TAC(ISPEC `frechet_derivative (Y:real^N->real^P) (at (sndcart(w:real^(1,N)finite_sum)))`
    LINEAR_0) THEN
  ANTS_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

let RDT_SUBJET_COMPOSE_UNIF = prove
 (`!(Phi:real^M->real^P) W Kc n.
     open W /\ smooth_map_on W Phi /\ compact Kc /\ Kc SUBSET W
     ==> ?C. &0 <= C /\
             !(K:real^Q->real^M) U x l.
               open U /\ smooth_map_on U K /\ IMAGE K U SUBSET W /\ x IN U /\ K x IN Kc /\
               ALL (\i. 1 <= i /\ i <= dimindex(:Q)) l /\ LENGTH l <= n
               ==> pde_subjet l (\z. Phi(K z)) x <= C * (&1 + pde_subjet l K x) pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^M->bool`; `Kc:real^M->bool`; `Phi:real^M->real^P`; `n:num`]
    RDT_JETS_BOUNDED_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `CJ:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(&1 + &(dimindex(:M))) pow n * CJ` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
    REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `Phi:real^M->real^P`; `K:real^Q->real^M`; `U:real^Q->bool`;
                 `W:real^M->bool`; `x:real^Q`] RDT_SUBJET_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  ABBREV_TAC `s = pde_subjet l (K:real^Q->real^M) x` THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL [EXPAND_TAC "s" THEN REWRITE_TAC[PDE_SUBJET_POS]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `&1 <= &1 + &(dimindex(:M)) /\ &1 <= &1 + s` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&1 <= &1 + x <=> &0 <= x`; REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PDE_JETN_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[PDE_JETN_POS];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_jetn n (Phi:real^M->real^P) ((K:real^Q->real^M) x)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[]]);;

let RDT_BILINEAR_MATENTRY = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
         ==> bilinear (\(u:real^(N,N)finite_prod) (v:real^K). (matrify u:real^N^N)$i$j % v) /\
             !(u:real^(N,N)finite_prod) (v:real^K).
               norm((matrify u:real^N^N)$i$j % v) <= &1 * norm u * norm v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[bilinear; linear] THEN
    ASM_SIMP_TAC[MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[NORM_MUL; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_SIMP_TAC[MATRIFY_COMPONENT; COMPONENT_LE_NORM]]);;

let RDT_BILINEAR_MATMUL = prove
 (`bilinear (\(u:real^(K,K)finite_prod) (v:real^K). (matrify u:real^K^K) ** v) /\
   !(u:real^(K,K)finite_prod) (v:real^K). norm((matrify u:real^K^K) ** v) <= &1 * norm u * norm v`,
  REWRITE_TAC[P2CT_MATRIFY_MUL_BILINEAR; REAL_MUL_LID; PDE_MATRIFY_MUL_NORM]);;

let RDT_SUBJET_STOP = prove
 (`!S (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
    (V:real^(1,N)finite_sum->real^K) l z.
     open S /\ smooth_map_on S (\z. vectorize(a z)) /\
     (!i. smooth_map_on S (\z. vectorize(b z i))) /\ smooth_map_on S (\z. vectorize(c z)) /\
     smooth_map_on S V /\ z IN S
     ==> pde_subjet l (pde_stop a b c V) z <=
         sum(1..dimindex(:N))
           (\i. sum(1..dimindex(:N))
                  (\j. pde_subjet l (\z. vectorize(a z)) z *
                       pde_subjet l (partial_derivative (1 + i) (partial_derivative (1 + j) V)) z)) +
         sum(1..dimindex(:N))
           (\i. pde_subjet l (\z. vectorize(b z i)) z *
                pde_subjet l (partial_derivative (1 + i) V) z) +
         pde_subjet l (\z. vectorize(c z)) z * pde_subjet l V z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. smooth_map_on S (partial_derivative i (V:real^(1,N)finite_sum->real^K)) /\
        !j. smooth_map_on S (partial_derivative i (partial_derivative j V))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> smooth_map_on S (\z. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
                                   partial_derivative (1 + i) (partial_derivative (1 + j)
                                     (V:real^(1,N)finite_sum->real^K)) z) /\
              pde_subjet l (\z. a z$i$j %
                                partial_derivative (1 + i) (partial_derivative (1 + j) V) z) z <=
              pde_subjet l (\z. vectorize(a z)) z *
              pde_subjet l (partial_derivative (1 + i) (partial_derivative (1 + j) V)) z`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`i:num`; `j:num`] (INST_TYPE [`:K`,`:K`] RDT_BILINEAR_MATENTRY)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                     `\(u:real^(N,N)finite_prod) (v:real^K). (matrify u:real^N^N)$i$j % v`;
                     `\z. vectorize((a:real^(1,N)finite_sum->real^N^N) z)`;
                     `partial_derivative (1 + i)
                        (partial_derivative (1 + j) (V:real^(1,N)finite_sum->real^K))`]
        SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_REWRITE_TAC[MATRIFY_VECTORIZE];
      MP_TAC(ISPECL [`\(u:real^(N,N)finite_prod) (v:real^K). (matrify u:real^N^N)$i$j % v`;
                     `&1`; `l:num list`; `S:real^(1,N)finite_sum->bool`;
                     `\z. vectorize((a:real^(1,N)finite_sum->real^N^N) z)`;
                     `partial_derivative (1 + i)
                        (partial_derivative (1 + j) (V:real^(1,N)finite_sum->real^K))`;
                     `z:real^(1,N)finite_sum`] RDT_SUBJET_BILINEAR) THEN
      ASM_REWRITE_TAC[REAL_POS; MATRIFY_VECTORIZE] THEN REWRITE_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. smooth_map_on S (\z. (b:real^(1,N)finite_sum->num->real^K^K) z i **
                             partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K) z) /\
        pde_subjet l (\z. b z i ** partial_derivative (1 + i) V z) z <=
        pde_subjet l (\z. vectorize(b z i)) z * pde_subjet l (partial_derivative (1 + i) V) z`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                     `\(u:real^(K,K)finite_prod) (v:real^K). (matrify u:real^K^K) ** v`;
                     `\z. vectorize((b:real^(1,N)finite_sum->num->real^K^K) z i)`;
                     `partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K)`]
        SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_REWRITE_TAC[MATRIFY_VECTORIZE; RDT_BILINEAR_MATMUL];
      MP_TAC(ISPECL [`\(u:real^(K,K)finite_prod) (v:real^K). (matrify u:real^K^K) ** v`;
                     `&1`; `l:num list`; `S:real^(1,N)finite_sum->bool`;
                     `\z. vectorize((b:real^(1,N)finite_sum->num->real^K^K) z i)`;
                     `partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K)`;
                     `z:real^(1,N)finite_sum`] RDT_SUBJET_BILINEAR) THEN
      ASM_REWRITE_TAC[REAL_POS; RDT_BILINEAR_MATMUL; MATRIFY_VECTORIZE] THEN REWRITE_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S (\z. (c:real^(1,N)finite_sum->real^K^K) z ** (V:real^(1,N)finite_sum->real^K) z) /\
    pde_subjet l (\z. c z ** V z) z <= pde_subjet l (\z. vectorize(c z)) z * pde_subjet l V z`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                     `\(u:real^(K,K)finite_prod) (v:real^K). (matrify u:real^K^K) ** v`;
                     `\z. vectorize((c:real^(1,N)finite_sum->real^K^K) z)`;
                     `V:real^(1,N)finite_sum->real^K`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_REWRITE_TAC[MATRIFY_VECTORIZE; RDT_BILINEAR_MATMUL];
      MP_TAC(ISPECL [`\(u:real^(K,K)finite_prod) (v:real^K). (matrify u:real^K^K) ** v`;
                     `&1`; `l:num list`; `S:real^(1,N)finite_sum->bool`;
                     `\z. vectorize((c:real^(1,N)finite_sum->real^K^K) z)`;
                     `V:real^(1,N)finite_sum->real^K`; `z:real^(1,N)finite_sum`]
        RDT_SUBJET_BILINEAR) THEN
      ASM_REWRITE_TAC[REAL_POS; RDT_BILINEAR_MATMUL; MATRIFY_VECTORIZE] THEN REWRITE_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  (* the sums *)
  SUBGOAL_THEN
   `smooth_map_on S
      (\z. vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
             (\j. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
                  partial_derivative (1 + i) (partial_derivative (1 + j)
                    (V:real^(1,N)finite_sum->real^K)) z))) /\
    smooth_map_on S
      (\z. vsum(1..dimindex(:N))
             (\i. (b:real^(1,N)finite_sum->num->real^K^K) z i ** partial_derivative (1 + i) V z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_stop (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
             (V:real^(1,N)finite_sum->real^K) =
    (\z. vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
           (\j. a z$i$j % partial_derivative (1 + i) (partial_derivative (1 + j) V) z)) +
         (vsum(1..dimindex(:N)) (\i. b z i ** partial_derivative (1 + i) V z) +
          c z ** V z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_stop; VECTOR_ADD_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `pde_subjet l (\z. vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
       (\j. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
            partial_derivative (1 + i) (partial_derivative (1 + j)
              (V:real^(1,N)finite_sum->real^K)) z))) z +
    pde_subjet l (\z. vsum(1..dimindex(:N))
       (\i. (b:real^(1,N)finite_sum->num->real^K^K) z i ** partial_derivative (1 + i) V z) +
       (c:real^(1,N)finite_sum->real^K^K) z ** V z) z` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`l:num list`; `S:real^(1,N)finite_sum->bool`;
     `\z. vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
       (\j. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
            partial_derivative (1 + i) (partial_derivative (1 + j)
              (V:real^(1,N)finite_sum->real^K)) z))`;
     `\z. vsum(1..dimindex(:N))
       (\i. (b:real^(1,N)finite_sum->num->real^K^K) z i ** partial_derivative (1 + i) V z) +
       (c:real^(1,N)finite_sum->real^K^K) z ** V z`; `z:real^(1,N)finite_sum`] RDT_SUBJET_ADD) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`l:num list`; `S:real^(1,N)finite_sum->bool`;
     `\i z. vsum(1..dimindex(:N))
       (\j. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
            partial_derivative (1 + i) (partial_derivative (1 + j)
              (V:real^(1,N)finite_sum->real^K)) z)`;
     `1..dimindex(:N)`; `z:real^(1,N)finite_sum`] RDT_SUBJET_VSUM) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l:num list`; `S:real^(1,N)finite_sum->bool`;
     `\j z. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
            partial_derivative (1 + i) (partial_derivative (1 + j)
              (V:real^(1,N)finite_sum->real^K)) z`;
     `1..dimindex(:N)`; `z:real^(1,N)finite_sum`] RDT_SUBJET_VSUM) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `pde_subjet l (\z. vsum(1..dimindex(:N))
       (\i. (b:real^(1,N)finite_sum->num->real^K^K) z i **
            partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K) z)) z +
    pde_subjet l (\z. (c:real^(1,N)finite_sum->real^K^K) z ** V z) z` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`l:num list`; `S:real^(1,N)finite_sum->bool`;
     `\z. vsum(1..dimindex(:N))
       (\i. (b:real^(1,N)finite_sum->num->real^K^K) z i **
            partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K) z)`;
     `\z. (c:real^(1,N)finite_sum->real^K^K) z ** V z`; `z:real^(1,N)finite_sum`]
      RDT_SUBJET_ADD) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l:num list`; `S:real^(1,N)finite_sum->bool`;
     `\i z. (b:real^(1,N)finite_sum->num->real^K^K) z i **
            partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K) z`;
     `1..dimindex(:N)`; `z:real^(1,N)finite_sum`] RDT_SUBJET_VSUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The space-time representative rdt_strep of a family in a chart, the       *)
(* space-time inner maps rdt_stkc and rdt_stkf, and the coefficients and the *)
(* forcing of a step as compositions of the fixed smooth maps rdt_phia,      *)
(* rdt_phib, rdt_phic, rdt_psi with these inner maps.                        *)
(* ------------------------------------------------------------------------- *)

let rdt_hv = new_definition
 `rdt_hv (H:real^N->real^N^N) (y:real^N) = pastecart (rdt_gv H y) (rdt_gdv H y)`;;

let RDT_HV_SMOOTH = prove
 (`!U (H:real^N->real^N^N). metric_field U H ==> smooth_map_on U (rdt_hv H)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rdt_hv (H:real^N->real^N^N) = (\y. pastecart (rdt_gv H y) (rdt_gdv H y))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rdt_hv]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN REWRITE_TAC[ETA_AX] THEN
  ASM_MESON_TAC[RDT_GV_SMOOTH; RDT_GDV_SMOOTH; metric_field]);;

let rdt_strep = new_definition
 `rdt_strep (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
            (v:real->A->real^N^N) (w:real^(1,N)finite_sum) =
    (vectorize:real^N^N->real^(N,N)finite_prod)
      (metric_local atlas c (v (drop(fstcart w))) (sndcart w))`;;

let rdt_stkc = new_definition
 `rdt_stkc (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
           (v:real->A->real^N^N) (h:A->real^N^N) (w:real^(1,N)finite_sum) =
    pastecart (rdt_strep atlas c v w) (rdt_hv (metric_local atlas c h) (sndcart w))`;;

let rdt_stkf = new_definition
 `rdt_stkf (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
           (v:real->A->real^N^N) (h:A->real^N^N) (w:real^(1,N)finite_sum) =
    pastecart (rdt_strep atlas c v w)
      (pastecart ((vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
                    (lambda i. partial_derivative (1 + i) (rdt_strep atlas c v) w))
                 (rdt_hv (metric_local atlas c h) (sndcart w)))`;;

let RDT_STREP_ALT = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) c (v:real->A->real^N^N).
     rdt_strep atlas c v =
     (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
            (metric_local atlas c (v (drop(fstcart w))) (sndcart w)))`,
  REWRITE_TAC[FUN_EQ_THM; rdt_strep]);;

let RDT_ST_COEF_FACTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c a b (h:A->real^N^N)
    (gk:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (gk t)) /\ pde_tfam_from atlas a b gk
     ==> open (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c)) /\
         smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
                       (rdt_strep atlas c gk) /\
         smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
                       (rdt_stkc atlas c gk h) /\
         smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
                       (rdt_stkf atlas c gk h) /\
         IMAGE (rdt_stkc atlas c gk h) (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
         SUBSET {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)} /\
         IMAGE (rdt_stkf atlas c gk h) (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
         SUBSET {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)} /\
         (!w. w IN interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c)
              ==> vectorize(pde_mlaa atlas c gk (drop(fstcart w)) (sndcart w)) =
                  rdt_phia(rdt_stkc atlas c gk h w) /\
                  (!i. vectorize(pde_mlbt atlas c gk h (drop(fstcart w)) (sndcart w) i) =
                       rdt_phib i (rdt_stkc atlas c gk h w)) /\
                  vectorize(pde_mlct atlas c gk h (drop(fstcart w)) (sndcart w)) =
                  rdt_phic(rdt_stkc atlas c gk h w) /\
                  vectorize(metric_local atlas c
                    (\x. pde_rdt_rhs atlas h (gk (drop(fstcart w))) x -
                         pde_trhess atlas (gk (drop(fstcart w))) h (gk (drop(fstcart w))) x)
                    (sndcart w)) = rdt_psi(rdt_stkf atlas c gk h w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `U = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                metric_field U (metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN CONJ_TAC THENL
     [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ASM_MESON_TAC[riemannian_metric]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N))`
  ASSUME_TAC THENL
   [REWRITE_TAC[RDT_STREP_ALT] THEN MAP_EVERY EXPAND_TAC ["S"; "U"] THEN
    MATCH_MP_TAC RDT_ST_REP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN S ==> a < drop(fstcart w) /\ drop(fstcart w) < b /\
                   sndcart(w:real^(1,N)finite_sum) IN U`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                                    SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN S ==> metric_field U (metric_local atlas (c:(A->bool)#(A->real^N))
                                     ((gk:real->A->real^N^N) (drop(fstcart(w:real^(1,N)finite_sum)))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas ((gk:real->A->real^N^N) (drop(fstcart(w:real^(1,N)finite_sum))))`
    MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S (\w:real^(1,N)finite_sum.
       rdt_hv (metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N)) (sndcart w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_SMOOTH_COMPOSE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[RDT_HV_SMOOTH] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S (\w. (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
                           (lambda i. partial_derivative (1 + i)
                              (rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N)) w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `rdt_stkc atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N) (h:A->real^N^N) =
      (\w. pastecart (rdt_strep atlas c gk w) (rdt_hv (metric_local atlas c h) (sndcart w)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rdt_stkc]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    SUBGOAL_THEN
     `rdt_stkf atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N) (h:A->real^N^N) =
      (\w. pastecart (rdt_strep atlas c gk w)
             (pastecart ((vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
                           (lambda i. partial_derivative (1 + i) (rdt_strep atlas c gk) w))
                        (rdt_hv (metric_local atlas c h) (sndcart w))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rdt_stkf]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; rdt_stkc; FSTCART_PASTECART; rdt_strep;
                MATRIFY_VECTORIZE] THEN
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `metric_local atlas (c:(A->bool)#(A->real^N))
                      ((gk:real->A->real^N^N) (drop(fstcart(w:real^(1,N)finite_sum))))`;
                   `sndcart(w:real^(1,N)finite_sum)`] LRG_METRIC_INVERTIBLE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; rdt_stkf; FSTCART_PASTECART; rdt_strep;
                MATRIFY_VECTORIZE] THEN
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `metric_local atlas (c:(A->bool)#(A->real^N))
                      ((gk:real->A->real^N^N) (drop(fstcart(w:real^(1,N)finite_sum))))`;
                   `sndcart(w:real^(1,N)finite_sum)`] LRG_METRIC_INVERTIBLE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  SUBGOAL_THEN `a < drop(fstcart(w:real^(1,N)finite_sum)) /\ drop(fstcart w) < b /\
                sndcart w IN U`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field U (metric_local atlas (c:(A->bool)#(A->real^N))
                      ((gk:real->A->real^N^N) (drop(fstcart(w:real^(1,N)finite_sum)))))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
      (lambda i. partial_derivative (1 + i)
                   (rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N)) w) =
    rdt_dgv (metric_local atlas c (gk (drop(fstcart w)))) (sndcart(w:real^(1,N)finite_sum))`
  ASSUME_TAC THENL
   [REWRITE_TAC[rdt_dgv] THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[CART_EQ] THEN SIMP_TAC[LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N)`;
                   `fstcart(w:real^(1,N)finite_sum)`; `sndcart(w:real^(1,N)finite_sum)`; `i:num`]
      PDE_ST_SLICE_PARTIAL) THEN
    REWRITE_TAC[PASTECART_FST_SND] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; rdt_strep; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rdt_stkc atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N) (h:A->real^N^N) w =
    rdt_kc (metric_local atlas c (gk (drop(fstcart w)))) (metric_local atlas c h) (sndcart w)`
  SUBST1_TAC THENL [REWRITE_TAC[rdt_stkc; rdt_kc; rdt_strep; rdt_hv]; ALL_TAC] THEN
  SUBGOAL_THEN
   `rdt_stkf atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N) (h:A->real^N^N) w =
    rdt_kf (metric_local atlas c (gk (drop(fstcart w)))) (metric_local atlas c h) (sndcart w)`
  SUBST1_TAC THENL
   [REWRITE_TAC[rdt_stkf; rdt_kf; rdt_hv] THEN ASM_REWRITE_TAC[rdt_strep]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pde_mlaa; RDT_PHIA_KC];
    GEN_TAC THEN REWRITE_TAC[pde_mlbt] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RDT_PHIB_KC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[pde_mlct] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RDT_PHIC_KC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `h:A->real^N^N`;
                 `(gk:real->A->real^N^N) (drop(fstcart(w:real^(1,N)finite_sum)))`]
    RDT_FORCING_CHART) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `sndcart(w:real^(1,N)finite_sum)` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for the uniform bounds of the space-time jets: the space-time     *)
(* set, finite families of uniform bounds, parabolic jets of a family,       *)
(* sub-jets of time-free functions, compositions with the fixed coefficient  *)
(* maps, the smoothness of the coefficients in space-time, the time trade on *)
(* the whole space-time set, and the bound of the jets of the time           *)
(* derivative by sub-jets of the coefficients and of the solution.           *)
(* ------------------------------------------------------------------------- *)

let RDT_IN_STSET = prove
 (`!a b (U:real^N->bool) (w:real^(1,N)finite_sum).
     w IN interval(lift a,lift b) PCROSS U <=>
     a < drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(ISPEC `w:real^(1,N)finite_sum` PASTECART_FST_SND)) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1;
              LIFT_DROP; CONJ_ASSOC]);;

let RDT_SUM_GE_TERM = prove
 (`!f:num->real n i. (!j. 1 <= j /\ j <= n ==> &0 <= f j) /\ 1 <= i /\ i <= n
                     ==> f i <= sum(1..n) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{i:num}`; `1..n`; `f:num->real`] SUM_SUBSET_SIMPLE) THEN
  ASM_SIMP_TAC[SUM_SING; FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; IN_DIFF]);;

let RDT_FINITE_UNIF = prove
 (`!(P:num list->bool) (Q:real^M->bool) (f:num list->num->real^M->real).
     FINITE {l | P l} /\ (!l. P l ==> ?B. !k w. Q w ==> f l k w <= B)
     ==> ?B. !l k w. P l /\ Q w ==> f l k w <= B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `Bf:num list->real` o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  MP_TAC(ISPECL [`Bf:num list->real`; `{l:num list | P l}`] UPPER_BOUND_FINITE_SET_REAL) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `B:real` THEN ASM_MESON_TAC[REAL_LE_TRANS]);;

let RDT_PJET_UNIF = prove
 (`!(Fv:num->real^M->real^K) s r n.
     (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ pde_ntime l <= n
          ==> ?B. !k w. w IN s ==> norm(iterated_partial l (Fv k) w) <= B)
     ==> ?B. !k w. w IN s ==> pde_pjet r n (Fv k) w <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ pde_ntime l <= n /\
         LENGTH l <= r + n /\ LENGTH l - pde_ntime l <= r`;
    `\w:real^M. w IN s`;
    `\l k w. norm(iterated_partial l ((Fv:num->real^M->real^K) k) w)`] RDT_FINITE_UNIF) THEN
  REWRITE_TAC[PDE_PJET_FINITE] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC
   `&(CARD {l | ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ pde_ntime l <= n /\
                LENGTH l <= r + n /\ LENGTH l - pde_ntime l <= r}) * B` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_PJET_LE_BOUND THEN ASM_MESON_TAC[]);;

let RDT_SUBJET_TIMEFREE = prove
 (`!U (Y:real^N->real^P) l.
     open U /\ smooth_map_on U Y /\ ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
     ==> ?C. &0 <= C /\
             !z. z IN (:real^1) PCROSS U
                 ==> pde_subjet l (\w. Y(sndcart w)) z <= C * pde_jetn (LENGTH l) Y (sndcart z)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `r = LENGTH(l:num list) - pde_ntime l` THEN
  ABBREV_TAC `n = pde_ntime(l:num list)` THEN
  EXISTS_TAC `&2 pow (LENGTH(l:num list)) *
              &(CARD {l':num list | ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l' /\
                                    pde_ntime l' <= n /\ LENGTH l' <= r + n /\
                                    LENGTH l' - pde_ntime l' <= r})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 pow (LENGTH(l:num list)) *
              pde_pjet r n (\w:real^(1,N)finite_sum. (Y:real^N->real^P)(sndcart w)) z` THEN
  CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "n"] THEN MATCH_MP_TAC PDE_SUBJET_PJET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RDT_PJET_LE_BOUND THEN
  X_GEN_TAC `l':num list` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_jetn (LENGTH(l':num list)) (Y:real^N->real^P) (sndcart(z:real^(1,N)finite_sum))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RDT_ST_TIMEFREE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_JETN_MONO THEN
    MP_TAC(SPEC `l:num list` PDE_NTIME_LE) THEN ASM_ARITH_TAC]);;

let RDT_OPEN_DETSET = prove
 (`open {x:real^((N,N)finite_prod,Q)finite_sum |
         ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}`,
  MATCH_MP_TAC RDT_OPEN_INV THEN REWRITE_TAC[LINEAR_FSTCART; ETA_AX]);;

let RDT_SMOOTH_COMPOSE_DET = prove
 (`!(Phi:real^((N,N)finite_prod,Q)finite_sum->real^P)
    (K:real^M->real^((N,N)finite_prod,Q)finite_sum) U.
     open U /\ smooth_map_on U K /\
     IMAGE K U SUBSET {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)} /\
     smooth_map_on {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)} Phi
     ==> smooth_map_on U (\z. Phi(K z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_SMOOTH_COMPOSE THEN
  EXISTS_TAC `{x:real^((N,N)finite_prod,Q)finite_sum |
               ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}` THEN
  ASM_REWRITE_TAC[RDT_OPEN_DETSET]);;

let RDT_SMOOTH_SNDCART = prove
 (`!U (Y:real^N->real^P) (s:real^(M,N)finite_sum->bool).
     open U /\ smooth_map_on U Y /\ open s /\ IMAGE sndcart s SUBSET U
     ==> smooth_map_on s (\w. Y(sndcart w))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_SMOOTH_COMPOSE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `(:real^(M,N)finite_sum)` THEN
  REWRITE_TAC[SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART]);;

let RDT_SUBJET_COMPOSE_SK = prove
 (`!(Phi:real^((N,N)finite_prod,Q)finite_sum->real^P) K1 R n.
     smooth_map_on {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)} Phi
     ==> ?C. &0 <= C /\
             !(K:real^(1,N)finite_sum->real^((N,N)finite_prod,Q)finite_sum) U x l.
               open U /\ smooth_map_on U K /\
               IMAGE K U SUBSET
                 {x | ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)} /\
               x IN U /\ K x IN rdt_sk K1 R /\
               ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ LENGTH l <= n
               ==> pde_subjet l (\z. Phi(K z)) x <= C * (&1 + pde_subjet l K x) pow n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_SUBJET_COMPOSE_UNIF THEN
  ASM_REWRITE_TAC[RDT_SK_COMPACT; RDT_SK_SUBSET; RDT_OPEN_DETSET]);;

let RDT_ST_HV_SMOOTH = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c (h:A->real^N^N) a b.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h
     ==> open (IMAGE (SND c) (FST c)) /\
         smooth_map_on (IMAGE (SND c) (FST c)) (rdt_hv (metric_local atlas c h)) /\
         smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
           (\w. rdt_hv (metric_local atlas c h) (sndcart w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)) /\
                metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c (h:A->real^N^N))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ASM_MESON_TAC[riemannian_metric]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RDT_HV_SMOOTH] THEN
  MATCH_MP_TAC RDT_SMOOTH_SNDCART THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_SIMP_TAC[RDT_HV_SMOOTH; OPEN_PCROSS; OPEN_INTERVAL; ETA_AX] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RDT_IN_STSET] THEN SIMP_TAC[]);;

let RDT_ST_COEF_SMOOTH = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c a b (h:A->real^N^N)
    (gk:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (gk t)) /\ pde_tfam_from atlas a b gk
     ==> smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
           (\z. vectorize(pde_mlaa atlas c gk (drop(fstcart z)) (sndcart z))) /\
         (!i. smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
                (\z. vectorize(pde_mlbt atlas c gk h (drop(fstcart z)) (sndcart z) i))) /\
         smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
           (\z. vectorize(pde_mlct atlas c gk h (drop(fstcart z)) (sndcart z))) /\
         smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
           (\z. vectorize(metric_local atlas c
                  (\x. pde_rdt_rhs atlas h (gk (drop(fstcart z))) x -
                       pde_trhess atlas (gk (drop(fstcart z))) h (gk (drop(fstcart z))) x)
                  (sndcart z)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RDT_ST_COEF_FACTS) THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TEXT_SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z:real^(1,N)finite_sum. rdt_phia(rdt_stkc atlas (c:(A->bool)#(A->real^N))
                                             (gk:real->A->real^N^N) (h:A->real^N^N) z)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC RDT_SMOOTH_COMPOSE_DET THEN
    ASM_REWRITE_TAC[RDT_PHIA_SMOOTH; ETA_AX];
    X_GEN_TAC `i:num` THEN MATCH_MP_TAC TEXT_SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z:real^(1,N)finite_sum. rdt_phib i (rdt_stkc atlas (c:(A->bool)#(A->real^N))
                                             (gk:real->A->real^N^N) (h:A->real^N^N) z)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC RDT_SMOOTH_COMPOSE_DET THEN
    ASM_REWRITE_TAC[RDT_PHIB_SMOOTH; ETA_AX];
    MATCH_MP_TAC TEXT_SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z:real^(1,N)finite_sum. rdt_phic(rdt_stkc atlas (c:(A->bool)#(A->real^N))
                                             (gk:real->A->real^N^N) (h:A->real^N^N) z)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC RDT_SMOOTH_COMPOSE_DET THEN
    ASM_REWRITE_TAC[RDT_PHIC_SMOOTH; ETA_AX];
    MATCH_MP_TAC TEXT_SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z:real^(1,N)finite_sum. rdt_psi(rdt_stkf atlas (c:(A->bool)#(A->real^N))
                                             (gk:real->A->real^N^N) (h:A->real^N^N) z)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC RDT_SMOOTH_COMPOSE_DET THEN
    ASM_REWRITE_TAC[RDT_PSI_SMOOTH; ETA_AX]]);;

let RDT_ST_COEF_SUBJETS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c a b (h:A->real^N^N) K1 R RF n.
     ?C. &0 <= C /\
         !(gk:real->A->real^N^N) l w.
           smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
           (!t. a <= t /\ t < b ==> riemannian_metric atlas (gk t)) /\
           pde_tfam_from atlas a b gk /\
           w IN interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c) /\
           rdt_stkc atlas c gk h w IN rdt_sk K1 R /\
           rdt_stkf atlas c gk h w IN rdt_sk K1 RF /\
           ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ LENGTH l <= n
           ==> pde_subjet l (\z. vectorize(pde_mlaa atlas c gk (drop(fstcart z)) (sndcart z))) w
               <= C * (&1 + pde_subjet l (rdt_stkc atlas c gk h) w) pow n /\
               (!i. 1 <= i /\ i <= dimindex(:N)
                    ==> pde_subjet l (\z. vectorize(pde_mlbt atlas c gk h (drop(fstcart z))
                                                              (sndcart z) i)) w
                        <= C * (&1 + pde_subjet l (rdt_stkc atlas c gk h) w) pow n) /\
               pde_subjet l (\z. vectorize(pde_mlct atlas c gk h (drop(fstcart z)) (sndcart z))) w
               <= C * (&1 + pde_subjet l (rdt_stkc atlas c gk h) w) pow n /\
               pde_subjet l (\z. vectorize(metric_local atlas c
                   (\x. pde_rdt_rhs atlas h (gk (drop(fstcart z))) x -
                        pde_trhess atlas (gk (drop(fstcart z))) h (gk (drop(fstcart z))) x)
                   (sndcart z))) w
               <= C * (&1 + pde_subjet l (rdt_stkf atlas c gk h) w) pow n`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`K1:real`; `R:real`; `n:num`]
    (MATCH_MP RDT_SUBJET_COMPOSE_SK RDT_PHIA_SMOOTH)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ca:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ca"))) THEN
  MP_TAC(SPECL [`K1:real`; `R:real`; `n:num`]
    (MATCH_MP RDT_SUBJET_COMPOSE_SK RDT_PHIC_SMOOTH)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cc"))) THEN
  MP_TAC(SPECL [`K1:real`; `RF:real`; `n:num`]
    (MATCH_MP RDT_SUBJET_COMPOSE_SK RDT_PSI_SMOOTH)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cf:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cf"))) THEN
  MP_TAC(GEN `i:num` (SPECL [`K1:real`; `R:real`; `n:num`]
    (MATCH_MP RDT_SUBJET_COMPOSE_SK (SPEC `i:num` RDT_PHIB_SMOOTH)))) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cb:num->real` (LABEL_TAC "cb")) THEN
  SUBGOAL_THEN `&0 <= sum(1..dimindex(:N)) (Cb:num->real) /\
                !i. 1 <= i /\ i <= dimindex(:N) ==> Cb i <= sum(1..dimindex(:N)) Cb`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_SUM_GE_TERM THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `Ca + Cc + Cf + sum(1..dimindex(:N)) (Cb:num->real)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `a:real`; `b:real`; `h:A->real^N^N`;
                 `gk:real->A->real^N^N`] RDT_ST_COEF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  STRIP_TAC THEN
  ABBREV_TAC `s1 = pde_subjet l (rdt_stkc atlas (c:(A->bool)#(A->real^N))
                                   (gk:real->A->real^N^N) (h:A->real^N^N)) w` THEN
  ABBREV_TAC `s2 = pde_subjet l (rdt_stkf atlas (c:(A->bool)#(A->real^N))
                                   (gk:real->A->real^N^N) (h:A->real^N^N)) w` THEN
  SUBGOAL_THEN `&0 <= (&1 + s1) pow n /\ &0 <= (&1 + s2) pow n` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN REWRITE_TAC[PDE_SUBJET_POS];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ca * (&1 + s1) pow n` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_subjet l (\z. rdt_phia(rdt_stkc atlas (c:(A->bool)#(A->real^N))
                                       (gk:real->A->real^N^N) (h:A->real^N^N) z)) w` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC RDT_SUBJET_LOCAL THEN
        EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[];
        EXPAND_TAC "s1" THEN USE_THEN "ca" MATCH_MP_TAC THEN
        EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Cb:num->real) i * (&1 + s1) pow n` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_subjet l (\z. rdt_phib i (rdt_stkc atlas (c:(A->bool)#(A->real^N))
                                       (gk:real->A->real^N^N) (h:A->real^N^N) z)) w` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC RDT_SUBJET_LOCAL THEN
        EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[];
        EXPAND_TAC "s1" THEN USE_THEN "cb" (MP_TAC o CONJUNCT2 o SPEC `i:num`) THEN
        DISCH_THEN MATCH_MP_TAC THEN
        EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c /\ x <= s ==> x <= a + b + c + s`) THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Cc * (&1 + s1) pow n` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_subjet l (\z. rdt_phic(rdt_stkc atlas (c:(A->bool)#(A->real^N))
                                       (gk:real->A->real^N^N) (h:A->real^N^N) z)) w` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC RDT_SUBJET_LOCAL THEN
        EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[];
        EXPAND_TAC "s1" THEN USE_THEN "cc" MATCH_MP_TAC THEN
        EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Cf * (&1 + s2) pow n` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_subjet l (\z. rdt_psi(rdt_stkf atlas (c:(A->bool)#(A->real^N))
                                       (gk:real->A->real^N^N) (h:A->real^N^N) z)) w` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC RDT_SUBJET_LOCAL THEN
        EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[];
        EXPAND_TAC "s2" THEN USE_THEN "cf" MATCH_MP_TAC THEN
        EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let RDT_ST_TRADE_ON = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (k:real->A->real^N^N) h f v0
    (v:real->A->real^N^N) c w.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_mlin_sol (top,atlas) a b k h f v0 v /\
     w IN interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c)
     ==> partial_derivative 1 (rdt_strep atlas c v) w =
         pde_stop (\w. pde_mlaa atlas c k (drop(fstcart w)) (sndcart w))
                  (\w i. pde_mlbt atlas c k h (drop(fstcart w)) (sndcart w) i)
                  (\w. pde_mlct atlas c k h (drop(fstcart w)) (sndcart w))
                  (rdt_strep atlas c v) w +
         vectorize(metric_local atlas c (f (drop(fstcart w))) (sndcart w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(w:real^(1,N)finite_sum) IN
                interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  REWRITE_TAC[RDT_IN_STSET] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `f:real->A->real^N^N`;
                 `v0:A->real^N^N`; `v:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `drop(fstcart(w:real^(1,N)finite_sum))`; `sndcart(w:real^(1,N)finite_sum)`]
    RDT_TRADE) THEN
  ASM_REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND; RDT_STREP_ALT]);;

let RDT_ST_D1_BOUND = prove
 (`!S (V:real^(1,N)finite_sum->real^K) (a:real^(1,N)finite_sum->real^N^N)
    (b:real^(1,N)finite_sum->num->real^K^K) c (Fv:real^(1,N)finite_sum->real^K) l w
    QC QF PV PD PDD.
     open S /\ w IN S /\ smooth_map_on S V /\ smooth_map_on S (\z. vectorize(a z)) /\
     (!i. smooth_map_on S (\z. vectorize(b z i))) /\ smooth_map_on S (\z. vectorize(c z)) /\
     smooth_map_on S Fv /\
     (!z. z IN S ==> partial_derivative 1 V z = pde_stop a b c V z + Fv z) /\
     ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
     pde_subjet l (\z. vectorize(a z)) w <= QC /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> pde_subjet l (\z. vectorize(b z i)) w <= QC) /\
     pde_subjet l (\z. vectorize(c z)) w <= QC /\ pde_subjet l Fv w <= QF /\
     pde_subjet l V w <= PV /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> pde_subjet l (partial_derivative (1 + i) V) w <= PD) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> pde_subjet l (partial_derivative (1 + i) (partial_derivative (1 + j) V)) w <= PDD)
     ==> norm(iterated_partial l (partial_derivative 1 V) w) <=
         &(dimindex(:N)) * &(dimindex(:N)) * QC * PDD + &(dimindex(:N)) * QC * PD + QC * PV + QF`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on S (pde_stop (a:real^(1,N)finite_sum->real^N^N)
                       (b:real^(1,N)finite_sum->num->real^K^K) c (V:real^(1,N)finite_sum->real^K))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TEXT_SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z. partial_derivative 1 (V:real^(1,N)finite_sum->real^K) z -
                    (Fv:real^(1,N)finite_sum->real^K) z` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `iterated_partial l (partial_derivative 1 (V:real^(1,N)finite_sum->real^K)) w =
    iterated_partial l (\z. pde_stop (a:real^(1,N)finite_sum->real^N^N)
                              (b:real^(1,N)finite_sum->num->real^K^K) c V z +
                            (Fv:real^(1,N)finite_sum->real^K) z) w`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`l:num list`; `S:real^(1,N)finite_sum->bool`;
                   `partial_derivative 1 (V:real^(1,N)finite_sum->real^K)`;
                   `\z. pde_stop (a:real^(1,N)finite_sum->real^N^N)
                          (b:real^(1,N)finite_sum->num->real^K^K) c V z +
                        (Fv:real^(1,N)finite_sum->real^K) z`]
      TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_subjet l (\z. pde_stop (a:real^(1,N)finite_sum->real^N^N)
                                 (b:real^(1,N)finite_sum->num->real^K^K) c
                                 (V:real^(1,N)finite_sum->real^K) z +
                               (Fv:real^(1,N)finite_sum->real^K) z) w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RDT_ITERATED_LE_SUBJET THEN EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_subjet l (pde_stop (a:real^(1,N)finite_sum->real^N^N)
                              (b:real^(1,N)finite_sum->num->real^K^K) c
                              (V:real^(1,N)finite_sum->real^K)) w +
              pde_subjet l (Fv:real^(1,N)finite_sum->real^K) w` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`l:num list`; `S:real^(1,N)finite_sum->bool`;
                   `pde_stop (a:real^(1,N)finite_sum->real^N^N)
                      (b:real^(1,N)finite_sum->num->real^K^K) c (V:real^(1,N)finite_sum->real^K)`;
                   `Fv:real^(1,N)finite_sum->real^K`; `w:real^(1,N)finite_sum`] RDT_SUBJET_ADD) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= a + b + c /\ y <= d ==> x + y <= a + b + c + d`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `a:real^(1,N)finite_sum->real^N^N`;
                 `b:real^(1,N)finite_sum->num->real^K^K`; `c:real^(1,N)finite_sum->real^K^K`;
                 `V:real^(1,N)finite_sum->real^K`; `l:num list`; `w:real^(1,N)finite_sum`]
    RDT_SUBJET_STOP) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. QC * PDD))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[PDE_SUBJET_POS];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. QC * PD)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[PDE_SUBJET_POS];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[PDE_SUBJET_POS]]);;

let RDT_STKC_SUBJET = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c a b (h:A->real^N^N)
    (gk:real->A->real^N^N) l w.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (gk t)) /\ pde_tfam_from atlas a b gk /\
     w IN interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c)
     ==> pde_subjet l (rdt_stkc atlas c gk h) w <=
         pde_subjet l (rdt_strep atlas c gk) w +
         pde_subjet l (\z. rdt_hv (metric_local atlas c h) (sndcart z)) w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `a:real`; `b:real`; `h:A->real^N^N`;
                 `gk:real->A->real^N^N`] RDT_ST_COEF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `h:A->real^N^N`; `a:real`; `b:real`]
    RDT_ST_HV_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `rdt_stkc atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N) (h:A->real^N^N) =
    (\z. pastecart (rdt_strep atlas c gk z) (rdt_hv (metric_local atlas c h) (sndcart z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rdt_stkc]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num list`;
                 `interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N)`;
                 `\z:real^(1,N)finite_sum. rdt_hv (metric_local atlas (c:(A->bool)#(A->real^N))
                                                    (h:A->real^N^N)) (sndcart z)`;
                 `w:real^(1,N)finite_sum`] RDT_SUBJET_PASTECART) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RDT_STKF_SUBJET = prove
 (`?Bv. &0 <= Bv /\
        !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c a b (h:A->real^N^N)
         (gk:real->A->real^N^N) l w.
          smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
          (!t. a <= t /\ t < b ==> riemannian_metric atlas (gk t)) /\
          pde_tfam_from atlas a b gk /\
          w IN interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c)
          ==> pde_subjet l (rdt_stkf atlas c gk h) w <=
              pde_subjet l (rdt_strep atlas c gk) w +
              Bv * sum(1..dimindex(:N))
                     (\i. pde_subjet l (partial_derivative (1 + i) (rdt_strep atlas c gk)) w) +
              pde_subjet l (\z. rdt_hv (metric_local atlas c h) (sndcart z)) w`,
  MP_TAC(INST_TYPE [`:N`,`:P`; `:(N,N)finite_prod`,`:K`; `:(1,N)finite_sum`,`:M`]
    RDT_SUBJET_VLAMBDA) THEN
  DISCH_THEN(X_CHOOSE_THEN `Bv:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bv"))) THEN
  EXISTS_TAC `Bv:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `a:real`; `b:real`; `h:A->real^N^N`;
                 `gk:real->A->real^N^N`] RDT_ST_COEF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `h:A->real^N^N`; `a:real`; `b:real`]
    RDT_ST_HV_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  SUBGOAL_THEN
   `smooth_map_on S (\z. (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
                           (lambda i. partial_derivative (1 + i)
                              (rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N)) z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rdt_stkf atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N) (h:A->real^N^N) =
    (\z. pastecart (rdt_strep atlas c gk z)
           (pastecart ((vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
                         (lambda i. partial_derivative (1 + i) (rdt_strep atlas c gk) z))
                      (rdt_hv (metric_local atlas c h) (sndcart z))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rdt_stkf]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `pde_subjet l (rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N)) w +
    pde_subjet l (\z. pastecart
       ((vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
          (lambda i. partial_derivative (1 + i) (rdt_strep atlas c gk) z))
       (rdt_hv (metric_local atlas c (h:A->real^N^N)) (sndcart z))) w` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`l:num list`; `S:real^(1,N)finite_sum->bool`;
                   `rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N)`;
                   `\z. pastecart
                          ((vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
                             (lambda i. partial_derivative (1 + i)
                                (rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N)) z))
                          (rdt_hv (metric_local atlas c (h:A->real^N^N)) (sndcart z))`;
                   `w:real^(1,N)finite_sum`] RDT_SUBJET_PASTECART) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC; REAL_LE_LADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `pde_subjet l (\z. (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
                        (lambda i. partial_derivative (1 + i)
                           (rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N)) z)) w +
    pde_subjet l (\z. rdt_hv (metric_local atlas c (h:A->real^N^N)) (sndcart z)) w` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`l:num list`; `S:real^(1,N)finite_sum->bool`;
                   `\z. (vectorize:real^(N,N)finite_prod^N->real^(N,(N,N)finite_prod)finite_prod)
                          (lambda i. partial_derivative (1 + i)
                             (rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N)) z)`;
                   `\z:real^(1,N)finite_sum. rdt_hv (metric_local atlas (c:(A->bool)#(A->real^N))
                                                      (h:A->real^N^N)) (sndcart z)`;
                   `w:real^(1,N)finite_sum`] RDT_SUBJET_PASTECART) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_RADD] THEN
  USE_THEN "bv" (MP_TAC o SPECL
   [`l:num list`; `S:real^(1,N)finite_sum->bool`;
    `\i. partial_derivative (1 + i)
           (rdt_strep atlas (c:(A->bool)#(A->real^N)) (gk:real->A->real^N^N))`;
    `w:real^(1,N)finite_sum`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The inductive step for the uniform bounds of the space-time               *)
(* jets of the iterates: uniform bounds of the parabolic jets of time order  *)
(* n of all iterates give uniform bounds of the jets of time order n of the  *)
(* time derivatives of all iterates after the first.                         *)
(* ------------------------------------------------------------------------- *)

let RDT_IN_UNIV_PCROSS = prove
 (`!(U:real^N->bool) (w:real^(M,N)finite_sum).
     w IN (:real^M) PCROSS U <=> sndcart w IN U`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(ISPEC `w:real^(M,N)finite_sum` PASTECART_FST_SND)) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; SNDCART_PASTECART]);;

let RDT_POW_BOUND_MONO = prove
 (`!C s X y n. &0 <= C /\ &0 <= s /\ s <= X /\ y <= C * (&1 + s) pow n
               ==> y <= C * (&1 + X) pow n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * (&1 + s) pow n` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

let RDT_ST_STEP = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c a b (g0:A->real^N^N)
    (g:num->real->A->real^N^N) K0 n.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas g0 /\
     compact K0 /\ K0 SUBSET IMAGE (SND c) (FST c) /\
     (!k. pde_tfam_from atlas a b (g k)) /\
     (!k t. a <= t /\ t < b ==> riemannian_metric atlas (g k t)) /\
     (!k. pde_rdt_step (top,atlas) a b g0 (g k) (g (SUC k))) /\
     (?K1. !k t y. a <= t /\ t < b /\ y IN K0
                   ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                              (metric_local atlas c (g k t) y)) <= K1 /\
                       !v. norm v pow 2 <= K1 * (v dot (metric_local atlas c (g k t) y ** v))) /\
     (!r. ?M. !k w. w IN interval(lift a,lift b) PCROSS K0
                    ==> pde_pjet r n (rdt_strep atlas c (g k)) w <= M)
     ==> !l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ pde_ntime l = n
             ==> ?M. !k w. w IN interval(lift a,lift b) PCROSS K0
                           ==> norm(iterated_partial l
                                      (partial_derivative 1 (rdt_strep atlas c (g (SUC k)))) w)
                               <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `l:num list` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "pj" o check (fun th -> rdt_has_const "pde_pjet" th)) THEN
  USE_THEN "pj" (X_CHOOSE_TAC `Mr:real` o SPEC `LENGTH(l:num list) - n`) THEN
  USE_THEN "pj" (X_CHOOSE_TAC `Mr1:real` o SPEC `SUC(LENGTH(l:num list) - n)`) THEN
  USE_THEN "pj" (X_CHOOSE_TAC `Mr2:real` o SPEC `SUC(SUC(LENGTH(l:num list) - n))`) THEN
  USE_THEN "pj" (X_CHOOSE_TAC `M1:real` o SPEC `1:num`) THEN
  (* static facts *)
  SUBGOAL_THEN
   `open (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)) /\
    smooth_map_on (IMAGE (SND c) (FST c)) (rdt_hv (metric_local atlas c (g0:A->real^N^N))) /\
    smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
      (\w. rdt_hv (metric_local atlas c g0) (sndcart w))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_ST_HV_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open (interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                      (rdt_strep atlas c ((g:num->real->A->real^N^N) k))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `c:(A->bool)#(A->real^N)`; `a:real`; `b:real`; `g0:A->real^N^N`;
      `(g:num->real->A->real^N^N) k`] RDT_ST_COEF_FACTS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `rdt_hv (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N))`;
                 `l:num list`] RDT_SUBJET_TIMEFREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `K0:real^N->bool`;
                 `rdt_hv (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N))`;
                 `LENGTH(l:num list)`] RDT_JETS_BOUNDED_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `CJ:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `K0:real^N->bool`;
                 `rdt_hv (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N))`;
                 `0:num`] RDT_JETS_BOUNDED_COMPACT) THEN
  ASM_REWRITE_TAC[RDT_JETN_0] THEN DISCH_THEN(X_CHOOSE_THEN `CJ0:real` STRIP_ASSUME_TAC) THEN
  X_CHOOSE_THEN `Bv:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bvf")) RDT_STKF_SUBJET THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `a:real`; `b:real`; `g0:A->real^N^N`; `K1:real`;
                 `CJ0:real`; `K1 + Bv * &(dimindex(:N)) * M1 + CJ0`; `LENGTH(l:num list)`]
    RDT_ST_COEF_SUBJETS) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cs"))) THEN
  ABBREV_TAC `PV = &2 pow (LENGTH(l:num list)) * Mr` THEN
  ABBREV_TAC `PD = &2 pow (LENGTH(l:num list)) * Mr1` THEN
  ABBREV_TAC `PDD = &2 pow (LENGTH(l:num list)) * Mr2` THEN
  ABBREV_TAC `Chl = C0 * CJ` THEN
  ABBREV_TAC `QC = C * (&1 + PV + Chl) pow (LENGTH(l:num list))` THEN
  ABBREV_TAC `QF = C * (&1 + PV + Bv * &(dimindex(:N)) * PD + Chl) pow (LENGTH(l:num list))` THEN
  EXISTS_TAC `&(dimindex(:N)) * &(dimindex(:N)) * QC * PDD + &(dimindex(:N)) * QC * PD +
              QC * PV + QF` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `w:real^(1,N)finite_sum`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(w:real^(1,N)finite_sum) IN
      interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c) /\
    a < drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN K0 /\
    sndcart w IN IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^(1,N)finite_sum) IN interval(lift a,lift b) PCROSS K0` THEN
    REWRITE_TAC[RDT_IN_STSET] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* sub-jets of the iterates by parabolic jets *)
  SUBGOAL_THEN
   `!f:real^(1,N)finite_sum->real^(N,N)finite_prod.
      pde_subjet l f w <= &2 pow (LENGTH(l:num list)) * pde_pjet (LENGTH l - n) n f w`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`l:num list`; `f:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `w:real^(1,N)finite_sum`] PDE_SUBJET_PJET) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. pde_subjet l (rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) j)) w
        <= PV /\
        (!i. 1 <= i /\ i <= dimindex(:N)
             ==> pde_subjet l (partial_derivative (1 + i) (rdt_strep atlas c (g j))) w <= PD) /\
        (!i i'. 1 <= i /\ i <= dimindex(:N) /\ 1 <= i' /\ i' <= dimindex(:N)
                ==> pde_subjet l (partial_derivative (1 + i)
                                   (partial_derivative (1 + i') (rdt_strep atlas c (g j)))) w
                    <= PDD)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 pow (LENGTH(l:num list)) *
                  pde_pjet (LENGTH l - n) n
                    (rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) j)) w` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "PV" THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ASM_SIMP_TAC[]];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 pow (LENGTH(l:num list)) *
                  pde_pjet (LENGTH l - n) n
                    (partial_derivative (1 + i)
                       (rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) j))) w` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "PD" THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_pjet (SUC(LENGTH(l:num list) - n)) n
                    (rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) j)) w` THEN
      ASM_SIMP_TAC[PDE_PJET_PARTIAL_SPACE];
      MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 pow (LENGTH(l:num list)) *
                  pde_pjet (LENGTH l - n) n
                    (partial_derivative (1 + i) (partial_derivative (1 + i')
                       (rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) j)))) w` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "PDD" THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_pjet (SUC(LENGTH(l:num list) - n)) n
                    (partial_derivative (1 + i')
                       (rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) j))) w` THEN
      ASM_SIMP_TAC[PDE_PJET_PARTIAL_SPACE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_pjet (SUC(SUC(LENGTH(l:num list) - n))) n
                    (rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) j)) w` THEN
      ASM_SIMP_TAC[PDE_PJET_PARTIAL_SPACE]];
    ALL_TAC] THEN
  (* the time-free part *)
  SUBGOAL_THEN
   `pde_subjet l (\z:real^(1,N)finite_sum.
       rdt_hv (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N)) (sndcart z)) w
    <= Chl`
  ASSUME_TAC THENL
   [EXPAND_TAC "Chl" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C0 * pde_jetn (LENGTH(l:num list))
                       (rdt_hv (metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N)))
                       (sndcart(w:real^(1,N)finite_sum))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        rdt_has_const "pde_jetn" th && rdt_has_const "pde_subjet" th)) THEN
      ASM_REWRITE_TAC[RDT_IN_UNIV_PCROSS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the inner maps: values in compact sets and sub-jets *)
  SUBGOAL_THEN
   `!j. rdt_stkc atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) j) g0 w
          IN rdt_sk K1 CJ0 /\
        rdt_stkf atlas c (g j) g0 w IN rdt_sk K1 (K1 + Bv * &(dimindex(:N)) * M1 + CJ0) /\
        pde_subjet l (rdt_stkc atlas c (g j) g0) w <= PV + Chl /\
        pde_subjet l (rdt_stkf atlas c (g j) g0) w <= PV + Bv * &(dimindex(:N)) * PD + Chl`
  ASSUME_TAC THENL
   [GEN_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[rdt_sk; IN_ELIM_THM; rdt_stkc; FSTCART_PASTECART; SNDCART_PASTECART;
                  rdt_strep; MATRIFY_VECTORIZE] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[rdt_sk; IN_ELIM_THM] THEN
      SUBGOAL_THEN
       `fstcart(rdt_stkf atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) j) g0 w) =
        rdt_strep atlas c (g j) w`
      SUBST1_TAC THENL [REWRITE_TAC[rdt_stkf; FSTCART_PASTECART]; ALL_TAC] THEN
      REWRITE_TAC[rdt_strep; MATRIFY_VECTORIZE] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(rdt_stkf atlas (c:(A->bool)#(A->real^N))
                         ((g:num->real->A->real^N^N) j) g0 w)` THEN
      REWRITE_TAC[NORM_SNDCART] THEN
      USE_THEN "bvf" (MP_TAC o SPECL
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c:(A->bool)#(A->real^N)`;
        `a:real`; `b:real`; `g0:A->real^N^N`; `(g:num->real->A->real^N^N) j`; `[]:num list`;
        `w:real^(1,N)finite_sum`]) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[pde_subjet] THEN
      MATCH_MP_TAC(REAL_ARITH
       `a <= a' /\ b <= b' /\ c <= c' ==> x <= a + b + c ==> x <= a' + b' + c'`) THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[rdt_strep] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..dimindex(:N)) (\i. M1)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `pde_pjet 1 n (rdt_strep atlas (c:(A->bool)#(A->real^N))
                                     ((g:num->real->A->real^N^N) j)) w` THEN
          CONJ_TAC THENL
           [MP_TAC(ISPECL [`1:num`; `n:num`;
                           `rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) j)`;
                           `w:real^(1,N)finite_sum`; `[1 + i:num]`] PDE_PJET_TERM) THEN
            REWRITE_TAC[iterated_partial; ALL; LENGTH; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
            ASM_SIMP_TAC[PDE_NTIME_CLAUSES; ARITH_RULE `1 <= i ==> ~(1 + i = 1)`] THEN
            DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
            ASM_SIMP_TAC[]];
          REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
        ASM_SIMP_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_subjet l (rdt_strep atlas (c:(A->bool)#(A->real^N))
                                  ((g:num->real->A->real^N^N) j)) w +
                  pde_subjet l (\z. rdt_hv (metric_local atlas c (g0:A->real^N^N)) (sndcart z)) w` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RDT_STKC_SUBJET THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_subjet l (rdt_strep atlas (c:(A->bool)#(A->real^N))
                                  ((g:num->real->A->real^N^N) j)) w +
                  Bv * sum(1..dimindex(:N))
                         (\i. pde_subjet l (partial_derivative (1 + i) (rdt_strep atlas c (g j))) w) +
                  pde_subjet l (\z. rdt_hv (metric_local atlas c (g0:A->real^N^N)) (sndcart z)) w` THEN
      CONJ_TAC THENL
       [USE_THEN "bvf" MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' /\ c <= c' ==> a + b + c <= a' + b' + c'`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..dimindex(:N)) (\i. PD)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[];
          REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]]];
    ALL_TAC] THEN
  (* the coefficient bounds *)
  SUBGOAL_THEN
   `pde_subjet l (\z. vectorize(pde_mlaa atlas (c:(A->bool)#(A->real^N))
                     ((g:num->real->A->real^N^N) k) (drop(fstcart z)) (sndcart z))) w <= QC /\
    (!i. 1 <= i /\ i <= dimindex(:N)
         ==> pde_subjet l (\z. vectorize(pde_mlbt atlas c (g k) (g0:A->real^N^N)
                                 (drop(fstcart z)) (sndcart z) i)) w <= QC) /\
    pde_subjet l (\z. vectorize(pde_mlct atlas c (g k) g0 (drop(fstcart z)) (sndcart z))) w <= QC /\
    pde_subjet l (\z. vectorize(metric_local atlas c
       (\x. pde_rdt_rhs atlas g0 (g k (drop(fstcart z))) x -
            pde_trhess atlas (g k (drop(fstcart z))) g0 (g k (drop(fstcart z))) x)
       (sndcart z))) w <= QF`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "cs" (MP_TAC o SPECL [`(g:num->real->A->real^N^N) k`; `l:num list`;
                                   `w:real^(1,N)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= pde_subjet l (rdt_stkc atlas (c:(A->bool)#(A->real^N))
                            ((g:num->real->A->real^N^N) k) (g0:A->real^N^N)) w /\
      pde_subjet l (rdt_stkc atlas c (g k) g0) w <= PV + Chl /\
      &0 <= pde_subjet l (rdt_stkf atlas c (g k) g0) w /\
      pde_subjet l (rdt_stkf atlas c (g k) g0) w <= PV + Bv * &(dimindex(:N)) * PD + Chl`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[PDE_SUBJET_POS]; ALL_TAC] THEN
    STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["QC"; "QF"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RDT_POW_BOUND_MONO THEN
      EXISTS_TAC `pde_subjet l (rdt_stkc atlas (c:(A->bool)#(A->real^N))
                                  ((g:num->real->A->real^N^N) k) (g0:A->real^N^N)) w` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC RDT_POW_BOUND_MONO THEN
      EXISTS_TAC `pde_subjet l (rdt_stkc atlas (c:(A->bool)#(A->real^N))
                                  ((g:num->real->A->real^N^N) k) (g0:A->real^N^N)) w` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC RDT_POW_BOUND_MONO THEN
      EXISTS_TAC `pde_subjet l (rdt_stkc atlas (c:(A->bool)#(A->real^N))
                                  ((g:num->real->A->real^N^N) k) (g0:A->real^N^N)) w` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RDT_POW_BOUND_MONO THEN
      EXISTS_TAC `pde_subjet l (rdt_stkf atlas (c:(A->bool)#(A->real^N))
                                  ((g:num->real->A->real^N^N) k) (g0:A->real^N^N)) w` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* smoothness of the coefficients and the time trade *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `a:real`; `b:real`; `g0:A->real^N^N`;
                 `(g:num->real->A->real^N^N) k`] RDT_ST_COEF_SMOOTH) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)
        ==> partial_derivative 1 (rdt_strep atlas c ((g:num->real->A->real^N^N) (SUC k))) z =
            pde_stop (\w. pde_mlaa atlas c (g k) (drop(fstcart w)) (sndcart w))
                     (\w i. pde_mlbt atlas c (g k) (g0:A->real^N^N) (drop(fstcart w)) (sndcart w) i)
                     (\w. pde_mlct atlas c (g k) g0 (drop(fstcart w)) (sndcart w))
                     (rdt_strep atlas c (g (SUC k))) z +
            vectorize(metric_local atlas c
              (\x. pde_rdt_rhs atlas g0 (g k (drop(fstcart z))) x -
                   pde_trhess atlas (g k (drop(fstcart z))) g0 (g k (drop(fstcart z))) x)
              (sndcart z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `(g:num->real->A->real^N^N) k`; `g0:A->real^N^N`;
                   `\t x. pde_rdt_rhs atlas (g0:A->real^N^N) ((g:num->real->A->real^N^N) k t) x -
                          pde_trhess atlas (g k t) g0 (g k t) x`;
                   `g0:A->real^N^N`; `(g:num->real->A->real^N^N) (SUC k)`;
                   `c:(A->bool)#(A->real^N)`; `z:real^(1,N)finite_sum`] RDT_ST_TRADE_ON) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> rdt_has_const "pde_rdt_step" th)) THEN
    REWRITE_TAC[pde_rdt_step];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
    `rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) (SUC k))`;
    `\w. pde_mlaa atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) k)
           (drop(fstcart w)) (sndcart w)`;
    `\w i. pde_mlbt atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) k)
             (g0:A->real^N^N) (drop(fstcart w)) (sndcart w) i`;
    `\w. pde_mlct atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) k)
           (g0:A->real^N^N) (drop(fstcart w)) (sndcart w)`;
    `\w. (vectorize:real^N^N->real^(N,N)finite_prod)
           (metric_local atlas (c:(A->bool)#(A->real^N))
              (\x. pde_rdt_rhs atlas (g0:A->real^N^N)
                     ((g:num->real->A->real^N^N) k (drop(fstcart w))) x -
                   pde_trhess atlas (g k (drop(fstcart w))) g0 (g k (drop(fstcart w))) x)
              (sndcart w))`;
    `l:num list`; `w:real^(1,N)finite_sum`; `QC:real`; `QF:real`; `PV:real`; `PD:real`;
    `PDD:real`] RDT_ST_D1_BOUND) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Uniform bounds of all space-time jets of the iterates in a chart, on      *)
(* (a,b) x K0, by induction on the number of time derivatives.               *)
(* ------------------------------------------------------------------------- *)

let RDT_ITER_ST_BOUNDS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c a b (g0:A->real^N^N)
    (g:num->real->A->real^N^N) K0.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas g0 /\
     compact K0 /\ K0 SUBSET IMAGE (SND c) (FST c) /\
     (!k. pde_tfam_from atlas a b (g k)) /\
     (!k t. a <= t /\ t < b ==> riemannian_metric atlas (g k t)) /\
     (!k. pde_rdt_step (top,atlas) a b g0 (g k) (g (SUC k))) /\ g 0 = (\t. g0) /\
     (?K1. !k t y. a <= t /\ t < b /\ y IN K0
                   ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                              (metric_local atlas c (g k t) y)) <= K1 /\
                       !v. norm v pow 2 <= K1 * (v dot (metric_local atlas c (g k t) y ** v))) /\
     (!l. ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
          ==> ?M. !k t y. a <= t /\ t < b /\ y IN K0
                          ==> norm(iterated_partial l
                                     ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                      metric_local atlas c (g k t)) y) <= M)
     ==> !l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
             ==> ?M. !k w. w IN interval(lift a,lift b) PCROSS K0
                           ==> norm(iterated_partial l (rdt_strep atlas c (g k)) w) <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "sj" o check (fun th -> rdt_has_const "iterated_partial" th)) THEN
  SUBGOAL_THEN
   `open (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)) /\
    smooth_map_on (IMAGE (SND c) (FST c))
      ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c (g0:A->real^N^N))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ASM_MESON_TAC[riemannian_metric; metric_field]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open (interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                      (rdt_strep atlas c ((g:num->real->A->real^N^N) k))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RDT_STREP_ALT] THEN MATCH_MP_TAC RDT_ST_REP_SMOOTH THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN interval(lift a,lift b) PCROSS K0
        ==> w IN interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c) /\
            a < drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN K0 /\
            sndcart w IN IMAGE (SND c) (FST c)`
  (LABEL_TAC "wf") THENL
   [REWRITE_TAC[RDT_IN_STSET] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ pde_ntime l <= n
          ==> ?M. !k w. w IN interval(lift a,lift b) PCROSS K0
                        ==> norm(iterated_partial l (rdt_strep atlas (c:(A->bool)#(A->real^N))
                                                       ((g:num->real->A->real^N^N) k)) w) <= M`
  (fun th -> MESON_TAC[th; LE_REFL]) THEN
  INDUCT_TAC THENL
   [X_GEN_TAC `l:num list` THEN REWRITE_TAC[LE] THEN STRIP_TAC THEN
    MP_TAC(SPEC `l:num list` RDT_NTIME0_MAP) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l0:num list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REMOVE_THEN "sj" (MP_TAC o SPEC `l0:num list`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real` (LABEL_TAC "m")) THEN EXISTS_TAC `M:real` THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `w:real^(1,N)finite_sum`] THEN DISCH_TAC THEN
    USE_THEN "wf" (MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`l0:num list`;
                   `rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) k)`;
                   `interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                   `fstcart(w:real^(1,N)finite_sum)`; `sndcart(w:real^(1,N)finite_sum)`]
      PDE_ST_SLICE_ITERATED) THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `(\y. rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) k)
             (pastecart (fstcart(w:real^(1,N)finite_sum)) y)) =
      (vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c (g k (drop(fstcart w)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; rdt_strep; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    USE_THEN "m" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN STRIP_TAC THEN
  ASM_CASES_TAC `pde_ntime l <= n` THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> rdt_has_const "pde_ntime" th)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_ntime l = SUC n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (* the first iterate is time-free *)
  SUBGOAL_THEN
   `?M0. !w. w IN interval(lift a,lift b) PCROSS K0
             ==> norm(iterated_partial l (rdt_strep atlas (c:(A->bool)#(A->real^N))
                                            ((g:num->real->A->real^N^N) 0)) w) <= M0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `K0:real^N->bool`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) o
                    metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N)`;
                   `LENGTH(l:num list)`] RDT_JETS_BOUNDED_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `M0:real` THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "wf" (MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `rdt_strep atlas (c:(A->bool)#(A->real^N)) (\t:real. (g0:A->real^N^N)) =
      (\w. ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c g0) (sndcart w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rdt_strep; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (LENGTH(l:num list))
                  ((vectorize:real^N^N->real^(N,N)finite_prod) o
                   metric_local atlas (c:(A->bool)#(A->real^N)) (g0:A->real^N^N))
                  (sndcart(w:real^(1,N)finite_sum))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RDT_ST_TIMEFREE THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[RDT_IN_UNIV_PCROSS];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the later iterates: trade one time derivative *)
  SUBGOAL_THEN
   `?B. !k w. w IN interval(lift a,lift b) PCROSS K0
              ==> norm(iterated_partial l (rdt_strep atlas (c:(A->bool)#(A->real^N))
                                             ((g:num->real->A->real^N^N) (SUC k))) w) <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `a:real`; `b:real`; `g0:A->real^N^N`;
                   `g:num->real->A->real^N^N`; `K0:real^N->bool`; `n:num`] RDT_ST_STEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `K1:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `r:num` THEN
      MP_TAC(ISPECL [`\k. rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) k)`;
                     `interval(lift a,lift b) PCROSS (K0:real^N->bool)`; `r:num`; `n:num`]
        RDT_PJET_UNIF) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      DISCH_THEN(LABEL_TAC "st")] THEN
    MP_TAC(ISPECL
     [`\l':num list. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l' /\
                     pde_ntime l' = n /\ LENGTH l' = LENGTH(l:num list) - 1`;
      `\w:real^(1,N)finite_sum. w IN interval(lift a,lift b) PCROSS K0`;
      `\l' k w. norm(iterated_partial l'
                  (partial_derivative 1 (rdt_strep atlas (c:(A->bool)#(A->real^N))
                                           ((g:num->real->A->real^N^N) (SUC k)))) w)`]
      RDT_FINITE_UNIF) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `pde_index_lists (LENGTH(l:num list) - 1) (:(1,N)finite_sum)` THEN
        REWRITE_TAC[PDE_INDEX_LISTS_FINITE; SUBSET; IN_ELIM_THM; pde_index_lists] THEN
        SIMP_TAC[LE_REFL];
        REPEAT STRIP_TAC THEN USE_THEN "st" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "b")) THEN EXISTS_TAC `B:real` THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `w:real^(1,N)finite_sum`] THEN DISCH_TAC THEN
    USE_THEN "wf" (MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                   `rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) (SUC k))`;
                   `l:num list`; `n:num`; `w:real^(1,N)finite_sum`] PDE_TIME_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l':num list` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "b" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `max M0 B` THEN MAP_EVERY X_GEN_TAC [`k:num`; `w:real^(1,N)finite_sum`] THEN
  DISCH_TAC THEN STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN ASM_SIMP_TAC[REAL_LE_MAX]);;

(* ------------------------------------------------------------------------- *)
(* Uniform Cauchy property of all space-time jets of the iterates on         *)
(* (a,t1] x K0 for every t1 < b, from the uniform Cauchy property of the     *)
(* space jets and the uniform bounds of all space-time jets, by induction on *)
(* the time order with a first-order Taylor bound in time:                   *)
(*   |f'(t)| <= |f(t + h) - f(t)| / h + h sup |f''|.                         *)
(* ------------------------------------------------------------------------- *)

let RDT_TIME_SPLIT_UNIF = prove
 (`!l n. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ pde_ntime l = SUC n
         ==> ?l'. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l' /\
                  pde_ntime l' = n /\ LENGTH l' = LENGTH l - 1 /\
                  !S (f:real^(1,N)finite_sum->real^P) z.
                     open S /\ smooth_map_on S f /\ z IN S
                     ==> iterated_partial l f z = iterated_partial l' (partial_derivative 1 f) z`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `APPEND (FILTER (\j. ~(j = 1)) l) (REPLICATE n 1)` THEN
  SUBGOAL_THEN `FILTER (\j. j = 1) l = REPLICATE (SUC n) 1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1:num`; `FILTER (\j:num. j = 1) l`] PDE_ALL_EQ_REPLICATE) THEN
    REWRITE_TAC[ALL_FILTER; ALL_T] THEN DISCH_THEN SUBST1_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pde_ntime]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\j:num. j = 1`; `l:num list`] PDE_FILTER_LENGTH_SPLIT) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[LENGTH_REPLICATE] THEN DISCH_TAC THEN
  REWRITE_TAC[ALL_APPEND; PDE_NTIME_APPEND; PDE_NTIME_FILTER_NOT; PDE_NTIME_REPLICATE;
              LENGTH_APPEND; LENGTH_REPLICATE; ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ALL_FILTER] THEN
    UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l` THEN
    MATCH_MP_TAC MONO_ALL THEN SIMP_TAC[];
    REWRITE_TAC[GSYM ALL_MEM; MEM_REPLICATE] THEN SIMP_TAC[PDE_HEAT_DIMINDEX_ST] THEN ARITH_TAC;
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `f:real^(1,N)finite_sum->real^P`; `1:num`]
                TEXT_ITERATED_PARTIAL_CANON) THEN
  ASM_REWRITE_TAC[PDE_HEAT_DIMINDEX_ST] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l` THEN
    REWRITE_TAC[PDE_HEAT_DIMINDEX_ST];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REPLICATE] THEN
  MATCH_MP_TAC PDE_ITERATED_PARTIAL_MOVE THEN EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; MEM_REPLICATE; PDE_HEAT_DIMINDEX_ST] THEN ARITH_TAC);;

let RDT_TAYLOR1 = prove
 (`!(f:real^1->real^K) f' f'' t h B.
     &0 < h /\
     (!r. r IN interval[t,t + lift h] ==> (f has_vector_derivative f' r) (at r)) /\
     (!r. r IN interval[t,t + lift h] ==> (f' has_vector_derivative f'' r) (at r)) /\
     (!r. r IN interval[t,t + lift h] ==> norm(f'' r) <= B)
     ==> norm(f' t) <= norm(f(t + lift h) - f t) / h + B * h`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `I1 = interval[t:real^1,t + lift h]` THEN
  SUBGOAL_THEN `(t:real^1) IN I1 /\ t + lift h IN I1 /\ convex(I1:real^1->bool) /\
                (!r. r IN I1 ==> norm(r - t) <= h)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "I1" THEN
    REWRITE_TAC[CONVEX_INTERVAL; IN_INTERVAL_1; DROP_ADD; LIFT_DROP; NORM_1; DROP_SUB] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((f'':real^1->real^K) t)` THEN
    ASM_SIMP_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN I1 ==> norm((f':real^1->real^K) r - f' t) <= B * h` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f':real^1->real^K`; `f'':real^1->real^K`; `I1:real^1->bool`; `B:real`]
      VECTOR_DIFFERENTIABLE_BOUND) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_AT_WITHIN]; ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * norm(r - t:real^1)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. (f:real^1->real^K) r - drop r % f' (t:real^1)`;
                 `\r. (f':real^1->real^K) r - f' t`; `I1:real^1->bool`; `B * h`]
    VECTOR_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t + lift h:real^1`; `t:real^1`]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((f:real^1->real^K) (t + lift h) - drop(t + lift h) % f' t) - (f t - drop t % f' (t:real^1)) =
    (f (t + lift h) - f t) - h % f' t`
  SUBST1_TAC THENL [REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `(t + h) - t:real^N = h`; NORM_LIFT] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < h ==> abs h = h`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `h * norm((f':real^1->real^K) t) <= norm((f:real^1->real^K)(t + lift h) - f t) + B * h * h`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `h * norm((f':real^1->real^K) t) = norm(h % (f':real^1->real^K) t)` SUBST1_TAC
    THENL [ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < h ==> abs h = h`]; ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH `norm(y - x:real^N) <= e ==> norm x <= norm y + e`) THEN
    UNDISCH_TAC
     `norm(((f:real^1->real^K) (t + lift h) - f t) - h % (f':real^1->real^K) t) <= (B * h) * h` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `h:real` THEN
  ASM_REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
  ASM_REAL_ARITH_TAC);;

let RDT_ST_TIME_TAYLOR = prove
 (`!S (D:real^(1,N)finite_sum->real^K) y t h B.
     open S /\ smooth_map_on S D /\ &0 < h /\
     (!s. t <= s /\ s <= t + h ==> pastecart (lift s) y IN S) /\
     (!s. t <= s /\ s <= t + h
          ==> norm(partial_derivative 1 (partial_derivative 1 D) (pastecart (lift s) y)) <= B)
     ==> norm(partial_derivative 1 D (pastecart (lift t) y)) <=
         norm(D(pastecart (lift(t + h)) y) - D(pastecart (lift t) y)) / h + B * h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. (D:real^(1,N)finite_sum->real^K) (pastecart r y)`;
                 `\r. partial_derivative 1 (D:real^(1,N)finite_sum->real^K) (pastecart r y)`;
                 `\r. partial_derivative 1 (partial_derivative 1 (D:real^(1,N)finite_sum->real^K))
                        (pastecart r y)`;
                 `lift t`; `h:real`; `B:real`] RDT_TAYLOR1) THEN
  REWRITE_TAC[GSYM LIFT_ADD] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THENL
   [MATCH_MP_TAC PDE_ST_TIME_DERIV THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC PDE_ST_TIME_DERIV THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ASM_SIMP_TAC[]]);;

let RDT_STREP_SLICE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c a b (v:real->A->real^N^N) l t y.
     smooth_manifold_atlas top atlas /\ pde_tfam_from atlas a b v /\ c IN atlas /\
     a < t /\ t < b /\ y IN IMAGE (SND c) (FST c) /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
     ==> iterated_partial (MAP (\k. 1 + k) l) (rdt_strep atlas c v) (pastecart (lift t) y) =
         iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                             metric_local atlas c (v t)) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `rdt_strep atlas (c:(A->bool)#(A->real^N)) (v:real->A->real^N^N)`;
                 `interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `lift t`; `y:real^N`] PDE_ST_SLICE_ITERATED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RDT_IN_STSET; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      ASM_MESON_TAC[PDM_CHART_OPEN_C];
      REWRITE_TAC[RDT_STREP_ALT] THEN MATCH_MP_TAC RDT_ST_REP_SMOOTH THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; rdt_strep; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]);;

let RDT_ITER_ST_CAUCHY = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c a b (g0:A->real^N^N)
    (g:num->real->A->real^N^N) K0.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas g0 /\
     compact K0 /\ K0 SUBSET IMAGE (SND c) (FST c) /\
     (!k. pde_tfam_from atlas a b (g k)) /\
     (!k t. a <= t /\ t < b ==> riemannian_metric atlas (g k t)) /\
     (!k. pde_rdt_step (top,atlas) a b g0 (g k) (g (SUC k))) /\ g 0 = (\t. g0) /\
     (?K1. !k t y. a <= t /\ t < b /\ y IN K0
                   ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                              (metric_local atlas c (g k t) y)) <= K1 /\
                       !v. norm v pow 2 <= K1 * (v dot (metric_local atlas c (g k t) y ** v))) /\
     (!l. ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
          ==> ?M. !k t y. a <= t /\ t < b /\ y IN K0
                          ==> norm(iterated_partial l
                                     ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                      metric_local atlas c (g k t)) y) <= M)
     ==> (!l e. ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ &0 < e
                ==> ?k0. !m k t y. k0 <= k /\ k <= m /\ a <= t /\ t < b /\ y IN K0
                                   ==> norm(iterated_partial l
                                              ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                               metric_local atlas c (g m t)) y -
                                            iterated_partial l
                                              ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                               metric_local atlas c (g k t)) y) <= e)
     ==> !l t1 e. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ t1 < b /\ &0 < e
                  ==> ?k0. !m k t y. k0 <= k /\ k <= m /\ a < t /\ t <= t1 /\ y IN K0
                                     ==> norm(iterated_partial l (rdt_strep atlas c (g m))
                                                (pastecart (lift t) y) -
                                              iterated_partial l (rdt_strep atlas c (g k))
                                                (pastecart (lift t) y)) <= e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> LABEL_TAC "bd" (MATCH_MP RDT_ITER_ST_BOUNDS th) THEN STRIP_ASSUME_TAC th) THEN
  DISCH_THEN(LABEL_TAC "cj") THEN
  ABBREV_TAC `U = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  SUBGOAL_THEN `open(S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. smooth_map_on S (rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) k))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RDT_STREP_ALT] THEN MAP_EVERY EXPAND_TAC ["S"; "U"] THEN
    MATCH_MP_TAC RDT_ST_REP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m k. smooth_map_on S (\z. rdt_strep atlas (c:(A->bool)#(A->real^N))
                                 ((g:num->real->A->real^N^N) m) z -
                               rdt_strep atlas c (g k) z)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n l t1 e. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ pde_ntime l <= n /\
               t1 < b /\ &0 < e
               ==> ?k0. !m k t y. k0 <= k /\ k <= m /\ a < t /\ t <= t1 /\ y IN K0
                                  ==> norm(iterated_partial l
                                             (rdt_strep atlas (c:(A->bool)#(A->real^N))
                                                ((g:num->real->A->real^N^N) m))
                                             (pastecart (lift t) y) -
                                           iterated_partial l (rdt_strep atlas c (g k))
                                             (pastecart (lift t) y)) <= e`
  (fun th -> MESON_TAC[th; LE_REFL]) THEN
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LE] THEN STRIP_TAC THEN
    MP_TAC(SPEC `l:num list` RDT_NTIME0_MAP) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l0:num list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "cj" (MP_TAC o SPECL [`l0:num list`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN EXISTS_TAC `k0:num` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `a < t /\ t < b /\ (y:real^N) IN U` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; REAL_LET_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `a:real`; `b:real`;
                   `(g:num->real->A->real^N^N) m`; `l0:num list`; `t:real`; `y:real^N`]
      RDT_STREP_SLICE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `a:real`; `b:real`;
                   `(g:num->real->A->real^N^N) k`; `l0:num list`; `t:real`; `y:real^N`]
      RDT_STREP_SLICE) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    USE_THEN "k0" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `pde_ntime l <= n` THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      rdt_has_const "pde_ntime" th && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_ntime l = SUC n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num list`; `n:num`]
    (INST_TYPE [`:(N,N)finite_prod`,`:P`] RDT_TIME_SPLIT_UNIF)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':num list` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ts"))))) THEN
  (* second time derivatives bounded *)
  USE_THEN "bd" (MP_TAC o SPEC `CONS 1 (CONS 1 (l':num list))`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:real` (LABEL_TAC "m2")) THEN
  ABBREV_TAC `B = &2 * abs M2 + &1` THEN
  SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL [EXPAND_TAC "B" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t2 = (t1 + b) / &2` THEN
  SUBGOAL_THEN `t1 < t2 /\ t2 < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < min (t2 - t1) (e / (&4 * B)) /\ min (t2 - t1) (e / (&4 * B)) <= t2 - t1 /\
                B * min (t2 - t1) (e / (&4 * B)) <= e / &4` MP_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &4`; REAL_SUB_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * e / (&4 * B)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MIN_LE; REAL_LE_REFL];
      ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_FIELD
        `&0 < B ==> B * e / (&4 * B) = e / &4`; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `h = min (t2 - t1) (e / (&4 * B))` THEN STRIP_TAC THEN
  (* the induction hypothesis at time order n on (a,t2] *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`l':num list`; `t2:real`; `e * h / &4`] o check (fun th ->
    rdt_has_const "pde_ntime" th && is_forall(concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_ARITH `&0 < &4`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN EXISTS_TAC `k0:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `k:num`; `t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. t <= s /\ s <= t + h ==> pastecart (lift s) (y:real^N) IN S /\
                                 pastecart (lift s) y IN interval(lift a,lift b) PCROSS K0 /\
                                 a < s /\ s <= t2`
  (LABEL_TAC "sm") THENL
   [GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[RDT_IN_STSET; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Dmk = \z. rdt_strep atlas (c:(A->bool)#(A->real^N))
                          ((g:num->real->A->real^N^N) m) z - rdt_strep atlas c (g k) z` THEN
  SUBGOAL_THEN `smooth_map_on S (Dmk:real^(1,N)finite_sum->real^(N,N)finite_prod)` ASSUME_TAC
  THENL [EXPAND_TAC "Dmk" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!q z. z IN S
          ==> iterated_partial q (Dmk:real^(1,N)finite_sum->real^(N,N)finite_prod) z =
              iterated_partial q (rdt_strep atlas (c:(A->bool)#(A->real^N))
                                    ((g:num->real->A->real^N^N) m)) z -
              iterated_partial q (rdt_strep atlas c (g k)) z`
  (LABEL_TAC "ds") THENL
   [X_GEN_TAC `q:num list` THEN X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    EXPAND_TAC "Dmk" THEN
    MP_TAC(ISPECL [`q:num list`; `S:real^(1,N)finite_sum->bool`;
                   `rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) m)`;
                   `rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) k)`]
      TEXT_ITERATED_PARTIAL_SUB_OPEN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `iterated_partial l (rdt_strep atlas (c:(A->bool)#(A->real^N)) ((g:num->real->A->real^N^N) m))
      (pastecart (lift t) y) -
    iterated_partial l (rdt_strep atlas c (g k)) (pastecart (lift t) y) =
    partial_derivative 1 (iterated_partial l' (Dmk:real^(1,N)finite_sum->real^(N,N)finite_prod))
      (pastecart (lift t) y)`
  SUBST1_TAC THENL
   [USE_THEN "sm" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "ds" (MP_TAC o SPECL [`l:num list`; `pastecart (lift t) (y:real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    USE_THEN "ts" (MP_TAC o SPECL [`S:real^(1,N)finite_sum->bool`;
                                   `Dmk:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                                   `pastecart (lift t) (y:real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                   `Dmk:real^(1,N)finite_sum->real^(N,N)finite_prod`; `1:num`]
      TEXT_PARTIAL_COMMUTE_ITERATED) THEN
    ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `l':num list`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l'` THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (y:real^N)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  (* the difference quotient over [t,t+h] is small *)
  SUBGOAL_THEN
   `norm(iterated_partial l' (Dmk:real^(1,N)finite_sum->real^(N,N)finite_prod)
           (pastecart (lift(t + h)) y) -
         iterated_partial l' Dmk (pastecart (lift t) y)) <= e / &2 * h`
  ASSUME_TAC THENL
   [USE_THEN "sm" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "sm" (MP_TAC o SPEC `t + h:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "ds" (fun th -> ASM_SIMP_TAC[th]) THEN
    MATCH_MP_TAC(NORM_ARITH
     `!a1 b1 a0 b0:real^N d e2.
        norm(a1 - b1) <= d /\ norm(a0 - b0) <= d /\ &2 * d = e2
        ==> norm((a1 - b1) - (a0 - b0)) <= e2`) THEN
    EXISTS_TAC `e * h / &4` THEN REPEAT CONJ_TAC THENL
     [USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                 `iterated_partial l' (Dmk:real^(1,N)finite_sum->real^(N,N)finite_prod)`;
                 `y:real^N`; `t:real`; `h:real`; `B:real`] RDT_ST_TIME_TAYLOR) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN USE_THEN "sm" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN USE_THEN "sm" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN
       `partial_derivative 1 (partial_derivative 1
          (iterated_partial l' (Dmk:real^(1,N)finite_sum->real^(N,N)finite_prod)))
          (pastecart (lift s) y) =
        iterated_partial (CONS 1 (CONS 1 l')) Dmk (pastecart (lift s) y)`
      SUBST1_TAC THENL [REWRITE_TAC[iterated_partial]; ALL_TAC] THEN
      USE_THEN "ds" (MP_TAC o SPECL [`CONS 1 (CONS 1 (l':num list))`;
                                     `pastecart (lift s) (y:real^N)`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      EXPAND_TAC "B" THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^N) <= M /\ norm(y:real^N) <= M ==> norm(x - y) <= &2 * abs M + &1`) THEN
      CONJ_TAC THEN USE_THEN "m2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= e / &2 /\ y <= e / &4 /\ &0 < e ==> n <= x + y ==> n <= e`) THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ]);;

