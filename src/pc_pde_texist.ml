(* ========================================================================= *)
(* Unit pc_pde_texist (the torus theory, second part): existence for linear  *)
(* parabolic systems with scalar principal part on the torus by the          *)
(* continuity method from the flat heat equation; the statement M4,          *)
(* PDE_TORUS_LIN_HOLDS.  Builds on pc_pde_tlin (energy estimates, PDE_FT1,   *)
(* PDE_FT2, PDE_GRONWALL_W, uniqueness) and pc_pde_heat (PDE_TORUS_HEAT).    *)
(* ========================================================================= *)

needs "src/pc_pde_tlin.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The Leibniz rule on an open set, with the jets of the second factor       *)
(* collected along the subsequences of the list of derivatives (pde_subjet). *)
(* ========================================================================= *)

let pde_subjet = define
 `(pde_subjet [] (g:real^M->real^Q) z = norm(g z)) /\
  (pde_subjet (CONS i l) g z = pde_subjet l g z + pde_subjet l (partial_derivative i g) z)`;;

let PDE_SUBJET_POS = prove
 (`!l (g:real^M->real^Q) z. &0 <= pde_subjet l g z`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[pde_subjet; NORM_POS_LE; REAL_LE_ADD]);;

let PDE_SUBJET_LEIBNIZ = prove
 (`!(bb:real^P->real^Q->real^K) M A S.
     bilinear bb /\ (!x y. norm(bb x y) <= M * norm x * norm y) /\ &0 <= M /\ open S
     ==> !l (f:real^M->real^P) (g:real^M->real^Q) z.
           smooth_map_on S f /\ smooth_map_on S g /\ z IN S /\
           ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\
           (!l' y. LENGTH l' <= LENGTH l /\ ALL (\i. 1 <= i /\ i <= dimindex(:M)) l' /\
                   y IN S
                   ==> norm(iterated_partial l' f y) <= A)
           ==> norm(iterated_partial l (\x. bb (f x) (g x)) z) <= M * A * pde_subjet l g z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[iterated_partial; pde_subjet; LENGTH] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M * norm((f:real^M->real^P) z) * norm((g:real^M->real^Q) z)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`[]:num list`; `z:real^M`]) THEN
    ASM_REWRITE_TAC[LENGTH; ALL; LE_REFL; iterated_partial];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`f:real^M->real^P`; `g:real^M->real^Q`; `z:real^M`] THEN
  REWRITE_TAC[ALL; LENGTH] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on S (\x. (bb:real^P->real^Q->real^K) ((f:real^M->real^P) x)
                                                  ((g:real^M->real^Q) x))`
  ASSUME_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_BILINEAR_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S (partial_derivative i (f:real^M->real^P)) /\
    smooth_map_on S (partial_derivative i (g:real^M->real^Q))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `iterated_partial (CONS i l)
      (\x. (bb:real^P->real^Q->real^K) ((f:real^M->real^P) x) ((g:real^M->real^Q) x)) z =
    iterated_partial l (\x. bb (partial_derivative i f x) (g x)) z +
    iterated_partial l (\x. bb (f x) (partial_derivative i g x)) z`
  SUBST1_TAC THENL
   [REWRITE_TAC[iterated_partial] THEN
    MP_TAC(ISPECL [`S:real^M->bool`;
                   `\x. (bb:real^P->real^Q->real^K) ((f:real^M->real^P) x)
                                                     ((g:real^M->real^Q) x)`;
                   `i:num`] TEXT_PARTIAL_COMMUTE_ITERATED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `iterated_partial l
                  (\x. (bb:real^P->real^Q->real^K) (partial_derivative i f x)
                                                   ((g:real^M->real^Q) x) +
                       bb ((f:real^M->real^P) x) (partial_derivative i g x)) z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `S:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
      MATCH_MP_TAC PDE_PARTIAL_BILINEAR THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `S:real^M->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`l:num list`; `S:real^M->bool`;
                     `\x. (bb:real^P->real^Q->real^K) (partial_derivative i f x)
                                                      ((g:real^M->real^Q) x)`;
                     `\x. (bb:real^P->real^Q->real^K) ((f:real^M->real^P) x)
                                                      (partial_derivative i g x)`]
                    PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_BILINEAR_OPEN THEN
        ASM_REWRITE_TAC[ETA_AX];
        DISCH_THEN(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[pde_subjet; REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a:real^K) <= x /\ norm(b) <= y ==> norm(a + b) <= x + y`) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MAP_EVERY X_GEN_TAC [`l':num list`; `y:real^M`] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `iterated_partial l' (partial_derivative i (f:real^M->real^P)) =
                  iterated_partial (APPEND l' [i]) f`
    SUBST1_TAC THENL [REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ALL_APPEND; ALL] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* Parabolic jets.  pde_ntime l counts the time derivatives (index 1) in     *)
(* a list; pde_pjet r a g z sums |D^l g z| over the lists with at most       *)
(* a time and at most r other derivatives.                                   *)
(* ========================================================================= *)

let pde_ntime = new_definition
 `pde_ntime (l:num list) = LENGTH (FILTER (\i. i = 1) l)`;;

let PDE_NTIME_CLAUSES = prove
 (`pde_ntime [] = 0 /\
   (!l. pde_ntime (CONS 1 l) = SUC (pde_ntime l)) /\
   (!i l. ~(i = 1) ==> pde_ntime (CONS i l) = pde_ntime l)`,
  SIMP_TAC[pde_ntime; FILTER; LENGTH]);;

let PDE_NTIME_LE = prove
 (`!l. pde_ntime l <= LENGTH l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pde_ntime; FILTER; LENGTH; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pde_ntime]) THEN ASM_ARITH_TAC);;

let PDE_NTIME_APPEND_SING = prove
 (`!l i. pde_ntime (APPEND l [i]) = pde_ntime l + (if i = 1 then 1 else 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_ntime; FILTER_APPEND; FILTER; LENGTH_APPEND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let pde_pjet = new_definition
 `pde_pjet r a (g:real^M->real^Q) z =
    sum {l | ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ pde_ntime l <= a /\
             LENGTH l <= r + a /\ LENGTH l - pde_ntime l <= r}
        (\l. norm(iterated_partial l g z))`;;

let PDE_PJET_FINITE = prove
 (`!r a. FINITE {l | ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ pde_ntime l <= a /\
                     LENGTH l <= r + a /\ LENGTH l - pde_ntime l <= r}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `pde_index_lists (r + a) (:M)` THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  REWRITE_TAC[pde_index_lists; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let PDE_PJET_POS = prove
 (`!r a (g:real^M->real^Q) z. &0 <= pde_pjet r a g z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_pjet] THEN MATCH_MP_TAC SUM_POS_LE THEN
  REWRITE_TAC[PDE_PJET_FINITE; NORM_POS_LE]);;

let PDE_PJET_MONO = prove
 (`!r a r' a' (g:real^M->real^Q) z.
     r <= r' /\ a <= a' ==> pde_pjet r a g z <= pde_pjet r' a' g z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_pjet] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  REWRITE_TAC[PDE_PJET_FINITE; NORM_POS_LE; SUBSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PDE_PJET_TERM = prove
 (`!r a (g:real^M->real^Q) z l.
     ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ pde_ntime l <= a /\
     LENGTH l - pde_ntime l <= r
     ==> norm(iterated_partial l g z) <= pde_pjet r a g z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_pjet] THEN
  MP_TAC(ISPECL [`\l. norm(iterated_partial l (g:real^M->real^Q) z)`;
                 `sum {l | ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ pde_ntime l <= a /\
                           LENGTH l <= r + a /\ LENGTH l - pde_ntime l <= r}
                      (\l. norm(iterated_partial l (g:real^M->real^Q) z))`;
                 `{l | ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ pde_ntime l <= a /\
                       LENGTH l <= r + a /\ LENGTH l - pde_ntime l <= r}`] SUM_POS_BOUND) THEN
  REWRITE_TAC[PDE_PJET_FINITE; NORM_POS_LE; REAL_LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* A partial derivative raises the time or the space count by one. *)

let PDE_PJET_PARTIAL = prove
 (`!r a (g:real^M->real^Q) z i.
     1 <= i /\ i <= dimindex(:M)
     ==> pde_pjet r a (partial_derivative i g) z <=
         pde_pjet (if i = 1 then r else SUC r) (if i = 1 then SUC a else a) g z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_pjet] THEN
  SUBGOAL_THEN `!l. iterated_partial l (partial_derivative i (g:real^M->real^Q)) =
                    iterated_partial (APPEND l [i]) g`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\l:num list. APPEND l [i:num]`;
                 `\l:num list. norm(iterated_partial l (g:real^M->real^Q) z)`;
                 `{l | ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ pde_ntime l <= a /\
                       LENGTH l <= r + a /\ LENGTH l - pde_ntime l <= r}`] SUM_IMAGE) THEN
  ANTS_TAC THENL [SIMP_TAC[PDE_APPEND_SING_INJ]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[PDE_PJET_FINITE; NORM_POS_LE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; PDE_NTIME_APPEND_SING; ALL_APPEND; ALL;
              LENGTH_APPEND; LENGTH] THEN
  X_GEN_TAC `l:num list` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `l:num list` PDE_NTIME_LE) THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* The subsequence jets are controlled by the parabolic jets. *)

let PDE_SUBJET_PJET = prove
 (`!l (g:real^M->real^Q) z.
     ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
     ==> pde_subjet l g z <=
         &2 pow (LENGTH l) * pde_pjet (LENGTH l - pde_ntime l) (pde_ntime l) g z`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[pde_subjet; LENGTH; PDE_NTIME_CLAUSES; real_pow; REAL_MUL_LID; SUB_0] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`0`; `0`; `g:real^M->real^Q`; `z:real^M`; `[]:num list`] PDE_PJET_TERM) THEN
    REWRITE_TAC[ALL; LENGTH; PDE_NTIME_CLAUSES; LE_REFL; SUB_0; iterated_partial];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`g:real^M->real^Q`; `z:real^M`] THEN
  REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`g:real^M->real^Q`; `z:real^M`] th) THEN
                          MP_TAC(SPECL [`partial_derivative i (g:real^M->real^Q)`;
                                        `z:real^M`] th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `l:num list` PDE_NTIME_LE) THEN DISCH_TAC THEN
  REWRITE_TAC[pde_subjet; LENGTH; real_pow] THEN
  ABBREV_TAC `n = LENGTH(l:num list)` THEN ABBREV_TAC `nt = pde_ntime l` THEN
  ASM_CASES_TAC `i = 1` THENL
   [SUBGOAL_THEN `pde_ntime (CONS i l) = SUC nt` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[PDE_NTIME_CLAUSES]; ALL_TAC] THEN
    SUBGOAL_THEN `SUC n - SUC nt = n - nt` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `pde_pjet (n - nt) nt (partial_derivative i (g:real^M->real^Q)) z <=
                  pde_pjet (n - nt) (SUC nt) g z` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`n - nt:num`; `nt:num`; `g:real^M->real^Q`; `z:real^M`; `i:num`]
                    PDE_PJET_PARTIAL) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`n - nt:num`; `nt:num`; `n - nt:num`; `SUC nt`; `g:real^M->real^Q`;
                   `z:real^M`] PDE_PJET_MONO) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `nt <= SUC nt`] THEN DISCH_TAC;
    SUBGOAL_THEN `pde_ntime (CONS i l) = nt` SUBST1_TAC THENL
     [ASM_SIMP_TAC[PDE_NTIME_CLAUSES]; ALL_TAC] THEN
    SUBGOAL_THEN `SUC n - nt = SUC(n - nt)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `pde_pjet (n - nt) nt (partial_derivative i (g:real^M->real^Q)) z <=
                  pde_pjet (SUC(n - nt)) nt g z` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`n - nt:num`; `nt:num`; `g:real^M->real^Q`; `z:real^M`; `i:num`]
                    PDE_PJET_PARTIAL) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`n - nt:num`; `nt:num`; `SUC(n - nt)`; `nt:num`; `g:real^M->real^Q`;
                   `z:real^M`] PDE_PJET_MONO) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `m <= SUC m`] THEN DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s1 s2 p1 p2 q c. s1 <= c * p1 /\ s2 <= c * p2 /\ c * p1 <= c * q /\ c * p2 <= c * q
                      ==> s1 + s2 <= (&2 * c) * q`) THEN
  MAP_EVERY EXISTS_TAC [`pde_pjet (n - nt) nt (g:real^M->real^Q) z`;
                        `pde_pjet (n - nt) nt (partial_derivative i (g:real^M->real^Q)) z`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  (MATCH_MP_TAC REAL_LE_LMUL THEN
   CONJ_TAC THENL [SIMP_TAC[REAL_POW_LE; REAL_POS]; FIRST_ASSUM ACCEPT_TAC]));;

(* ========================================================================= *)
(* The operator in space-time form (pde_stop: the space indices of           *)
(* real^(1,N) are 1 + i), bounded space-time coefficient data on an open set *)
(* (pde_stbnd), and the bound of D^l (pde_stop V) by the parabolic jet of    *)
(* V with two more space derivatives.                                        *)
(* ========================================================================= *)

let pde_stop = new_definition
 `pde_stop (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K)
           (c:real^(1,N)finite_sum->real^K^K) (V:real^(1,N)finite_sum->real^K) z =
    vsum(1..dimindex(:N))
      (\i. vsum(1..dimindex(:N))
             (\j. a z$i$j % partial_derivative (1 + i) (partial_derivative (1 + j) V) z)) +
    vsum(1..dimindex(:N)) (\i. b z i ** partial_derivative (1 + i) V z) +
    c z ** V z`;;

let pde_stbnd = new_definition
 `pde_stbnd S p A (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K)
            (c:real^(1,N)finite_sum->real^K^K) <=>
    &0 <= A /\
    smooth_map_on S (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (a z)) /\
    (!i. smooth_map_on S (\z. (vectorize:real^K^K->real^(K,K)finite_prod) (b z i))) /\
    smooth_map_on S (\z. (vectorize:real^K^K->real^(K,K)finite_prod) (c z)) /\
    (!l z. LENGTH l <= p /\ ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ z IN S
           ==> norm(iterated_partial l
                      (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (a z)) z) <= A /\
               (!i. 1 <= i /\ i <= dimindex(:N)
                    ==> norm(iterated_partial l
                              (\z. (vectorize:real^K^K->real^(K,K)finite_prod) (b z i)) z)
                        <= A) /\
               norm(iterated_partial l
                      (\z. (vectorize:real^K^K->real^(K,K)finite_prod) (c z)) z) <= A)`;;

(* Entries of matrix fields on an open set. *)

let PDE_ENTRY_ITERATED_OPEN = prove
 (`!S (A:real^M->real^Q^Q) l i j x.
     open S /\ smooth_map_on S (\x. (vectorize:real^Q^Q->real^(Q,Q)finite_prod) (A x)) /\
     x IN S
     ==> iterated_partial l (\x. lift(A x$i$j)) x =
         lift((matrify(iterated_partial l
                 (\x. (vectorize:real^Q^Q->real^(Q,Q)finite_prod) (A x)) x):real^Q^Q)$i$j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `\v:real^(Q,Q)finite_prod. lift((matrify v:real^Q^Q)$i$j)`;
                 `\x. (vectorize:real^Q^Q->real^(Q,Q)finite_prod) ((A:real^M->real^Q^Q) x)`;
                 `S:real^M->bool`; `x:real^M`] PDE_ITERATED_PARTIAL_LINEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY; MATRIFY_VECTORIZE]);;

let PDE_STBND_SMOOTH = prove
 (`!S p A (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c i j.
     open S /\ pde_stbnd S p A a b c
     ==> smooth_map_on S (\z. lift(a z$i$j)) /\
         smooth_map_on S (\z. (vectorize:real^K^K->real^(K,K)finite_prod) (b z i)) /\
         smooth_map_on S (\z. (vectorize:real^K^K->real^(K,K)finite_prod) (c z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_stbnd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((a:real^(1,N)finite_sum->real^N^N) z)`;
                 `\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$i$j)`]
                SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY; o_DEF; MATRIFY_VECTORIZE]);;

let PDE_STBND_AJET = prove
 (`!S p A (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c i j
    l z.
     open S /\ pde_stbnd S p A a b c /\ LENGTH l <= p /\
     ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ z IN S
     ==> norm(iterated_partial l (\z. lift(a z$i$j)) z) <= A`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_stbnd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `z:real^(1,N)finite_sum`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `a:real^(1,N)finite_sum->real^N^N`;
                 `l:num list`; `i:num`; `j:num`; `z:real^(1,N)finite_sum`]
                PDE_ENTRY_ITERATED_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(iterated_partial l
                (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                       ((a:real^(1,N)finite_sum->real^N^N) z)) z)` THEN
  ASM_REWRITE_TAC[PDE_MATRIFY_ENTRY_LE]);;

let PDE_STBND_BJET = prove
 (`!S p A (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c i l z.
     pde_stbnd S p A a b c /\ LENGTH l <= p /\
     ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ z IN S /\
     1 <= i /\ i <= dimindex(:N)
     ==> norm(iterated_partial l
                (\z. (vectorize:real^K^K->real^(K,K)finite_prod) (b z i)) z) <= A`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_stbnd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `z:real^(1,N)finite_sum`]) THEN
  ASM_SIMP_TAC[]);;

let PDE_STBND_CJET = prove
 (`!S p A (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c l z.
     pde_stbnd S p A a b c /\ LENGTH l <= p /\
     ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ z IN S
     ==> norm(iterated_partial l
                (\z. (vectorize:real^K^K->real^(K,K)finite_prod) (c z)) z) <= A`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_stbnd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `z:real^(1,N)finite_sum`]) THEN
  ASM_SIMP_TAC[]);;

(* The pieces of pde_stop, and D^l distributed over them. *)

let PDE_STOP_PIECES_SMOOTH = prove
 (`!S p A (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
    (V:real^(1,N)finite_sum->real^K) i j.
     open S /\ pde_stbnd S p A a b c /\ smooth_map_on S V
     ==> smooth_map_on S
           (\z. a z$i$j % partial_derivative (1 + i) (partial_derivative (1 + j) V) z) /\
         smooth_map_on S (\z. b z i ** partial_derivative (1 + i) V z) /\
         smooth_map_on S (\z. c z ** V z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `p:num`; `A:real`;
                 `a:real^(1,N)finite_sum->real^N^N`; `b:real^(1,N)finite_sum->num->real^K^K`;
                 `c:real^(1,N)finite_sum->real^K^K`; `i:num`; `j:num`] PDE_STBND_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                   `\z. lift((a:real^(1,N)finite_sum->real^N^N) z$i$j)`;
                   `partial_derivative (1 + i) (partial_derivative (1 + j)
                      (V:real^(1,N)finite_sum->real^K))`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    ASM_SIMP_TAC[LIFT_DROP; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                   `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `\z. (vectorize:real^K^K->real^(K,K)finite_prod)
                          ((b:real^(1,N)finite_sum->num->real^K^K) z i)`;
                   `partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K)`]
                  SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_SIMP_TAC[LRG_BILINEAR_MATRIFY_MUL; MATRIFY_VECTORIZE; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                   `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `\z. (vectorize:real^K^K->real^(K,K)finite_prod)
                          ((c:real^(1,N)finite_sum->real^K^K) z)`;
                   `V:real^(1,N)finite_sum->real^K`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_SIMP_TAC[LRG_BILINEAR_MATRIFY_MUL; MATRIFY_VECTORIZE; ETA_AX]]);;

let PDE_STOP_SMOOTH = prove
 (`!S p A (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
    (V:real^(1,N)finite_sum->real^K).
     open S /\ pde_stbnd S p A a b c /\ smooth_map_on S V
     ==> smooth_map_on S (pde_stop a b c V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `p:num`; `A:real`;
                 `a:real^(1,N)finite_sum->real^N^N`; `b:real^(1,N)finite_sum->num->real^K^K`;
                 `c:real^(1,N)finite_sum->real^K^K`; `V:real^(1,N)finite_sum->real^K`]
                PDE_STOP_PIECES_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `pde_stop (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
             (V:real^(1,N)finite_sum->real^K) =
    (\z. vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
                  (\j. a z$i$j % partial_derivative (1 + i) (partial_derivative (1 + j) V) z)) +
         (vsum(1..dimindex(:N)) (\i. b z i ** partial_derivative (1 + i) V z) +
          c z ** V z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_stop]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG]]);;

let PDE_STOP_ITERATED = prove
 (`!S p A (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
    (V:real^(1,N)finite_sum->real^K) l z.
     open S /\ pde_stbnd S p A a b c /\ smooth_map_on S V /\ z IN S
     ==> iterated_partial l (pde_stop a b c V) z =
         vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
              (\j. iterated_partial l
                     (\z. a z$i$j % partial_derivative (1 + i) (partial_derivative (1 + j) V) z)
                     z)) +
         vsum(1..dimindex(:N))
           (\i. iterated_partial l (\z. b z i ** partial_derivative (1 + i) V z) z) +
         iterated_partial l (\z. c z ** V z) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `p:num`; `A:real`;
                 `a:real^(1,N)finite_sum->real^N^N`; `b:real^(1,N)finite_sum->num->real^K^K`;
                 `c:real^(1,N)finite_sum->real^K^K`; `V:real^(1,N)finite_sum->real^K`]
                PDE_STOP_PIECES_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `pde_stop (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
             (V:real^(1,N)finite_sum->real^K) =
    (\z. vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
                  (\j. a z$i$j % partial_derivative (1 + i) (partial_derivative (1 + j) V) z)) +
         (vsum(1..dimindex(:N)) (\i. b z i ** partial_derivative (1 + i) V z) +
          c z ** V z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; pde_stop]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. smooth_map_on S
          (\z. vsum(1..dimindex(:N))
                 (\j. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
                      partial_derivative (1 + i)
                        (partial_derivative (1 + j) (V:real^(1,N)finite_sum->real^K)) z))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S
      (\z. vsum(1..dimindex(:N))
             (\i. vsum(1..dimindex(:N))
                    (\j. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
                         partial_derivative (1 + i)
                           (partial_derivative (1 + j) (V:real^(1,N)finite_sum->real^K)) z))) /\
    smooth_map_on S
      (\z. vsum(1..dimindex(:N))
             (\i. (b:real^(1,N)finite_sum->num->real^K^K) z i **
                  partial_derivative (1 + i) V z)) /\
    smooth_map_on S (\z. (c:real^(1,N)finite_sum->real^K^K) z ** V z)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`l:num list`; `S:real^(1,N)finite_sum->bool`;
    `\z. vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
                  (\j. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
                       partial_derivative (1 + i)
                         (partial_derivative (1 + j) (V:real^(1,N)finite_sum->real^K)) z))`;
    `\z. vsum(1..dimindex(:N))
           (\i. (b:real^(1,N)finite_sum->num->real^K^K) z i **
                partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K) z) +
         (c:real^(1,N)finite_sum->real^K^K) z ** V z`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`l:num list`; `S:real^(1,N)finite_sum->bool`;
    `\z. vsum(1..dimindex(:N))
           (\i. (b:real^(1,N)finite_sum->num->real^K^K) z i **
                partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K) z)`;
    `\z. (c:real^(1,N)finite_sum->real^K^K) z ** (V:real^(1,N)finite_sum->real^K) z`]
   PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`l:num list`; `S:real^(1,N)finite_sum->bool`;
    `\i z. (b:real^(1,N)finite_sum->num->real^K^K) z i **
           partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K) z`;
    `1..dimindex(:N)`] PDE_HEAT_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`l:num list`; `S:real^(1,N)finite_sum->bool`;
    `\i z. vsum(1..dimindex(:N))
             (\j. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
                  partial_derivative (1 + i)
                    (partial_derivative (1 + j) (V:real^(1,N)finite_sum->real^K)) z)`;
    `1..dimindex(:N)`] PDE_HEAT_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  MP_TAC(ISPECL
   [`l:num list`; `S:real^(1,N)finite_sum->bool`;
    `\j z. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
           partial_derivative (1 + i)
             (partial_derivative (1 + j) (V:real^(1,N)finite_sum->real^K)) z`;
    `1..dimindex(:N)`] PDE_HEAT_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[]);;

let PDE_PJET_PARTIAL_SPACE = prove
 (`!r a (g:real^(1,N)finite_sum->real^Q) z i.
     1 <= i /\ i <= dimindex(:N)
     ==> pde_pjet r a (partial_derivative (1 + i) g) z <= pde_pjet (SUC r) a g z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:num`; `a:num`; `g:real^(1,N)finite_sum->real^Q`; `z:real^(1,N)finite_sum`;
                 `1 + i`] PDE_PJET_PARTIAL) THEN
  REWRITE_TAC[PDE_HEAT_DIMINDEX_ST] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(1 + i = 1)`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* The bound of D^l (pde_stop V) by the parabolic jet of V. *)

let PDE_STOP_ITERATED_BOUND = prove
 (`!S p A (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
    (V:real^(1,N)finite_sum->real^K) l z.
     open S /\ pde_stbnd S p A a b c /\ smooth_map_on S V /\ z IN S /\
     LENGTH l <= p /\ ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
     ==> norm(iterated_partial l (pde_stop a b c V) z) <=
         &(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * A * &2 pow (LENGTH l) *
         pde_pjet ((LENGTH l - pde_ntime l) + 2) (pde_ntime l) V z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL [ASM_MESON_TAC[pde_stbnd]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `p:num`; `A:real`;
                 `a:real^(1,N)finite_sum->real^N^N`; `b:real^(1,N)finite_sum->num->real^K^K`;
                 `c:real^(1,N)finite_sum->real^K^K`; `V:real^(1,N)finite_sum->real^K`;
                 `l:num list`; `z:real^(1,N)finite_sum`] PDE_STOP_ITERATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `nx = LENGTH(l:num list) - pde_ntime l` THEN
  ABBREV_TAC `q = A * &2 pow (LENGTH(l:num list)) *
                  pde_pjet (nx + 2) (pde_ntime l) (V:real^(1,N)finite_sum->real^K) z` THEN
  SUBGOAL_THEN
   `!g:real^(1,N)finite_sum->real^K.
      smooth_map_on S g /\
      pde_pjet nx (pde_ntime l) g (z:real^(1,N)finite_sum) <=
      pde_pjet (nx + 2) (pde_ntime l) (V:real^(1,N)finite_sum->real^K) z
      ==> A * pde_subjet l g z <= q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow (LENGTH(l:num list)) *
                pde_pjet nx (pde_ntime l) (g:real^(1,N)finite_sum->real^K) z` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "nx" THEN MATCH_MP_TAC PDE_SUBJET_PJET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> norm(iterated_partial l
                (\z. (a:real^(1,N)finite_sum->real^N^N) z$i$j %
                     partial_derivative (1 + i)
                       (partial_derivative (1 + j) (V:real^(1,N)finite_sum->real^K)) z) z) <= q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\(x:real^1) (y:real^K). drop x % y`; `&1`; `A:real`;
                   `S:real^(1,N)finite_sum->bool`] PDE_SUBJET_LEIBNIZ) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; NORM_MUL; GSYM NORM_1; REAL_MUL_LID; REAL_LE_REFL;
                REAL_POS] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`l:num list`; `\z. lift((a:real^(1,N)finite_sum->real^N^N) z$i$j)`;
      `partial_derivative (1 + i) (partial_derivative (1 + j) (V:real^(1,N)finite_sum->real^K))`;
      `z:real^(1,N)finite_sum`]) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `p:num`; `A:real`;
                     `a:real^(1,N)finite_sum->real^N^N`; `b:real^(1,N)finite_sum->num->real^K^K`;
                     `c:real^(1,N)finite_sum->real^K^K`; `i:num`; `j:num`] PDE_STBND_SMOOTH) THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN DISCH_TAC THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_STBND_AJET THEN
      MAP_EVERY EXISTS_TAC [`S:real^(1,N)finite_sum->bool`; `p:num`;
                            `b:real^(1,N)finite_sum->num->real^K^K`;
                            `c:real^(1,N)finite_sum->real^K^K`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_pjet (SUC nx) (pde_ntime l)
                  (partial_derivative (1 + j) (V:real^(1,N)finite_sum->real^K)) z` THEN
    ASM_SIMP_TAC[PDE_PJET_PARTIAL_SPACE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_pjet (SUC(SUC nx)) (pde_ntime l) (V:real^(1,N)finite_sum->real^K) z` THEN
    ASM_SIMP_TAC[PDE_PJET_PARTIAL_SPACE] THEN
    MATCH_MP_TAC PDE_PJET_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> norm(iterated_partial l
              (\z. (b:real^(1,N)finite_sum->num->real^K^K) z i **
                   partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K) z) z) <= q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `&1`; `A:real`; `S:real^(1,N)finite_sum->bool`] PDE_SUBJET_LEIBNIZ) THEN
    REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; REAL_MUL_LID; PDE_MATRIFY_MUL_NORM; REAL_POS] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`l:num list`;
      `\z. (vectorize:real^K^K->real^(K,K)finite_prod)
             ((b:real^(1,N)finite_sum->num->real^K^K) z i)`;
      `partial_derivative (1 + i) (V:real^(1,N)finite_sum->real^K)`;
      `z:real^(1,N)finite_sum`]) THEN
    REWRITE_TAC[MATRIFY_VECTORIZE] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `p:num`; `A:real`;
                     `a:real^(1,N)finite_sum->real^N^N`; `b:real^(1,N)finite_sum->num->real^K^K`;
                     `c:real^(1,N)finite_sum->real^K^K`; `i:num`; `i:num`] PDE_STBND_SMOOTH) THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN DISCH_TAC THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_STBND_BJET THEN
      MAP_EVERY EXISTS_TAC [`S:real^(1,N)finite_sum->bool`; `p:num`;
                            `a:real^(1,N)finite_sum->real^N^N`;
                            `c:real^(1,N)finite_sum->real^K^K`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_pjet (SUC nx) (pde_ntime l) (V:real^(1,N)finite_sum->real^K) z` THEN
    ASM_SIMP_TAC[PDE_PJET_PARTIAL_SPACE] THEN
    MATCH_MP_TAC PDE_PJET_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(iterated_partial l
      (\z. (c:real^(1,N)finite_sum->real^K^K) z ** (V:real^(1,N)finite_sum->real^K) z) z) <= q`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `&1`; `A:real`; `S:real^(1,N)finite_sum->bool`] PDE_SUBJET_LEIBNIZ) THEN
    REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; REAL_MUL_LID; PDE_MATRIFY_MUL_NORM; REAL_POS] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`l:num list`;
      `\z. (vectorize:real^K^K->real^(K,K)finite_prod)
             ((c:real^(1,N)finite_sum->real^K^K) z)`;
      `V:real^(1,N)finite_sum->real^K`; `z:real^(1,N)finite_sum`]) THEN
    REWRITE_TAC[MATRIFY_VECTORIZE] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `p:num`; `A:real`;
                     `a:real^(1,N)finite_sum->real^N^N`; `b:real^(1,N)finite_sum->num->real^K^K`;
                     `c:real^(1,N)finite_sum->real^K^K`; `1`; `1`] PDE_STBND_SMOOTH) THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_STBND_CJET THEN
      MAP_EVERY EXISTS_TAC [`S:real^(1,N)finite_sum->bool`; `p:num`;
                            `a:real^(1,N)finite_sum->real^N^N`;
                            `b:real^(1,N)finite_sum->num->real^K^K`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_PJET_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(dimindex(:N) * dimindex(:N)) * q + &(dimindex(:N)) * q + q` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(a1:real^K) <= x /\ norm(b1) <= y /\ norm(c1) <= z
      ==> norm(a1 + (b1 + c1)) <= x + y + z`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. q:real))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..dimindex(:N)) (\i. q:real)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]];
    EXPAND_TAC "q" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Trading a time derivative for the equation.  For V with                   *)
(* partial_1 V = pde_stop V + pde_stop2 W on an open set, the parabolic jet  *)
(* with SUC n time derivatives is bounded by those with n time derivatives   *)
(* and two more space derivatives (PDE_PJET_TIME_STEP).                      *)
(* ========================================================================= *)

let PDE_ALL_EQ_REPLICATE = prove
 (`!(k:num) l. ALL (\j. j = k) l ==> l = REPLICATE (LENGTH l) k`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; LENGTH; REPLICATE] THEN
  STRIP_TAC THEN REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[]);;

let PDE_NTIME_APPEND = prove
 (`!l1 l2. pde_ntime (APPEND l1 l2) = pde_ntime l1 + pde_ntime l2`,
  REWRITE_TAC[pde_ntime; FILTER_APPEND; LENGTH_APPEND]);;

let PDE_NTIME_REPLICATE = prove
 (`!n. pde_ntime (REPLICATE n 1) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; PDE_NTIME_CLAUSES]);;

let PDE_NTIME_FILTER_NOT = prove
 (`!l. pde_ntime (FILTER (\j. ~(j = 1)) l) = 0`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; PDE_NTIME_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[PDE_NTIME_CLAUSES]);;

let PDE_FILTER_LENGTH_SPLIT = prove
 (`!P (l:A list). LENGTH (FILTER P l) + LENGTH (FILTER (\x. ~P x) l) = LENGTH l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; LENGTH] THEN
  ASM_CASES_TAC `(P:A->bool) h` THEN ASM_REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC);;

let PDE_ITERATED_PARTIAL_MOVE = prove
 (`!S (f:real^M->real^P) l1 l2 i z.
     open S /\ smooth_map_on S f /\ z IN S /\
     ALL (\k. 1 <= k /\ k <= dimindex(:M)) l2 /\ 1 <= i /\ i <= dimindex(:M)
     ==> iterated_partial (APPEND l1 (CONS i l2)) f z =
         iterated_partial (APPEND l1 l2) (partial_derivative i f) z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
  MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `S:real^M->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^M->bool`; `f:real^M->real^P`; `i:num`]
                TEXT_PARTIAL_COMMUTE_ITERATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `l2:num list`) THEN ASM_REWRITE_TAC[]);;

(* A list with SUC n time derivatives is, up to order, a list with n time   *)
(* derivatives followed by one time derivative applied first.               *)

let PDE_TIME_SPLIT = prove
 (`!S (f:real^(1,N)finite_sum->real^P) l n z.
     open S /\ smooth_map_on S f /\ z IN S /\
     ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ pde_ntime l = SUC n
     ==> ?l'. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l' /\
              pde_ntime l' = n /\ LENGTH l' - pde_ntime l' = LENGTH l - pde_ntime l /\
              LENGTH l' = LENGTH l - 1 /\
              iterated_partial l f z = iterated_partial l' (partial_derivative 1 f) z`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `APPEND (FILTER (\j. ~(j = 1)) l) (REPLICATE n 1)` THEN
  SUBGOAL_THEN `FILTER (\j. j = 1) l = REPLICATE (SUC n) 1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `FILTER (\j. j = 1) l`] PDE_ALL_EQ_REPLICATE) THEN
    REWRITE_TAC[ALL_FILTER; ALL_T] THEN DISCH_THEN SUBST1_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pde_ntime]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\j:num. j = 1`; `l:num list`] PDE_FILTER_LENGTH_SPLIT) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[LENGTH_REPLICATE] THEN DISCH_TAC THEN
  REWRITE_TAC[ALL_APPEND; PDE_NTIME_APPEND; PDE_NTIME_FILTER_NOT; PDE_NTIME_REPLICATE;
              LENGTH_APPEND; LENGTH_REPLICATE; ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ALL_FILTER] THEN UNDISCH_TAC
     `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l` THEN
    MATCH_MP_TAC MONO_ALL THEN SIMP_TAC[];
    REWRITE_TAC[GSYM ALL_MEM; MEM_REPLICATE] THEN
    SIMP_TAC[PDE_HEAT_DIMINDEX_ST] THEN ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `f:real^(1,N)finite_sum->real^P`; `1`]
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

let PDE_PJET_TIME_STEP = prove
 (`!S p A (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
    a2 b2 c2 (V:real^(1,N)finite_sum->real^K) W r n z.
     open S /\ pde_stbnd S p A a b c /\ pde_stbnd S p A a2 b2 c2 /\
     smooth_map_on S V /\ smooth_map_on S W /\
     (!z. z IN S
          ==> partial_derivative 1 V z = pde_stop a b c V z + pde_stop a2 b2 c2 W z) /\
     r + n <= p /\ z IN S
     ==> pde_pjet r (SUC n) V z <=
         pde_pjet r n V z +
         &(CARD(pde_index_lists (r + SUC n) (:(1,N)finite_sum))) *
         (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * A * &2 pow (r + n) *
          (pde_pjet (r + 2) n V z + pde_pjet (r + 2) n W z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL [ASM_MESON_TAC[pde_stbnd]; ALL_TAC] THEN
  ABBREV_TAC `L1 = {l | ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                        pde_ntime l <= SUC n /\ LENGTH l <= r + SUC n /\
                        LENGTH l - pde_ntime l <= r}` THEN
  ABBREV_TAC `L0 = {l | ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                        pde_ntime l <= n /\ LENGTH l <= r + n /\
                        LENGTH l - pde_ntime l <= r}` THEN
  SUBGOAL_THEN
   `pde_pjet r (SUC n) (V:real^(1,N)finite_sum->real^K) z =
    sum L1 (\l. norm(iterated_partial l V z)) /\
    pde_pjet r n V z = sum L0 (\l. norm(iterated_partial l V z))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["L0"; "L1"] THEN REWRITE_TAC[pde_pjet]; ALL_TAC] THEN
  SUBGOAL_THEN `L0 SUBSET (L1:num list->bool) /\ FINITE L1 /\
                L1 SUBSET pde_index_lists (r + SUC n) (:(1,N)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L0"; "L1"] THEN
    REWRITE_TAC[PDE_PJET_FINITE; SUBSET; IN_ELIM_THM; pde_index_lists] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Q = &(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * A * &2 pow (r + n) *
                  (pde_pjet (r + 2) n (V:real^(1,N)finite_sum->real^K) z +
                   pde_pjet (r + 2) n (W:real^(1,N)finite_sum->real^K) z)` THEN
  SUBGOAL_THEN
   `!l. l IN L1 DIFF L0 ==> norm(iterated_partial l (V:real^(1,N)finite_sum->real^K) z) <= Q`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num list` THEN MAP_EVERY EXPAND_TAC ["L0"; "L1"] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `pde_ntime l = SUC n` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `V:real^(1,N)finite_sum->real^K`;
                   `l:num list`; `n:num`; `z:real^(1,N)finite_sum`] PDE_TIME_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l':num list` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `iterated_partial l' (partial_derivative 1 (V:real^(1,N)finite_sum->real^K)) z =
      iterated_partial l' (pde_stop (a:real^(1,N)finite_sum->real^N^N)
                             (b:real^(1,N)finite_sum->num->real^K^K) c V) z +
      iterated_partial l' (pde_stop (a2:real^(1,N)finite_sum->real^N^N)
                             (b2:real^(1,N)finite_sum->num->real^K^K) c2
                             (W:real^(1,N)finite_sum->real^K)) z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `iterated_partial l'
                    (\z. pde_stop (a:real^(1,N)finite_sum->real^N^N)
                           (b:real^(1,N)finite_sum->num->real^K^K) c
                           (V:real^(1,N)finite_sum->real^K) z +
                         pde_stop a2 b2 c2 (W:real^(1,N)finite_sum->real^K) z) z` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
        EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[];
        MP_TAC(ISPECL [`l':num list`; `S:real^(1,N)finite_sum->bool`;
                       `pde_stop (a:real^(1,N)finite_sum->real^N^N)
                          (b:real^(1,N)finite_sum->num->real^K^K) c
                          (V:real^(1,N)finite_sum->real^K)`;
                       `pde_stop (a2:real^(1,N)finite_sum->real^N^N)
                          (b2:real^(1,N)finite_sum->num->real^K^K) c2
                          (W:real^(1,N)finite_sum->real^K)`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC PDE_STOP_SMOOTH THEN
          MAP_EVERY EXISTS_TAC [`p:num`; `A:real`] THEN ASM_REWRITE_TAC[];
          DISCH_THEN(MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[ETA_AX]]];
      ALL_TAC] THEN
    EXPAND_TAC "Q" THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC(NORM_ARITH `norm(x:real^K) <= a /\ norm(y) <= b ==> norm(x + y) <= a + b`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * A *
                  &2 pow (LENGTH(l':num list)) *
                  pde_pjet ((LENGTH l' - pde_ntime l') + 2) (pde_ntime l')
                    (V:real^(1,N)finite_sum->real^K) z`;
      EXISTS_TAC `&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * A *
                  &2 pow (LENGTH(l':num list)) *
                  pde_pjet ((LENGTH l' - pde_ntime l') + 2) (pde_ntime l')
                    (W:real^(1,N)finite_sum->real^K) z`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC PDE_STOP_ITERATED_BOUND THEN
       EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN EXISTS_TAC `p:num` THEN
       ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
       ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[PDE_PJET_POS] THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC PDE_PJET_MONO THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC PDE_PJET_MONO THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\l. norm(iterated_partial l (V:real^(1,N)finite_sum->real^K) z)`;
                 `L1:num list->bool`; `L0:num list->bool`] SUM_DIFF) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`L1 DIFF L0:num list->bool`;
                 `\l. norm(iterated_partial l (V:real^(1,N)finite_sum->real^K) z)`; `Q:real`]
                SUM_BOUND) THEN
  ASM_SIMP_TAC[FINITE_DIFF] THEN
  SUBGOAL_THEN `&(CARD(L1 DIFF L0:num list->bool)) <=
                &(CARD(pde_index_lists (r + SUC n) (:(1,N)finite_sum)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    MAP_EVERY UNDISCH_TAC [`L1 SUBSET pde_index_lists (r + SUC n) (:(1,N)finite_sum)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_ADD; PDE_PJET_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&(CARD(L1 DIFF L0:num list->bool))`;
                 `&(CARD(pde_index_lists (r + SUC n) (:(1,N)finite_sum)))`; `Q:real`]
                REAL_LE_RMUL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* For a sequence V_k with                                                   *)
(* partial_1 V_(k+1) = pde_stop V_(k+1) + pde_stop2 V_k, every parabolic jet *)
(* of V_k is bounded by the spatial jets of V_k, ..., V_(k-n).               *)
(* ========================================================================= *)

let PDE_SUM_SHIFT_LE = prove
 (`!(g:num->real) n.
     (!j. &0 <= g j)
     ==> sum(0..n) (\j. g(j + 1)) <= sum(0..SUC n) g /\
         sum(0..n) g <= sum(0..SUC n) g`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`1`; `g:num->real`; `0`; `n:num`] SUM_OFFSET) THEN
    REWRITE_TAC[ADD_CLAUSES; ADD1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`g:num->real`; `0`; `n + 1`] SUM_CLAUSES_LEFT) THEN
    REWRITE_TAC[LE_0] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ADD_CLAUSES] THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN REAL_ARITH_TAC]);;

let PDE_PJET_SEQ_BOUND = prove
 (`!S (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
    a2 b2 c2 (V:num->real^(1,N)finite_sum->real^K).
     open S /\
     (!p. ?A. pde_stbnd S p A a b c /\ pde_stbnd S p A a2 b2 c2) /\
     (!k. smooth_map_on S (V k)) /\
     (!k z. z IN S
            ==> partial_derivative 1 (V(SUC k)) z =
                pde_stop a b c (V(SUC k)) z + pde_stop a2 b2 c2 (V k) z)
     ==> !n r. ?C. &0 <= C /\
                   !k z. n <= k /\ z IN S
                         ==> pde_pjet r n (V k) z <=
                             C * sum(0..n) (\j. pde_pjet (r + 2 * n) 0 (V(k - j)) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [GEN_TAC THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_POS; SUM_SING_NUMSEG; SUB_0; MULT_CLAUSES; ADD_CLAUSES; REAL_MUL_LID;
                REAL_LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `r:num` THEN
  FIRST_ASSUM(X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC o SPEC `r:num`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `C2:real` STRIP_ASSUME_TAC o SPEC `r + 2`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `A:real` STRIP_ASSUME_TAC o SPEC `r + n:num`) THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL [ASM_MESON_TAC[pde_stbnd]; ALL_TAC] THEN
  ABBREV_TAC `Ct = &(CARD(pde_index_lists (r + SUC n) (:(1,N)finite_sum))) *
                   (&(dimindex(:N) * dimindex(:N) + dimindex(:N) + 1) * A * &2 pow (r + n))` THEN
  SUBGOAL_THEN `&0 <= Ct` ASSUME_TAC THENL
   [EXPAND_TAC "Ct" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  EXISTS_TAC `C1 + &2 * Ct * C2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `z:real^(1,N)finite_sum`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?k0. k = SUC k0` (X_CHOOSE_THEN `k0:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `k - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `r + n:num`; `A:real`;
                 `a:real^(1,N)finite_sum->real^N^N`; `b:real^(1,N)finite_sum->num->real^K^K`;
                 `c:real^(1,N)finite_sum->real^K^K`;
                 `a2:real^(1,N)finite_sum->real^N^N`; `b2:real^(1,N)finite_sum->num->real^K^K`;
                 `c2:real^(1,N)finite_sum->real^K^K`;
                 `(V:num->real^(1,N)finite_sum->real^K) (SUC k0)`;
                 `(V:num->real^(1,N)finite_sum->real^K) k0`;
                 `r:num`; `n:num`; `z:real^(1,N)finite_sum`] PDE_PJET_TIME_STEP) THEN
  ASM_SIMP_TAC[LE_REFL] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `pde_pjet r n ((V:num->real^(1,N)finite_sum->real^K) (SUC k0)) z <=
    C1 * sum(0..n) (\j. pde_pjet (r + 2 * n) 0 (V(SUC k0 - j)) z) /\
    pde_pjet (r + 2) n (V (SUC k0)) z <=
    C2 * sum(0..n) (\j. pde_pjet ((r + 2) + 2 * n) 0 (V(SUC k0 - j)) z) /\
    pde_pjet (r + 2) n (V k0) z <=
    C2 * sum(0..n) (\j. pde_pjet ((r + 2) + 2 * n) 0 (V(k0 - j)) z)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `g = \j. pde_pjet (r + 2 * SUC n) 0
                        ((V:num->real^(1,N)finite_sum->real^K) (SUC k0 - j)) z` THEN
  SUBGOAL_THEN `!j. &0 <= (g:num->real) j` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[PDE_PJET_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:num->real`; `n:num`] PDE_SUM_SHIFT_LE) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(0..n) (\j. pde_pjet (r + 2 * n) 0
                    ((V:num->real^(1,N)finite_sum->real^K) (SUC k0 - j)) z) <= sum(0..SUC n) g /\
    sum(0..n) (\j. pde_pjet ((r + 2) + 2 * n) 0 (V (SUC k0 - j)) z) <= sum(0..SUC n) g /\
    sum(0..n) (\j. pde_pjet ((r + 2) + 2 * n) 0 (V (k0 - j)) z) <= sum(0..SUC n) g`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `sum(0..n) (g:num->real)`;
      EXISTS_TAC `sum(0..n) (g:num->real)`;
      EXISTS_TAC `sum(0..n) (\j. (g:num->real) (j + 1))`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN
    STRIP_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THENL
     [MATCH_MP_TAC PDE_PJET_MONO THEN ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `(r + 2) + 2 * n = r + 2 * SUC n`; REAL_LE_REFL];
      REWRITE_TAC[ARITH_RULE `(r + 2) + 2 * n = r + 2 * SUC n`;
                  ARITH_RULE `SUC k0 - (j + 1) = k0 - j`; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C1:real`;
                 `sum(0..n) (\j. pde_pjet (r + 2 * n) 0
                    ((V:num->real^(1,N)finite_sum->real^K) (SUC k0 - j)) z)`;
                 `sum(0..SUC n) (g:num->real)`] REAL_LE_LMUL) THEN
  MP_TAC(ISPECL [`C2:real`;
                 `sum(0..n) (\j. pde_pjet ((r + 2) + 2 * n) 0
                    ((V:num->real^(1,N)finite_sum->real^K) (SUC k0 - j)) z)`;
                 `sum(0..SUC n) (g:num->real)`] REAL_LE_LMUL) THEN
  MP_TAC(ISPECL [`C2:real`;
                 `sum(0..n) (\j. pde_pjet ((r + 2) + 2 * n) 0
                    ((V:num->real^(1,N)finite_sum->real^K) (k0 - j)) z)`;
                 `sum(0..SUC n) (g:num->real)`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `Ct * (pde_pjet (r + 2) n ((V:num->real^(1,N)finite_sum->real^K) (SUC k0)) z +
          pde_pjet (r + 2) n (V k0) z) <=
    Ct * (&2 * C2 * sum(0..SUC n) (g:num->real))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "Ct" THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    let c = concl th in not (is_forall c) && not (is_eq c) &&
            can (find_term ((=) `pde_pjet:num->num->(real^(1,N)finite_sum->real^K)->real^(1,N)finite_sum->real`)) c)) THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Spatial partials of maps smooth up to t = 0, continuity of the gradient   *)
(* energies, and bounded (not necessarily elliptic) time-dependent           *)
(* coefficients (pde_tbnd) with uniform fixed-time bounds.                   *)
(* ========================================================================= *)

let PDE_UPTO_PARTIAL = prove
 (`!b (W:real->real^N->real^K) i.
     pde_upto (&0) b (:real^N) W /\ 1 <= i /\ i <= dimindex(:N)
     ==> pde_upto (&0) b (:real^N) (\t x. partial_derivative i (W t) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FW:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e:real`;
                        `partial_derivative (1 + i) (FW:real^(1,N)finite_sum->real^K)`] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(W:real->real^N->real^K) t = (\y. FW(pastecart (lift t) y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDE_ST_SLICE_PARTIAL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `interval(lift(&0 - e),lift b) PCROSS (:real^N)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_INTERVAL_1;
               LIFT_DROP; IN_UNIV] THEN
  MAP_EVERY UNDISCH_TAC [`&0 < e`; `&0 <= t`; `t < b`] THEN REAL_ARITH_TAC);;

let PDE_UPTO_GM_CONT = prove
 (`!b (W:real->real^N->real^K) T1 m.
     pde_upto (&0) b (:real^N) W /\ T1 < b
     ==> (\r. sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i (W r))))
         real_continuous_on real_interval[&0,T1]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real`; `\t x. partial_derivative i ((W:real->real^N->real^K) t) x`;
                 `T1:real`; `m:num`] PDE_UPTO_HS2_CONT) THEN
  ASM_SIMP_TAC[PDE_UPTO_PARTIAL; ETA_AX]);;

(* Bounded time-dependent coefficients. *)

let pde_tbnd = new_definition
 `pde_tbnd (tmax:real) (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K)
           (cc:real->real^N->real^K^K) <=>
    pde_upto (&0) tmax (:real^N) (\t y. (vectorize:real^N^N->real^(N,N)finite_prod) (aa t y)) /\
    (!i. pde_upto (&0) tmax (:real^N)
           (\t y. (vectorize:real^K^K->real^(K,K)finite_prod) (bb t y i))) /\
    pde_upto (&0) tmax (:real^N) (\t y. (vectorize:real^K^K->real^(K,K)finite_prod) (cc t y)) /\
    (!t. pde_zper (aa t) /\ pde_zper (cc t) /\ !i. pde_zper (\y. bb t y i))`;;

let PDE_TCOEFF_TBND = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc.
     pde_tcoeff tmax lam aa bb cc ==> pde_tbnd tmax aa bb cc`,
  REWRITE_TAC[pde_tcoeff; pde_tbnd] THEN MESON_TAC[]);;

let PDE_TBND_FBND = prove
 (`!tmax (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc T1 p.
     pde_tbnd tmax aa bb cc /\ &0 <= T1 /\ T1 < tmax
     ==> ?M. !t. &0 <= t /\ t <= T1 ==> pde_fbnd p M (aa t) (bb t) (cc t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tbnd] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`;
                 `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((aa:real->real^N->real^N^N) t y)`;
                 `T1:real`; `p:num`] PDE_UPTO_JET_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PDE_ZPER_COMPOSE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `MA:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tmax:real`;
                 `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                          ((cc:real->real^N->real^K^K) t y)`;
                 `T1:real`; `p:num`] PDE_UPTO_JET_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PDE_ZPER_COMPOSE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `MC:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. ?A. &0 <= A /\
            !t l y. &0 <= t /\ t <= T1 /\ LENGTH l <= p /\
                    ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
                    ==> norm(iterated_partial l
                          (\y. (vectorize:real^K^K->real^(K,K)finite_prod)
                                 ((bb:real->real^N->num->real^K^K) t y i)) y) <= A`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`tmax:real`;
                   `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((bb:real->real^N->num->real^K^K) t y i)`;
                   `T1:real`; `p:num`] PDE_UPTO_JET_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN
    MP_TAC(ISPECL [`\y. (bb:real->real^N->num->real^K^K) t y i`;
                   `vectorize:real^K^K->real^(K,K)finite_prod`] PDE_ZPER_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `MB:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `MA + sum(1..dimindex(:N)) MB + MC` THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sum(1..dimindex(:N)) MB` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t < tmax` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`t <= T1`; `T1 < tmax`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[pde_fbnd] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= MA`; `&0 <= MC`; `&0 <= sum(1..dimindex(:N)) MB`] THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL [`tmax:real`;
                   `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                            ((aa:real->real^N->real^N^N) t y)`; `t:real`]
                  PDE_UPTO_SLICE_SMOOTH) THEN
    ASM_REWRITE_TAC[ETA_AX];
    GEN_TAC THEN
    MP_TAC(ISPECL [`tmax:real`;
                   `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((bb:real->real^N->num->real^K^K) t y i)`; `t:real`]
                  PDE_UPTO_SLICE_SMOOTH) THEN
    ASM_REWRITE_TAC[ETA_AX];
    MP_TAC(ISPECL [`tmax:real`;
                   `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((cc:real->real^N->real^K^K) t y)`; `t:real`]
                  PDE_UPTO_SLICE_SMOOTH) THEN
    ASM_REWRITE_TAC[ETA_AX];
    MAP_EVERY X_GEN_TAC [`l:num list`; `x:real^N`] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `MA:real` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `l:num list`; `x:real^N`] o
          check (fun th -> can (find_term ((=) `MA:real`)) (concl th) && is_forall (concl th))) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[ETA_AX];
        MAP_EVERY UNDISCH_TAC [`&0 <= MC`; `&0 <= sum(1..dimindex(:N)) MB`] THEN
        REAL_ARITH_TAC];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(MB:num->real) i` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        MP_TAC(ISPECL [`MB:num->real`; `sum(1..dimindex(:N)) MB`; `1..dimindex(:N)`]
                      SUM_POS_BOUND) THEN
        ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL; IN_NUMSEG] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`&0 <= MA`; `&0 <= MC`] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `MC:real` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `l:num list`; `x:real^N`] o
          check (fun th -> can (find_term ((=) `MC:real`)) (concl th) && is_forall (concl th))) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[ETA_AX];
        MAP_EVERY UNDISCH_TAC [`&0 <= MA`; `&0 <= sum(1..dimindex(:N)) MB`] THEN
        REAL_ARITH_TAC]]]);;

(* ========================================================================= *)
(* The energy inequality for L1 u + L2 w (PDE_ENERGY_FT12) when              *)
(* 8 a2^2 <= lam1^2, the weighted quantity pde_zn, and the contraction of    *)
(* the iteration (PDE_CONTRACT).                                             *)
(* ========================================================================= *)

let PDE_ENERGY_FT12 = prove
 (`!m M1 M2 lam1 a2.
     &0 < lam1 /\ &8 * a2 pow 2 <= lam1 pow 2
     ==> ?K. &0 <= K /\
             !(A1:real^N->real^N^N) (B1:real^N->num->real^K^K) C1 A2 B2 C2
              (u:real^N->real^K) w.
               pde_fcoeff (m + 1) M1 lam1 A1 B1 C1 /\ pde_fbnd (m + 1) M2 A2 B2 C2 /\
               (!x. norm((vectorize:real^N^N->real^(N,N)finite_prod) (A2 x)) <= a2) /\
               smooth_map_on (:real^N) u /\ pde_zper u /\
               smooth_map_on (:real^N) w /\ pde_zper w
               ==> sum (pde_index_lists m (:N))
                       (\l. pde_cint (\x. &2 * (iterated_partial l u x dot
                              iterated_partial l
                                (\x. pde_lop0 A1 B1 C1 u x + pde_lop0 A2 B2 C2 w x) x)))
                   <= --lam1 * sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i u)) +
                      (lam1 / &2) *
                      sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i w)) +
                      K * (pde_hs2 m u + pde_hs2 m w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `M1:real`; `lam1:real`] PDE_FT1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K1:real`) THEN
  MP_TAC(ISPECL [`m:num`; `M2:real`; `a2:real`; `lam1 / &2`; `lam1 / &4`] PDE_FT2) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `K2:real`) THEN
  EXISTS_TAC `abs K1 + abs K2` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N)
      (pde_lop0 (A1:real^N->real^N^N) (B1:real^N->num->real^K^K) C1 (u:real^N->real^K)) /\
    smooth_map_on (:real^N)
      (pde_lop0 (A2:real^N->real^N^N) (B2:real^N->num->real^K^K) C2 (w:real^N->real^K))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_LOP0_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`m + 1`] THENL
     [EXISTS_TAC `M1:real` THEN ASM_MESON_TAC[pde_fcoeff];
      EXISTS_TAC `M2:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (pde_index_lists m (:N))
      (\l. pde_cint (\x. &2 * (iterated_partial l (u:real^N->real^K) x dot
                    iterated_partial l (pde_lop0 (A1:real^N->real^N^N)
                                         (B1:real^N->num->real^K^K) C1 u) x))) +
    sum (pde_index_lists m (:N))
      (\l. pde_cint (\x. &2 * (iterated_partial l u x dot
                    iterated_partial l (pde_lop0 (A2:real^N->real^N^N)
                                         (B2:real^N->num->real^K^K) C2 (w:real^N->real^K))
                      x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN SIMP_TAC[GSYM SUM_ADD; PDE_INDEX_LISTS_FINITE] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!x. iterated_partial l
            (\x. pde_lop0 (A1:real^N->real^N^N) (B1:real^N->num->real^K^K) C1
                          (u:real^N->real^K) x +
                 pde_lop0 (A2:real^N->real^N^N) (B2:real^N->num->real^K^K) C2
                          (w:real^N->real^K) x) x =
          iterated_partial l (pde_lop0 A1 B1 C1 u) x +
          iterated_partial l (pde_lop0 A2 B2 C2 w) x`
    (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPECL [`l:num list`; `(:real^N)`;
                     `pde_lop0 (A1:real^N->real^N^N) (B1:real^N->num->real^K^K) C1
                               (u:real^N->real^K)`;
                     `pde_lop0 (A2:real^N->real^N^N) (B2:real^N->num->real^K^K) C2
                               (w:real^N->real^K)`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[DOT_RADD; REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC PDE_CINT_ADD THEN CONJ_TAC THEN PDE_TL_SMOOTH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`A2:real^N->real^N^N`; `B2:real^N->num->real^K^K`;
                                `C2:real^N->real^K^K`; `u:real^N->real^K`;
                                `w:real^N->real^K`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`A1:real^N->real^N^N`; `B1:real^N->num->real^K^K`;
                                `C1:real^N->real^K^K`; `u:real^N->real^K`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= pde_hs2 m (u:real^N->real^K) /\ &0 <= pde_hs2 m (w:real^N->real^K) /\
    &0 <= sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i w))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PDE_HS2_POS] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    ASM_SIMP_TAC[PDE_HS2_POS; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `a2 pow 2 / (lam1 / &2) + lam1 / &4 <= lam1 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= lam1 / &4 ==> x + lam1 / &4 <= lam1 / &2`) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `&8 * a2 pow 2 <= lam1 pow 2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a2 pow 2 / (lam1 / &2) + lam1 / &4`; `lam1 / &2`;
                 `sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i (w:real^N->real^K)))`]
                REAL_LE_RMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K1:real`; `abs K1`; `pde_hs2 m (u:real^N->real^K)`] REAL_LE_RMUL) THEN
  MP_TAC(ISPECL [`K2:real`; `abs K2`; `pde_hs2 m (u:real^N->real^K) + pde_hs2 m (w:real^N->real^K)`]
                REAL_LE_RMUL) THEN
  ASM_SIMP_TAC[REAL_ABS_LE; REAL_LE_ADD] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= abs K1 * pde_hs2 m (w:real^N->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let pde_zn = new_definition
 `pde_zn m lam mu K T2 (v:real->real^N->real^K) =
    real_integral (real_interval[&0,T2])
      (\r. exp(--(mu * r)) *
           (lam * sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i (v r))) +
            (mu - K) * pde_hs2 m (v r)))`;;

(* Continuity and positivity of the weighted energy integrands. *)

let PDE_ZN_INTEGRAND_CONT = prove
 (`!b (v:real->real^N->real^K) T2 m lam mu K.
     pde_upto (&0) b (:real^N) v /\ T2 < b
     ==> (\r. exp(--(mu * r)) *
              (lam * sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i (v r))) +
               (mu - K) * pde_hs2 m (v r))) real_continuous_on real_interval[&0,T2]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
  REWRITE_TAC[PDE_EXP_WEIGHT_CONT] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THENL
   [MATCH_MP_TAC PDE_UPTO_GM_CONT; MATCH_MP_TAC PDE_UPTO_HS2_CONT] THEN
  EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[]);;

let PDE_GM_POS = prove
 (`!m (v:real^N->real^K).
     smooth_map_on (:real^N) v
     ==> &0 <= sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i v))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  ASM_SIMP_TAC[PDE_HS2_POS; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV]);;

(* The contraction of one step of the iteration, in the weighted norm.      *)

let PDE_CONTRACT = prove
 (`!tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 a2 t1 T2 m.
     pde_tcoeff tmax lam1 aa1 bb1 cc1 /\ pde_tbnd tmax aa2 bb2 cc2 /\
     (!t x. &0 <= t /\ t < tmax
            ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) (aa2 t x)) <= a2) /\
     &8 * a2 pow 2 <= lam1 pow 2 /\ &0 < T2 /\ T2 < t1 /\ t1 <= tmax
     ==> ?K mu. &0 <= K /\ &3 * K < mu /\
                !u w. pde_tsol t1 aa1 bb1 cc1 (\t x. pde_lop aa2 bb2 cc2 w t x)
                               (\x. vec 0) u /\
                      pde_upto (&0) t1 (:real^N) w /\
                      (!t. &0 <= t /\ t < t1 ==> pde_zper (w t))
                      ==> pde_zn m lam1 mu K T2 u <= pde_zn m lam1 mu K T2 w / &2 /\
                          !t. &0 <= t /\ t <= T2
                              ==> exp(--(mu * t)) * pde_hs2 m (u t) <=
                                  pde_zn m lam1 mu K T2 w / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < lam1` ASSUME_TAC THENL [ASM_MESON_TAC[pde_tcoeff]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= T2 /\ T2 < tmax` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < T2`; `T2 < t1`; `t1 <= tmax`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                 `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                 `T2:real`; `m + 1`] PDE_TCOEFF_FCOEFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M1:real`) THEN
  MP_TAC(ISPECL [`tmax:real`; `aa2:real->real^N->real^N^N`;
                 `bb2:real->real^N->num->real^K^K`; `cc2:real->real^N->real^K^K`;
                 `T2:real`; `m + 1`] PDE_TBND_FBND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M2:real`) THEN
  MP_TAC(ISPECL [`m:num`; `M1:real`; `M2:real`; `lam1:real`; `a2:real`] PDE_ENERGY_FT12) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K:real` THEN EXISTS_TAC `&3 * K + &1` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real->real^N->real^K`; `w:real->real^N->real^K`] THEN STRIP_TAC THEN
  ABBREV_TAC `mu = &3 * K + &1` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_tsol]) THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t < t1
        ==> smooth_map_on (:real^N) ((u:real->real^N->real^K) t) /\
            smooth_map_on (:real^N) ((w:real->real^N->real^K) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_UPTO_SLICE_SMOOTH THEN
    EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\r. pde_hs2 m ((u:real->real^N->real^K) r)`;
    `\r. sum (pde_index_lists m (:N))
           (\l. pde_cint (\x. &2 * (iterated_partial l ((u:real->real^N->real^K) r) x dot
                  iterated_partial l
                    (\x. pde_lop0 ((aa1:real->real^N->real^N^N) r)
                                  ((bb1:real->real^N->num->real^K^K) r)
                                  ((cc1:real->real^N->real^K^K) r) (u r) x +
                         pde_lop0 ((aa2:real->real^N->real^N^N) r)
                                  ((bb2:real->real^N->num->real^K^K) r)
                                  ((cc2:real->real^N->real^K^K) r)
                                  ((w:real->real^N->real^K) r) x) x)))`;
    `\r. lam1 * sum(1..dimindex(:N))
                  (\i. pde_hs2 m (partial_derivative i ((u:real->real^N->real^K) r)))`;
    `\r. (lam1 / &2) * sum(1..dimindex(:N))
                         (\i. pde_hs2 m (partial_derivative i ((w:real->real^N->real^K) r))) +
         K * pde_hs2 m (w r)`;
    `K:real`; `mu:real`; `T2:real`] PDE_GRONWALL_W) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(u:real->real^N->real^K) (&0) = (\y. vec 0)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; REWRITE_TAC[PDE_HS2_ZERO]];
      MATCH_MP_TAC PDE_UPTO_HS2_CONT THEN EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN MATCH_MP_TAC PDE_UPTO_GM_CONT THEN
      EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THENL
       [MATCH_MP_TAC PDE_UPTO_GM_CONT; MATCH_MP_TAC PDE_UPTO_HS2_CONT] THEN
      EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= t /\ t <= T2 /\ t < t1 /\ t < tmax` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`&0 < t`; `t < T2`; `T2 < t1`; `t1 <= tmax`] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`t1:real`; `aa1:real->real^N->real^N^N`;
                       `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                       `\t x. pde_lop (aa2:real->real^N->real^N^N)
                                      (bb2:real->real^N->num->real^K^K)
                                      (cc2:real->real^N->real^K^K)
                                      (w:real->real^N->real^K) t x`;
                       `\x:real^N. vec 0:real^K`; `u:real->real^N->real^K`; `m:num`; `t:real`]
                      PDE_TSOL_ENERGY_DERIV) THEN
        ASM_REWRITE_TAC[PDE_LOP_LOP0] THEN
        MAP_EVERY UNDISCH_TAC [`&0 < t`] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`(aa1:real->real^N->real^N^N) t`; `(bb1:real->real^N->num->real^K^K) t`;
        `(cc1:real->real^N->real^K^K) t`; `(aa2:real->real^N->real^N^N) t`;
        `(bb2:real->real^N->num->real^K^K) t`; `(cc2:real->real^N->real^K^K) t`;
        `(u:real->real^N->real^K) t`; `(w:real->real^N->real^K) t`] o
        check (fun th -> is_forall (concl th) &&
                         can (find_term (fun tm -> try fst(dest_const tm) = "pde_fbnd"
                                                   with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "gw") THEN
  SUBGOAL_THEN
   `!r. r IN real_interval[&0,T2]
        ==> &0 <= sum(1..dimindex(:N))
                    (\i. pde_hs2 m (partial_derivative i ((u:real->real^N->real^K) r))) /\
            &0 <= pde_hs2 m (u r) /\
            &0 <= sum(1..dimindex(:N))
                    (\i. pde_hs2 m (partial_derivative i ((w:real->real^N->real^K) r))) /\
            &0 <= pde_hs2 m (w r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= r /\ r < t1` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 <= r`; `r <= T2`; `T2 < t1`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o
      check (fun th -> is_forall (concl th) &&
               can (find_term (fun tm -> try fst(dest_const tm) = "smooth_map_on"
                                         with Failure _ -> false)) (concl th) &&
               not (can (find_term (fun tm -> try fst(dest_const tm) = "pde_fbnd"
                                              with Failure _ -> false)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[PDE_GM_POS; PDE_HS2_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,T2])
      (\r. exp(--(mu * r)) *
           ((lam1 / &2) * sum(1..dimindex(:N))
                            (\i. pde_hs2 m (partial_derivative i ((w:real->real^N->real^K) r))) +
            K * pde_hs2 m (w r))) <=
    pde_zn m lam1 mu K T2 w / &2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t1:real`; `w:real->real^N->real^K`; `T2:real`; `m:num`; `lam1:real`;
                   `mu:real`; `K:real`] PDE_ZN_INTEGRAND_CONT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `pde_zn m lam1 mu K T2 (w:real->real^N->real^K) / &2 =
      real_integral (real_interval[&0,T2])
        (\r. inv(&2) *
             (exp(--(mu * r)) *
              (lam1 * sum(1..dimindex(:N)) (\i. pde_hs2 m (partial_derivative i (w r))) +
               (mu - K) * pde_hs2 m (w r))))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; REAL_INTEGRABLE_CONTINUOUS; pde_zn] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; REAL_CONTINUOUS_ON_LMUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
      REWRITE_TAC[PDE_EXP_WEIGHT_CONT] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THENL
       [MATCH_MP_TAC PDE_UPTO_GM_CONT; MATCH_MP_TAC PDE_UPTO_HS2_CONT] THEN
      EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `ew = exp(--(mu * r))` THEN
    ABBREV_TAC `gw = sum(1..dimindex(:N))
                       (\i. pde_hs2 m (partial_derivative i ((w:real->real^N->real^K) r)))` THEN
    ABBREV_TAC `hw = pde_hs2 m ((w:real->real^N->real^K) r)` THEN
    SUBGOAL_THEN `&0 <= ew` ASSUME_TAC THENL
     [EXPAND_TAC "ew" THEN REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (inv(&2) * (mu - K) - K) * hw` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "mu" THEN
      UNDISCH_TAC `&0 <= K` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= ew * ((inv(&2) * (mu - K) - K) * hw)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REMOVE_THEN "gw" (MP_TAC o SPEC `T2:real`) THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM pde_zn] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `T2:real`) THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    STRIP_TAC THEN MP_TAC(SPEC `--(mu * T2)` REAL_EXP_POS_LE) THEN
    SUBGOAL_THEN `&0 <= exp(--(mu * T2)) * pde_hs2 m ((u:real->real^N->real^K) T2)`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REMOVE_THEN "gw" (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  SUBGOAL_THEN
   `&0 <= real_integral (real_interval[&0,t])
            (\r. exp(--(mu * r)) *
                 (lam1 * sum(1..dimindex(:N))
                           (\i. pde_hs2 m (partial_derivative i ((u:real->real^N->real^K) r))) +
                  (mu - K) * pde_hs2 m (u r)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_POS THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[&0,T2]` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PDE_ZN_INTEGRAND_CONT THEN EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "mu" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,t])
      (\r. exp(--(mu * r)) *
           ((lam1 / &2) * sum(1..dimindex(:N))
                            (\i. pde_hs2 m (partial_derivative i ((w:real->real^N->real^K) r))) +
            K * pde_hs2 m (w r))) <=
    real_integral (real_interval[&0,T2])
      (\r. exp(--(mu * r)) *
           ((lam1 / &2) * sum(1..dimindex(:N))
                            (\i. pde_hs2 m (partial_derivative i (w r))) +
            K * pde_hs2 m (w r)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
    SUBGOAL_THEN
     `(\r. exp(--(mu * r)) *
           ((lam1 / &2) * sum(1..dimindex(:N))
                            (\i. pde_hs2 m (partial_derivative i ((w:real->real^N->real^K) r))) +
            K * pde_hs2 m (w r))) real_continuous_on real_interval[&0,T2]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN REWRITE_TAC[PDE_EXP_WEIGHT_CONT] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THENL
       [MATCH_MP_TAC PDE_UPTO_GM_CONT; MATCH_MP_TAC PDE_UPTO_HS2_CONT] THEN
      EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[&0,T2]` THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Maps smooth up to t = 0 are closed under linear maps, bilinear maps, sums *)
(* and the operator; the operator preserves periodicity.                     *)
(* ========================================================================= *)

let PDE_UPTO_LINEAR = prove
 (`!b (L:real^P->real^Q) (f:real->real^N->real^P).
     linear L /\ pde_upto (&0) b (:real^N) f
     ==> pde_upto (&0) b (:real^N) (\t x. L(f t x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^P` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `(L:real^P->real^Q) o (FF:real^(1,N)finite_sum->real^P)`] THEN
  ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]);;

let PDE_UPTO_BILINEAR = prove
 (`!b (bb:real^P->real^Q->real^K) (f:real->real^N->real^P) g.
     bilinear bb /\ pde_upto (&0) b (:real^N) f /\ pde_upto (&0) b (:real^N) g
     ==> pde_upto (&0) b (:real^N) (\t x. bb (f t x) (g t x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `F1:real^(1,N)finite_sum->real^P`
      STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `e2:real` (X_CHOOSE_THEN `F2:real^(1,N)finite_sum->real^Q`
      STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `min e1 e2` THEN
  EXISTS_TAC `\z. (bb:real^P->real^Q->real^K) ((F1:real^(1,N)finite_sum->real^P) z)
                                              ((F2:real^(1,N)finite_sum->real^Q) z)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN];
    MATCH_MP_TAC SMOOTH_MAP_ON_BILINEAR_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `interval(lift(&0 - e1),lift b) PCROSS (:real^N)`;
      EXISTS_TAC `interval(lift(&0 - e2),lift b) PCROSS (:real^N)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN BINOP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let PDE_UPTO_ADD = prove
 (`!b (u:real->real^N->real^K) v.
     pde_upto (&0) b (:real^N) u /\ pde_upto (&0) b (:real^N) v
     ==> pde_upto (&0) b (:real^N) (\t x. u t x + v t x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&0`; `b:real`; `u:real->real^N->real^K`; `v:real->real^N->real^K`;
                 `&1`; `&1`] PDE_UPTO_LIN2) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID]);;

let PDE_UPTO_VSUM = prove
 (`!b (f:num->real->real^N->real^K) n.
     (!i. 1 <= i /\ i <= n ==> pde_upto (&0) b (:real^N) (f i))
     ==> pde_upto (&0) b (:real^N) (\t x. vsum(1..n) (\i. f i t x))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_EQ; PDE_UPTO_CONST]; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  MATCH_MP_TAC PDE_UPTO_ADD THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* The operator applied to a map smooth up to t = 0. *)

let PDE_UPTO_LOP = prove
 (`!tmax b (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc w.
     pde_tbnd tmax aa bb cc /\ pde_upto (&0) b (:real^N) w /\ b <= tmax
     ==> pde_upto (&0) b (:real^N) (\t x. pde_lop aa bb cc w t x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tbnd] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pde_upto (&0) b (:real^N)
      (\t y. (vectorize:real^N^N->real^(N,N)finite_prod) ((aa:real->real^N->real^N^N) t y)) /\
    (!i. pde_upto (&0) b (:real^N)
           (\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                    ((bb:real->real^N->num->real^K^K) t y i))) /\
    pde_upto (&0) b (:real^N)
      (\t y. (vectorize:real^K^K->real^(K,K)finite_prod) ((cc:real->real^N->real^K^K) t y))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY GEN_TAC THEN MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN
    EXISTS_TAC `tmax:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pde_lop] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> pde_upto (&0) b (:real^N) (\t x. partial_derivative i ((w:real->real^N->real^K) t) x)`
  ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_UPTO_PARTIAL THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> pde_upto (&0) b (:real^N)
                (\t x. partial_derivative i
                         (partial_derivative j ((w:real->real^N->real^K) t)) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`b:real`; `\t x. partial_derivative j ((w:real->real^N->real^K) t) x`;
                   `i:num`] PDE_UPTO_PARTIAL) THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_UPTO_ADD THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`b:real`;
                   `\i t x. vsum(1..dimindex(:N))
                             (\j. ((aa:real->real^N->real^N^N) t x)$i$j %
                                  partial_derivative i
                                    (partial_derivative j ((w:real->real^N->real^K) t)) x)`;
                   `dimindex(:N)`] PDE_UPTO_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`b:real`;
                   `\j t x. ((aa:real->real^N->real^N^N) t x)$i$j %
                            partial_derivative i
                              (partial_derivative j ((w:real->real^N->real^K) t)) x`;
                   `dimindex(:N)`] PDE_UPTO_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`b:real`; `\(x:real^1) (y:real^K). drop x % y`;
                   `\t y. lift(((aa:real->real^N->real^N^N) t y)$i$j)`;
                   `\t x. partial_derivative i
                            (partial_derivative j ((w:real->real^N->real^K) t)) x`]
                  PDE_UPTO_BILINEAR) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`b:real`; `\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$i$j)`;
                   `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                            ((aa:real->real^N->real^N^N) t y)`] PDE_UPTO_LINEAR) THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_UPTO_ADD THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`b:real`;
                   `\i t x. (bb:real->real^N->num->real^K^K) t x i **
                            partial_derivative i ((w:real->real^N->real^K) t) x`;
                   `dimindex(:N)`] PDE_UPTO_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`b:real`;
                   `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((bb:real->real^N->num->real^K^K) t y i)`;
                   `\t x. partial_derivative i ((w:real->real^N->real^K) t) x`]
                  PDE_UPTO_BILINEAR) THEN
    REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; MATRIFY_VECTORIZE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`b:real`;
                   `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                            ((cc:real->real^N->real^K^K) t y)`;
                   `w:real->real^N->real^K`] PDE_UPTO_BILINEAR) THEN
    REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; MATRIFY_VECTORIZE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The operator preserves periodicity. *)

let PDE_ZPER_LOP0 = prove
 (`!(A:real^N->real^N^N) (B:real^N->num->real^K^K) C (w:real^N->real^K).
     pde_zper A /\ (!i. pde_zper (\x. B x i)) /\ pde_zper C /\
     smooth_map_on (:real^N) w /\ pde_zper w
     ==> pde_zper (pde_lop0 A B C w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. pde_zper (partial_derivative i (partial_derivative j (w:real^N->real^K))) /\
          pde_zper (partial_derivative i w)`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC PDE_ZPER_PARTIAL THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV; PDE_ZPER_PARTIAL];
    ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th -> can (find_term (fun tm ->
    try fst(dest_const tm) = "pde_zper" with Failure _ -> false)) (concl th))) THEN
  REWRITE_TAC[pde_zper; pde_lop0] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The iteration.  Congruence of solutions in the forcing, linearity of the  *)
(* operator in the map and in the coefficients, the sequence of iterates     *)
(* (PDE_ITER_EXISTS) and their differences (PDE_ITER_DIFF).                  *)
(* ========================================================================= *)

let PDE_TSOL_FORCING_EQ = prove
 (`!t1 (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc f g u0 u.
     (!t x. &0 < t /\ t < t1 ==> f t x = g t x)
     ==> (pde_tsol t1 aa bb cc f u0 u <=> pde_tsol t1 aa bb cc g u0 u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_tsol] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let PDE_LOP_LIN = prove
 (`!(aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc
    (u:real->real^N->real^K) v a b t x.
     smooth_map_on (:real^N) (u t) /\ smooth_map_on (:real^N) (v t)
     ==> pde_lop aa bb cc (\t x. a % u t x + b % v t x) t x =
         a % pde_lop aa bb cc u t x + b % pde_lop aa bb cc v t x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_LOP_LOP0] THEN
  MATCH_MP_TAC PDE_LOP0_LIN THEN ASM_REWRITE_TAC[]);;

let PDE_LOP_LOP0_FUN = prove
 (`!(aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc u t.
     pde_lop aa bb cc u t = pde_lop0 (aa t) (bb t) (cc t) (u t)`,
  REWRITE_TAC[FUN_EQ_THM; PDE_LOP_LOP0]);;

let PDE_LOP_COEFF_ADD = prove
 (`!(aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1 aa2 bb2 cc2
    (u:real->real^N->real^K) t x.
     pde_lop (\t x. aa1 t x + aa2 t x) (\t x i. bb1 t x i + bb2 t x i)
             (\t x. cc1 t x + cc2 t x) u t x =
     pde_lop aa1 bb1 cc1 u t x + pde_lop aa2 bb2 cc2 u t x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_lop; MATRIX_ADD_COMPONENT] THEN
  REWRITE_TAC[VECTOR_ADD_RDISTRIB; MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN
  SIMP_TAC[VSUM_ADD_NUMSEG; FINITE_NUMSEG] THEN VECTOR_ARITH_TAC);;

(* The iterates: u_0 solves with f, u_(k+1) with f + L2 u_k. *)

let PDE_ITER_EXISTS = prove
 (`!t1 tmax (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 f u0.
     pde_tbnd tmax aa2 bb2 cc2 /\ t1 <= tmax /\
     pde_upto (&0) t1 (:real^N) f /\ (!t. &0 <= t /\ t < t1 ==> pde_zper (f t)) /\
     pde_tbnd tmax aa1 bb1 cc1 /\
     (!g. pde_upto (&0) t1 (:real^N) g /\ (!t. &0 <= t /\ t < t1 ==> pde_zper (g t))
          ==> ?v. pde_tsol t1 aa1 bb1 cc1 g u0 v)
     ==> ?U. pde_tsol t1 aa1 bb1 cc1 f u0 (U 0) /\
             !k. pde_tsol t1 aa1 bb1 cc1
                   (\t x. f t x + pde_lop aa2 bb2 cc2 (U k) t x) u0 (U (SUC k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `SOL = \g. @v:real->real^N->real^K. pde_tsol t1 aa1 bb1 cc1 g u0 v` THEN
  SUBGOAL_THEN
   `!g. pde_upto (&0) t1 (:real^N) g /\ (!t. &0 <= t /\ t < t1 ==> pde_zper (g t))
        ==> pde_tsol t1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K)
                     cc1 g u0 (SOL g)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "SOL" THEN REWRITE_TAC[] THEN
    CONV_TAC SELECT_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(SOL:(real->real^N->real^K)->real->real^N->real^K) f`;
    `\(U:real->real^N->real^K) (k:num).
       (SOL:(real->real^N->real^K)->real->real^N->real^K)
         (\t x. f t x + pde_lop (aa2:real->real^N->real^N^N)
                          (bb2:real->real^N->num->real^K^K) cc2 U t x)`] num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:num->real->real^N->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!U:real->real^N->real^K.
      pde_upto (&0) t1 (:real^N) U /\ (!t. &0 <= t /\ t < t1 ==> pde_zper (U t))
      ==> pde_upto (&0) t1 (:real^N)
            (\t x. (f:real->real^N->real^K) t x +
                   pde_lop (aa2:real->real^N->real^N^N) (bb2:real->real^N->num->real^K^K)
                           cc2 U t x) /\
          (!t. &0 <= t /\ t < t1
               ==> pde_zper (\x. f t x + pde_lop aa2 bb2 cc2 U t x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC PDE_UPTO_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PDE_UPTO_LOP THEN EXISTS_TAC `tmax:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_ZPER_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[PDE_LOP_LOP0_FUN; PDE_LOP_LOP0; ETA_AX] THEN
      UNDISCH_TAC `pde_tbnd tmax (aa2:real->real^N->real^N^N)
                     (bb2:real->real^N->num->real^K^K) cc2` THEN
      REWRITE_TAC[pde_tbnd] THEN STRIP_TAC THEN
      MATCH_MP_TAC PDE_ZPER_LOP0 THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC PDE_UPTO_SLICE_SMOOTH THEN EXISTS_TAC `t1:real` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. pde_upto (&0) t1 (:real^N) ((U:num->real->real^N->real^K) k) /\
        (!t. &0 <= t /\ t < t1 ==> pde_zper (U k t))`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [SUBGOAL_THEN `pde_tsol t1 (aa1:real->real^N->real^N^N)
                      (bb1:real->real^N->num->real^K^K) cc1 f u0
                      ((U:num->real->real^N->real^K) 0)` MP_TAC THENL
       [ASM_SIMP_TAC[]; SIMP_TAC[pde_tsol]];
      SUBGOAL_THEN
       `pde_tsol t1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
          (\t x. (f:real->real^N->real^K) t x +
                 pde_lop (aa2:real->real^N->real^N^N) (bb2:real->real^N->num->real^K^K)
                         cc2 ((U:num->real->real^N->real^K) k) t x)
          u0 (U (SUC k))` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check
          (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `SOL:(real->real^N->real^K)->real->real^N->real^K`))
                         (concl th) &&
                     not (can (find_term ((=) `U:num->real->real^N->real^K`)) (concl th)))) THEN
        ASM_SIMP_TAC[];
        SIMP_TAC[pde_tsol]]];
    ALL_TAC] THEN
  EXISTS_TAC `U:num->real->real^N->real^K` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check
   (fun th -> is_forall(concl th) &&
              can (find_term ((=) `SOL:(real->real^N->real^K)->real->real^N->real^K`))
                  (concl th) &&
              not (can (find_term ((=) `U:num->real->real^N->real^K`)) (concl th)))) THEN
  ASM_SIMP_TAC[]);;

(* The differences of the iterates solve with zero data and forcing L2 of   *)
(* the previous difference.                                                  *)

let PDE_ITER_DIFF = prove
 (`!t1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1 aa2 bb2 cc2
    f u0 (U:num->real->real^N->real^K).
     pde_tsol t1 aa1 bb1 cc1 f u0 (U 0) /\
     (!k. pde_tsol t1 aa1 bb1 cc1 (\t x. f t x + pde_lop aa2 bb2 cc2 (U k) t x) u0
                   (U (SUC k)))
     ==> pde_tsol t1 aa1 bb1 cc1 (\t x. pde_lop aa2 bb2 cc2 (U 0) t x) (\x. vec 0)
                  (\t x. U (SUC 0) t x - U 0 t x) /\
         !k. pde_tsol t1 aa1 bb1 cc1
               (\t x. pde_lop aa2 bb2 cc2 (\t x. U (SUC k) t x - U k t x) t x) (\x. vec 0)
               (\t x. U (SUC (SUC k)) t x - U (SUC k) t x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`t1:real`; `aa1:real->real^N->real^N^N`;
                   `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                   `\t x. (f:real->real^N->real^K) t x +
                          pde_lop (aa2:real->real^N->real^N^N)
                                  (bb2:real->real^N->num->real^K^K) cc2
                                  ((U:num->real->real^N->real^K) 0) t x`;
                   `f:real->real^N->real^K`; `u0:real^N->real^K`; `u0:real^N->real^K`;
                   `(U:num->real->real^N->real^K) (SUC 0)`; `(U:num->real->real^N->real^K) 0`;
                   `&1`; `--(&1)`] PDE_TSOL_LIN2) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `&1 % (x:real^K) + --(&1) % y = x - y`;
                    VECTOR_ARITH `((a:real^K) + b) - a = b`; VECTOR_SUB_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN
  MP_TAC(ISPECL [`t1:real`; `aa1:real->real^N->real^N^N`;
                 `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                 `\t x. (f:real->real^N->real^K) t x +
                        pde_lop (aa2:real->real^N->real^N^N)
                                (bb2:real->real^N->num->real^K^K) cc2
                                ((U:num->real->real^N->real^K) (SUC k)) t x`;
                 `\t x. (f:real->real^N->real^K) t x +
                        pde_lop (aa2:real->real^N->real^N^N)
                                (bb2:real->real^N->num->real^K^K) cc2
                                ((U:num->real->real^N->real^K) k) t x`;
                 `u0:real^N->real^K`; `u0:real^N->real^K`;
                 `(U:num->real->real^N->real^K) (SUC (SUC k))`;
                 `(U:num->real->real^N->real^K) (SUC k)`; `&1`; `--(&1)`] PDE_TSOL_LIN2) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `&1 % (x:real^K) + --(&1) % y = x - y`;
                  VECTOR_ARITH `((a:real^K) + b) - (a + c) = b - c`; VECTOR_SUB_REFL] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
  MATCH_MP_TAC PDE_TSOL_FORCING_EQ THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) ((U:num->real->real^N->real^K) (SUC k) t) /\
                smooth_map_on (:real^N) ((U:num->real->real^N->real^K) k t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_UPTO_SLICE_SMOOTH THEN EXISTS_TAC `t1:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THENL
     [ASM_CASES_TAC `k = 0` THENL
       [ASM_MESON_TAC[pde_tsol];
        ASM_MESON_TAC[pde_tsol]];
      ASM_CASES_TAC `k = 0` THENL
       [ASM_MESON_TAC[pde_tsol];
        SUBGOAL_THEN `?j. k = SUC j` (X_CHOOSE_THEN `j:num` SUBST1_TAC) THENL
         [EXISTS_TAC `k - 1` THEN ASM_ARITH_TAC; ASM_MESON_TAC[pde_tsol]]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                 `cc2:real->real^N->real^K^K`; `(U:num->real->real^N->real^K) (SUC k)`;
                 `(U:num->real->real^N->real^K) k`; `&1`; `--(&1)`; `t:real`; `x:real^N`]
                PDE_LOP_LIN) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `&1 % (x:real^K) + --(&1) % y = x - y`; ETA_AX] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* The operator through the space-time partials of an extension              *)
(* (PDE_LOP_STOP), and the spatial parabolic jets of an extension bounded by *)
(* Sobolev (PDE_PJET0_SOBOLEV).                                              *)
(* ========================================================================= *)

let PDE_LOP_STOP = prove
 (`!(aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc (V:real->real^N->real^K)
    (FA:real^(1,N)finite_sum->real^(N,N)finite_prod)
    (FB:num->real^(1,N)finite_sum->real^(K,K)finite_prod)
    (FC:real^(1,N)finite_sum->real^(K,K)finite_prod) FV a b t y.
     smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) FV /\ a < t /\ t < b /\
     (!s y. a < s /\ s < b ==> FV(pastecart (lift s) y) = V s y) /\
     FA(pastecart (lift t) y) = vectorize(aa t y) /\
     (!i. FB i (pastecart (lift t) y) = vectorize(bb t y i)) /\
     FC(pastecart (lift t) y) = vectorize(cc t y)
     ==> pde_lop aa bb cc V t y =
         pde_stop (\z. matrify(FA z):real^N^N) (\z i. matrify(FB i z):real^K^K)
                  (\z. matrify(FC z):real^K^K) FV (pastecart (lift t) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(V:real->real^N->real^K) t =
                (\y. (FV:real^(1,N)finite_sum->real^K)(pastecart (lift t) y))`
  ASSUME_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[pde_lop; pde_stop; MATRIFY_VECTORIZE] THEN
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
        ==> iterated_partial l (\y. (FV:real^(1,N)finite_sum->real^K)(pastecart (lift t) y)) y =
            iterated_partial (MAP (\k. 1 + k) l) FV (pastecart (lift t) y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_SLAB_SLICE_ITERATED THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `[i:num; j]`) THEN
    ASM_REWRITE_TAC[ALL; MAP; iterated_partial];
    ALL_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `[i:num]`) THEN
    ASM_REWRITE_TAC[ALL; MAP; iterated_partial];
    REWRITE_TAC[]]);;

(* Spatial lists of space-time indices. *)

let PDE_NTIME_0_MAP = prove
 (`!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ pde_ntime l = 0
       ==> ALL (\i. 1 <= i /\ i <= dimindex(:N)) (MAP (\k. k - 1) l) /\
           l = MAP (\k. 1 + k) (MAP (\k. k - 1) l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN
  REWRITE_TAC[pde_ntime; FILTER; PDE_HEAT_DIMINDEX_ST] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pde_ntime; PDE_HEAT_DIMINDEX_ST]) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

let PDE_PJET0_SOBOLEV = prove
 (`!(FV:real^(1,N)finite_sum->real^K) (W:real->real^N->real^K) a b R t y C.
     smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) FV /\ a < t /\ t < b /\
     (!s y. a < s /\ s < b ==> FV(pastecart (lift s) y) = W s y) /\
     smooth_map_on (:real^N) (W t) /\ pde_zper (W t) /\ &0 < C /\
     (!(u:real^N->real^K) l x.
        smooth_map_on (:real^N) u /\ pde_zper u /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
        ==> norm(iterated_partial l u x) pow 2 <= C * pde_hs2 (dimindex(:N) + LENGTH l) u)
     ==> pde_pjet R 0 FV (pastecart (lift t) y) <=
         &(CARD(pde_index_lists R (:(1,N)finite_sum))) *
         sqrt(C * pde_hs2 (dimindex(:N) + R) (W t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pde_pjet; ADD_CLAUSES] THEN
  ABBREV_TAC `L = {l | ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                       pde_ntime l <= 0 /\ LENGTH l <= R /\ LENGTH l - pde_ntime l <= R}` THEN
  SUBGOAL_THEN `FINITE (L:num list->bool) /\ L SUBSET pde_index_lists R (:(1,N)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`R:num`; `0`] (INST_TYPE [`:(1,N)finite_sum`,`:M`] PDE_PJET_FINITE)) THEN
      REWRITE_TAC[ADD_CLAUSES];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; pde_index_lists] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(L:num list->bool)) *
              sqrt(C * pde_hs2 (dimindex(:N) + R) ((W:real->real^N->real^K) t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_BOUND THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `l:num list` THEN
    EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM; LE] THEN STRIP_TAC THEN
    MP_TAC(SPEC `l:num list` PDE_NTIME_0_MAP) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`FV:real^(1,N)finite_sum->real^K`; `a:real`; `b:real`;
                   `MAP (\k. k - 1) (l:num list)`; `t:real`; `y:real^N`]
                  PDE_SLAB_SLICE_ITERATED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(\y. (FV:real^(1,N)finite_sum->real^K)(pastecart (lift t) y)) =
                  (W:real->real^N->real^K) t`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * pde_hs2 (dimindex(:N) + LENGTH(MAP (\k. k - 1) (l:num list)))
                            ((W:real->real^N->real^K) t)` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC PDE_HS2_MONO THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE];
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; PDE_HS2_POS]]);;

(* Bounded coefficients give bounded space-time coefficient fields on the   *)
(* open slab (0,T2) x R^N.                                                   *)

let PDE_UPTO_SLAB_BOUND = prove
 (`!tmax (g:real->real^N->real^K) T2 p.
     pde_upto (&0) tmax (:real^N) g /\ (!t. pde_zper (g t)) /\ &0 < T2 /\ T2 < tmax
     ==> ?FG A. (!t y. &0 <= t /\ t < tmax ==> FG(pastecart (lift t) y) = g t y) /\
                smooth_map_on (interval(lift(&0),lift T2) PCROSS (:real^N)) FG /\ &0 <= A /\
                !l z. LENGTH l <= p /\ ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                      z IN interval(lift(&0),lift T2) PCROSS (:real^N)
                      ==> norm(iterated_partial l FG z) <= A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pde_upto]) THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^K`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`FG:real^(1,N)finite_sum->real^K`; `g:real->real^N->real^K`; `e:real`;
                 `tmax:real`] PDE_HEAT_EXT_ZPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC [`&0 < T2`; `T2 < tmax`] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`FG:real^(1,N)finite_sum->real^K`; `e:real`; `tmax:real`; `T2:real`; `p:num`]
                PDE_HEAT_SLAB_JET_BOUNDED) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`FG:real^(1,N)finite_sum->real^K`; `A:real`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(&0 - e),lift tmax) PCROSS (:real^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < e`; `T2 < tmax`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV] THEN
  X_GEN_TAC `w:real^1` THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `drop w`; `y:real^N`]) THEN
  ASM_SIMP_TAC[LIFT_DROP; REAL_LT_IMP_LE]);;

(* A field evaluated along space-time is bounded on the open slab when it   *)
(* is smooth up to t = 0 and periodic.                                       *)

let PDE_UPTO_ST_BOUND = prove
 (`!tmax (g:real->real^N->real^K) T2 p.
     pde_upto (&0) tmax (:real^N) g /\ (!t. pde_zper (g t)) /\ &0 < T2 /\ T2 < tmax
     ==> smooth_map_on (interval(lift(&0),lift T2) PCROSS (:real^N))
           (\z. g (drop(fstcart z)) (sndcart z)) /\
         ?A. &0 <= A /\
             !l z. LENGTH l <= p /\ ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                   z IN interval(lift(&0),lift T2) PCROSS (:real^N)
                   ==> norm(iterated_partial l (\z. g (drop(fstcart z)) (sndcart z)) z) <= A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `g:real->real^N->real^K`; `T2:real`; `p:num`]
                PDE_UPTO_SLAB_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^K` (X_CHOOSE_THEN `A:real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!z. z IN interval(lift(&0),lift T2) PCROSS (:real^N)
        ==> (FG:real^(1,N)finite_sum->real^K) z = g (drop(fstcart z)) (sndcart z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; IN_UNIV;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < x`; `x < T2`; `T2 < tmax`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `FG:real^(1,N)finite_sum->real^K` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
    ALL_TAC] THEN
  EXISTS_TAC `A:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(iterated_partial l (FG:real^(1,N)finite_sum->real^K) z)` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
  EXISTS_TAC `interval(lift(&0),lift T2) PCROSS (:real^N)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]);;

let PDE_TBND_STBND = prove
 (`!tmax (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc T2 p.
     pde_tbnd tmax aa bb cc /\ &0 < T2 /\ T2 < tmax
     ==> ?A. pde_stbnd (interval(lift(&0),lift T2) PCROSS (:real^N)) p A
               (\z. aa (drop(fstcart z)) (sndcart z))
               (\z i. bb (drop(fstcart z)) (sndcart z) i)
               (\z. cc (drop(fstcart z)) (sndcart z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tbnd] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`;
                 `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                         ((aa:real->real^N->real^N^N) t y)`;
                 `T2:real`; `p:num`] PDE_UPTO_ST_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC PDE_ZPER_COMPOSE THEN
    ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `AA:real` STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`tmax:real`;
                 `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                         ((cc:real->real^N->real^K^K) t y)`;
                 `T2:real`; `p:num`] PDE_UPTO_ST_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC PDE_ZPER_COMPOSE THEN
    ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `AC:real` STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN
   `!i. smooth_map_on (interval(lift(&0),lift T2) PCROSS (:real^N))
          (\z. (vectorize:real^K^K->real^(K,K)finite_prod)
                 ((bb:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)) /\
        ?A. &0 <= A /\
            !l z. LENGTH l <= p /\ ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                  z IN interval(lift(&0),lift T2) PCROSS (:real^N)
                  ==> norm(iterated_partial l
                             (\z. (vectorize:real^K^K->real^(K,K)finite_prod)
                                    (bb (drop(fstcart z)) (sndcart z) i)) z) <= A`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`tmax:real`;
                   `\t y. (vectorize:real^K^K->real^(K,K)finite_prod)
                           ((bb:real->real^N->num->real^K^K) t y i)`;
                   `T2:real`; `p:num`] PDE_UPTO_ST_BOUND) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    MP_TAC(ISPECL [`\y. (bb:real->real^N->num->real^K^K) t y i`;
                   `vectorize:real^K^K->real^(K,K)finite_prod`] PDE_ZPER_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_AND_THM; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `AB:num->real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `AA + sum(1..dimindex(:N)) AB + AC` THEN
  SUBGOAL_THEN `&0 <= sum(1..dimindex(:N)) AB` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pde_stbnd] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= AA`; `&0 <= AC`; `&0 <= sum(1..dimindex(:N)) AB`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `AA:real` THEN ASM_SIMP_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= AC`; `&0 <= sum(1..dimindex(:N)) AB`] THEN REAL_ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(AB:num->real) i` THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`AB:num->real`; `sum(1..dimindex(:N)) AB`; `1..dimindex(:N)`]
                  SUM_POS_BOUND) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL; IN_NUMSEG] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= AA`; `&0 <= AC`] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `AC:real` THEN ASM_SIMP_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= AA`; `&0 <= sum(1..dimindex(:N)) AB`] THEN REAL_ARITH_TAC]);;

(* The energies of the differences decay geometrically on [0,T2]. *)

let PDE_ITER_DECAY = prove
 (`!tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 a2 t1 T2 m (D:num->real->real^N->real^K).
     pde_tcoeff tmax lam1 aa1 bb1 cc1 /\ pde_tbnd tmax aa2 bb2 cc2 /\
     (!t x. &0 <= t /\ t < tmax
            ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) (aa2 t x)) <= a2) /\
     &8 * a2 pow 2 <= lam1 pow 2 /\ &0 < T2 /\ T2 < t1 /\ t1 <= tmax /\
     (!k. pde_upto (&0) t1 (:real^N) (D k) /\
          (!t. &0 <= t /\ t < t1 ==> pde_zper (D k t))) /\
     (!k. pde_tsol t1 aa1 bb1 cc1 (\t x. pde_lop aa2 bb2 cc2 (D k) t x) (\x. vec 0)
                   (D (SUC k)))
     ==> ?B. !k t. &0 <= t /\ t <= T2 ==> pde_hs2 m (D k t) <= B * inv(&2) pow k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                 `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                 `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                 `cc2:real->real^N->real^K^K`; `a2:real`; `t1:real`; `T2:real`; `m:num`]
                PDE_CONTRACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `mu:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!k. pde_zn m lam1 mu K T2 ((D:num->real->real^N->real^K) (SUC k)) <=
        pde_zn m lam1 mu K T2 (D k) / &2 /\
        !t. &0 <= t /\ t <= T2
            ==> exp(--(mu * t)) * pde_hs2 m (D (SUC k) t) <= pde_zn m lam1 mu K T2 (D k) / &2`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Z0 = pde_zn m lam1 mu K T2 ((D:num->real->real^N->real^K) 0)` THEN
  SUBGOAL_THEN `!k. pde_zn m lam1 mu K T2 ((D:num->real->real^N->real^K) k) <=
                    Z0 * inv(&2) pow k`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[real_pow; REAL_MUL_RID; REAL_LE_REFL];
      FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o SPEC `k:num`) THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. pde_hs2 m ((D:num->real->real^N->real^K) 0 t)`; `real_interval[&0,T2]`]
                REAL_CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_NE_EMPTY] THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < T2` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC PDE_UPTO_HS2_CONT THEN EXISTS_TAC `t1:real` THEN
      ASM_REWRITE_TAC[ETA_AX]];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `abs(pde_hs2 m ((D:num->real->real^N->real^K) 0 t0)) + exp(mu * T2) * abs Z0` THEN
  SUBGOAL_THEN `&0 <= exp(mu * T2) * abs Z0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE; REAL_ABS_POS]; ALL_TAC] THEN
  INDUCT_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[real_pow; REAL_MUL_RID] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `t0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= exp(mu * T2) * abs Z0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `&0 <= t`) (ASSUME `t <= T2`)) o
    SPEC `t:real` o CONJUNCT2 o SPEC `k:num` o
    check (fun th -> is_forall (concl th) &&
                     can (find_term (fun tm -> try fst(dest_const tm) = "exp"
                                               with Failure _ -> false)) (concl th))) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
    check (fun th -> is_forall (concl th) &&
                     can (find_term ((=) `Z0:real`)) (concl th))) THEN
  DISCH_TAC THEN
  ABBREV_TAC `E1 = pde_hs2 m ((D:num->real->real^N->real^K) (SUC k) t)` THEN
  ABBREV_TAC `Zk = pde_zn m lam1 mu K T2 ((D:num->real->real^N->real^K) k)` THEN
  ABBREV_TAC `q = inv(&2) pow k` THEN
  SUBGOAL_THEN `&0 <= E1` ASSUME_TAC THENL
   [EXPAND_TAC "E1" THEN MATCH_MP_TAC PDE_HS2_POS THEN MATCH_MP_TAC PDE_UPTO_SLICE_SMOOTH THEN
    EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `E1 = exp(mu * t) * (exp(--(mu * t)) * E1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL; REAL_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= exp(--(mu * t)) * E1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(mu * t) * (Z0 * q / &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(mu * T2) * (Z0 * q / &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(exp(mu * T2) * q) * Z0 <= (exp(mu * T2) * q) * abs Z0` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs(pde_hs2 m ((D:num->real->real^N->real^K) 0 t0)) * q`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The space-time equation of the extensions of the differences, their       *)
(* spatial jets decaying like rho^k, rho = sqrt(1/2), and summable bounds    *)
(* for every space-time partial (PDE_ITER_JET_SUMMABLE).                     *)
(* ========================================================================= *)

let PDE_LOP_STOP_CANON = prove
 (`!(aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc (V:real->real^N->real^K)
    FV a b t y.
     smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) FV /\ a < t /\ t < b /\
     (!s y. a < s /\ s < b ==> FV(pastecart (lift s) y) = V s y)
     ==> pde_lop aa bb cc V t y =
         pde_stop (\z. aa (drop(fstcart z)) (sndcart z))
                  (\z i. bb (drop(fstcart z)) (sndcart z) i)
                  (\z. cc (drop(fstcart z)) (sndcart z)) FV (pastecart (lift t) y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`aa:real->real^N->real^N^N`; `bb:real->real^N->num->real^K^K`;
                 `cc:real->real^N->real^K^K`; `V:real->real^N->real^K`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((aa:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))`;
                 `\i z. (vectorize:real^K^K->real^(K,K)finite_prod)
                          ((bb:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)`;
                 `\z. (vectorize:real^K^K->real^(K,K)finite_prod)
                        ((cc:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))`;
                 `FV:real^(1,N)finite_sum->real^K`; `a:real`; `b:real`; `t:real`; `y:real^N`]
                PDE_LOP_STOP) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; MATRIFY_VECTORIZE;
                  ETA_AX]);;

let PDE_ITER_ST_EQ = prove
 (`!t1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1 aa2 bb2 cc2
    (U:real->real^N->real^K) (W:real->real^N->real^K) FU FW eU eW T2 z.
     pde_tsol t1 aa1 bb1 cc1 (\t x. pde_lop aa2 bb2 cc2 W t x) (\x. vec 0) U /\
     &0 < eU /\ smooth_map_on (interval(lift(&0 - eU),lift t1) PCROSS (:real^N)) FU /\
     (!t y. &0 <= t /\ t < t1 ==> FU(pastecart (lift t) y) = U t y) /\
     &0 < eW /\ smooth_map_on (interval(lift(&0 - eW),lift t1) PCROSS (:real^N)) FW /\
     (!t y. &0 <= t /\ t < t1 ==> FW(pastecart (lift t) y) = W t y) /\
     T2 <= t1 /\ z IN interval(lift(&0),lift T2) PCROSS (:real^N)
     ==> partial_derivative 1 FU z =
         pde_stop (\z. aa1 (drop(fstcart z)) (sndcart z))
                  (\z i. bb1 (drop(fstcart z)) (sndcart z) i)
                  (\z. cc1 (drop(fstcart z)) (sndcart z)) FU z +
         pde_stop (\z. aa2 (drop(fstcart z)) (sndcart z))
                  (\z i. bb2 (drop(fstcart z)) (sndcart z) i)
                  (\z. cc2 (drop(fstcart z)) (sndcart z)) FW z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?t y. z = pastecart (lift t) (y:real^N) /\ &0 < t /\ t < T2`
  (X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`drop(fstcart(z:real^(1,N)finite_sum))`;
                          `sndcart(z:real^(1,N)finite_sum)`] THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND] THEN
    UNDISCH_TAC `z IN interval(lift(&0),lift T2) PCROSS (:real^N)` THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`t1:real`; `aa1:real->real^N->real^N^N`; `bb1:real->real^N->num->real^K^K`;
                 `cc1:real->real^N->real^K^K`;
                 `\t x. pde_lop (aa2:real->real^N->real^N^N)
                                (bb2:real->real^N->num->real^K^K) cc2
                                (W:real->real^N->real^K) t x`;
                 `\x:real^N. vec 0:real^K`; `U:real->real^N->real^K`;
                 `FU:real^(1,N)finite_sum->real^K`; `eU:real`; `t:real`; `y:real^N`]
                PDE_TSOL_TIME_PARTIAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC [`&0 < t`; `t < T2`; `T2 <= t1`] THEN
    REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!(G:real^(1,N)finite_sum->real^K) (X:real->real^N->real^K) e
     (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc.
      &0 < e /\ smooth_map_on (interval(lift(&0 - e),lift t1) PCROSS (:real^N)) G /\
      (!t y. &0 <= t /\ t < t1 ==> G(pastecart (lift t) y) = X t y)
      ==> pde_lop aa bb cc X t y =
            pde_stop (\z. aa (drop(fstcart z)) (sndcart z))
                     (\z i. bb (drop(fstcart z)) (sndcart z) i)
                     (\z. cc (drop(fstcart z)) (sndcart z)) G (pastecart (lift t) y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_LOP_STOP_CANON THEN
    MAP_EVERY EXISTS_TAC [`&0`; `t1:real`] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - e),lift t1) PCROSS (:real^N)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC [`t < T2`; `T2 <= t1`] THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  BINOP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
   [EXISTS_TAC `eU:real`; EXISTS_TAC `eW:real`] THEN ASM_REWRITE_TAC[]);;

(* Monotonicity of the space-time coefficient bounds in the constant. *)

let PDE_STBND_MONO = prove
 (`!S p A A' (a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c.
     pde_stbnd S p A a b c /\ A <= A' ==> pde_stbnd S p A' a b c`,
  REWRITE_TAC[pde_stbnd] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY ASM_REAL_ARITH_TAC THEN ASM_MESON_TAC[REAL_LE_TRANS]);;

(* The ratio rho = sqrt(1/2) of the geometric decay of the jets. *)

let PDE_RHO_BOUNDS = prove
 (`&0 < sqrt(inv(&2)) /\ sqrt(inv(&2)) < &1`,
  CONJ_TAC THENL
   [REWRITE_TAC[SQRT_LT_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN REWRITE_TAC[SQRT_MONO_LT_EQ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let PDE_SQRT_POW = prove
 (`!x n. sqrt(x pow n) = sqrt x pow n`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[real_pow; SQRT_1; SQRT_MUL]);;

(* A window of n + 1 consecutive terms of a geometric bound. *)

let PDE_GEOM_WINDOW = prove
 (`!(f:num->real) C2 n k rho.
     &0 < rho /\ rho <= &1 /\ n <= k /\ &0 <= C2 /\
     (!j. j <= n ==> f j <= C2 * rho pow (k - j))
     ==> sum(0..n) f <= (C2 * &(n + 1) * inv(rho pow n)) * rho pow k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..n) (\j. C2 * inv(rho pow n) * rho pow k)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C2 * rho pow (k - j)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(rho pow n) * rho pow k = rho pow k / rho pow n` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
    REWRITE_TAC[GSYM REAL_POW_ADD] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    REAL_ARITH_TAC]);;

(* Spatial jets of the differences decay like rho^k on the open slab.       *)

let PDE_ITER_SPACE_DECAY = prove
 (`!tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 a2 t1 T2 (D:num->real->real^N->real^K)
    (V:num->real^(1,N)finite_sum->real^K) E R.
     pde_tcoeff tmax lam1 aa1 bb1 cc1 /\ pde_tbnd tmax aa2 bb2 cc2 /\
     (!t x. &0 <= t /\ t < tmax
            ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) (aa2 t x)) <= a2) /\
     &8 * a2 pow 2 <= lam1 pow 2 /\ &0 < T2 /\ T2 < t1 /\ t1 <= tmax /\
     (!k. pde_upto (&0) t1 (:real^N) (D k) /\
          (!t. &0 <= t /\ t < t1 ==> pde_zper (D k t))) /\
     (!k. pde_tsol t1 aa1 bb1 cc1 (\t x. pde_lop aa2 bb2 cc2 (D k) t x) (\x. vec 0)
                   (D (SUC k))) /\
     (!k. &0 < E k /\
          smooth_map_on (interval(lift(&0 - E k),lift t1) PCROSS (:real^N)) (V k) /\
          !t y. &0 <= t /\ t < t1 ==> V k (pastecart (lift t) y) = D k t y)
     ==> ?C. &0 <= C /\
             !k z. z IN interval(lift(&0),lift T2) PCROSS (:real^N)
                   ==> pde_pjet R 0 (V k) z <= C * sqrt(inv(&2)) pow k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                 `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                 `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                 `cc2:real->real^N->real^K^K`; `a2:real`; `t1:real`; `T2:real`;
                 `dimindex(:N) + R`; `D:num->real->real^N->real^K`] PDE_ITER_DECAY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `B:real`)] THEN
  X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC PDE_TORUS_SOBOLEV_PARTIAL THEN
  EXISTS_TAC `&(CARD(pde_index_lists R (:(1,N)finite_sum))) * sqrt(C0 * abs B)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `z:real^(1,N)finite_sum`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?t y. z = pastecart (lift t) (y:real^N) /\ &0 < t /\ t < T2`
  (X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`drop(fstcart(z:real^(1,N)finite_sum))`;
                          `sndcart(z:real^(1,N)finite_sum)`] THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND] THEN
    UNDISCH_TAC `z IN interval(lift(&0),lift T2) PCROSS (:real^N)` THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `&0 <= t /\ t < t1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < t`; `t < T2`; `T2 < t1`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) ((D:num->real->real^N->real^K) k t) /\
                pde_zper ((D:num->real->real^N->real^K) k t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PDE_UPTO_SLICE_SMOOTH THEN EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(pde_index_lists R (:(1,N)finite_sum))) *
              sqrt(C0 * pde_hs2 (dimindex(:N) + R) ((D:num->real->real^N->real^K) k t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_PJET0_SOBOLEV THEN MAP_EVERY EXISTS_TAC [`&0`; `t1:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - (E:num->real) k),lift t1) PCROSS (:real^N)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      SUBGOAL_THEN `&0 < (E:num->real) k` MP_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS; GSYM PDE_SQRT_POW; GSYM SQRT_MUL] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN
   `pde_hs2 (dimindex(:N) + R) ((D:num->real->real^N->real^K) k t) <= B * inv(&2) pow k`
  MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `B * x <= abs B * x ==> h <= B * x ==> h <= abs B * x`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
  MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Summable bounds, on the closed slab [0,T2] x R^N, for every space-time   *)
(* partial of the extensions of the differences (time derivatives traded    *)
(* for space derivatives by PDE_PJET_SEQ_BOUND, then PDE_ITER_SPACE_DECAY). *)

let PDE_SLAB_CLOSURE = prove
 (`!T2. &0 < T2
        ==> closure(interval(lift(&0),lift T2) PCROSS (:real^N)) =
            interval[lift(&0),lift T2] PCROSS (:real^N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSURE_PCROSS; CLOSURE_UNIV] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC);;

let PDE_ITER_JET_SUMMABLE = prove
 (`!tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 a2 t1 T2 (D:num->real->real^N->real^K)
    (V:num->real^(1,N)finite_sum->real^K) E.
     pde_tcoeff tmax lam1 aa1 bb1 cc1 /\ pde_tbnd tmax aa2 bb2 cc2 /\
     (!t x. &0 <= t /\ t < tmax
            ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) (aa2 t x)) <= a2) /\
     &8 * a2 pow 2 <= lam1 pow 2 /\ &0 < T2 /\ T2 < t1 /\ t1 <= tmax /\
     (!k. pde_upto (&0) t1 (:real^N) (D k) /\
          (!t. &0 <= t /\ t < t1 ==> pde_zper (D k t))) /\
     (!k. pde_tsol t1 aa1 bb1 cc1 (\t x. pde_lop aa2 bb2 cc2 (D k) t x) (\x. vec 0)
                   (D (SUC k))) /\
     (!k. &0 < E k /\
          smooth_map_on (interval(lift(&0 - E k),lift t1) PCROSS (:real^N)) (V k) /\
          !t y. &0 <= t /\ t < t1 ==> V k (pastecart (lift t) y) = D k t y)
     ==> !l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
             ==> ?b N0. summable (from 0) (\k. lift(b k)) /\
                        !k z. N0 <= k /\ z IN interval[lift(&0),lift T2] PCROSS (:real^N)
                              ==> norm(iterated_partial l (V k) z) <= b k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. &0 < (E:num->real) k` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `T2 < tmax` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`T2 < t1`; `t1 <= tmax`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_tbnd tmax (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1`
  ASSUME_TAC THENL [ASM_MESON_TAC[PDE_TCOEFF_TBND]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. ?A. pde_stbnd (interval(lift(&0),lift T2) PCROSS (:real^N)) p A
              (\z. (aa1:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
              (\z i. (bb1:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
              (\z. (cc1:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z)) /\
            pde_stbnd (interval(lift(&0),lift T2) PCROSS (:real^N)) p A
              (\z. (aa2:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
              (\z i. (bb2:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
              (\z. (cc2:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN
    MP_TAC(ISPECL [`tmax:real`; `aa1:real->real^N->real^N^N`;
                   `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                   `T2:real`; `p:num`] PDE_TBND_STBND) THEN
    MP_TAC(ISPECL [`tmax:real`; `aa2:real->real^N->real^N^N`;
                   `bb2:real->real^N->num->real^K^K`; `cc2:real->real^N->real^K^K`;
                   `T2:real`; `p:num`] PDE_TBND_STBND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `A2:real`) THEN DISCH_THEN(X_CHOOSE_TAC `A1:real`) THEN
    EXISTS_TAC `max A1 A2` THEN CONJ_TAC THEN MATCH_MP_TAC PDE_STBND_MONO THENL
     [EXISTS_TAC `A1:real`; EXISTS_TAC `A2:real`] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. smooth_map_on (interval(lift(&0),lift T2) PCROSS (:real^N))
                      ((V:num->real^(1,N)finite_sum->real^K) k)` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(&0 - (E:num->real) k),lift t1) PCROSS (:real^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
    GEN_TAC THEN MP_TAC(SPEC `k:num` (ASSUME `!k. &0 < (E:num->real) k`)) THEN
    UNDISCH_TAC `T2 < t1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k z. z IN interval(lift(&0),lift T2) PCROSS (:real^N)
          ==> partial_derivative 1 ((V:num->real^(1,N)finite_sum->real^K) (SUC k)) z =
              pde_stop (\z. (aa1:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
                       (\z i. (bb1:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
                       (\z. (cc1:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))
                       (V(SUC k)) z +
              pde_stop (\z. (aa2:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
                       (\z i. (bb2:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
                       (\z. (cc2:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))
                       (V k) z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ITER_ST_EQ THEN
    MAP_EVERY EXISTS_TAC [`t1:real`; `(D:num->real->real^N->real^K) (SUC k)`;
                          `(D:num->real->real^N->real^K) k`; `(E:num->real) (SUC k)`;
                          `(E:num->real) k`; `T2:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift(&0),lift T2) PCROSS (:real^N)`;
                 `\z. (aa1:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)`;
                 `\z i. (bb1:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i`;
                 `\z. (cc1:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z)`;
                 `\z. (aa2:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)`;
                 `\z i. (bb2:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i`;
                 `\z. (cc2:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z)`;
                 `V:num->real^(1,N)finite_sum->real^K`] PDE_PJET_SEQ_BOUND) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`pde_ntime (l:num list)`; `LENGTH(l:num list) - pde_ntime l`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SEQ"))) THEN
  MP_TAC(ISPECL [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                 `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                 `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                 `cc2:real->real^N->real^K^K`; `a2:real`; `t1:real`; `T2:real`;
                 `D:num->real->real^N->real^K`; `V:num->real^(1,N)finite_sum->real^K`;
                 `E:num->real`; `(LENGTH(l:num list) - pde_ntime l) + 2 * pde_ntime l`]
                PDE_ITER_SPACE_DECAY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DEC"))) THEN
  EXISTS_TAC `\k. (C1 * C2 * &(pde_ntime (l:num list) + 1) *
                   inv(sqrt(inv(&2)) pow pde_ntime l)) * sqrt(inv(&2)) pow k` THEN
  EXISTS_TAC `pde_ntime (l:num list)` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `real_summable (from 0)
        (\k. (C1 * C2 * &(pde_ntime (l:num list) + 1) * inv(sqrt(inv(&2)) pow pde_ntime l)) *
             sqrt(inv(&2)) pow k)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN MATCH_MP_TAC REAL_SUMMABLE_GP THEN
      MP_TAC PDE_RHO_BOUNDS THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_SUMMABLE; o_DEF]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `z:real^(1,N)finite_sum`] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_CLOSURE_NORM_LE THEN
  EXISTS_TAC `interval(lift(&0),lift T2) PCROSS (:real^N)` THEN
  ASM_SIMP_TAC[PDE_SLAB_CLOSURE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(&0 - (E:num->real) k),lift t1) PCROSS (:real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
      MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      GEN_TAC THEN MP_TAC(SPEC `k:num` (ASSUME `!k. &0 < (E:num->real) k`)) THEN
      UNDISCH_TAC `T2 < t1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_pjet (LENGTH(l:num list) - pde_ntime l) (pde_ntime l)
                       ((V:num->real^(1,N)finite_sum->real^K) k) w` THEN
  CONJ_TAC THENL [MATCH_MP_TAC PDE_PJET_TERM THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C1 * sum(0..pde_ntime l)
                (\j. pde_pjet ((LENGTH(l:num list) - pde_ntime l) + 2 * pde_ntime l) 0
                              ((V:num->real^(1,N)finite_sum->real^K) (k - j)) w)` THEN
  CONJ_TAC THENL [USE_THEN "SEQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C1 * (C2 * &(pde_ntime (l:num list) + 1) * inv(sqrt(inv(&2)) pow pde_ntime l)) *
              sqrt(inv(&2)) pow k` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_GEOM_WINDOW THEN ASM_REWRITE_TAC[] THEN
    MP_TAC PDE_RHO_BOUNDS THEN SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "DEC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The series of the differences.  Data of the iteration (pde_itdata),       *)
(* telescoping sums, limits of pde_stop, the space-time equation with        *)
(* a forcing, smoothness of the series on slabs and on (0,t1) x R^N,         *)
(* continuity of the differentiated series up to t = 0.                      *)
(* ========================================================================= *)

(* The differences D k of the iterates, their space-time extensions V k     *)
(* (smooth on (-E k,t1) x R^N), with the hypotheses of PDE_ITER_DECAY.      *)

let pde_itdata = new_definition
 `pde_itdata tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
             aa2 bb2 cc2 a2 t1 (D:num->real->real^N->real^K)
             (V:num->real^(1,N)finite_sum->real^K) E <=>
    pde_tcoeff tmax lam1 aa1 bb1 cc1 /\ pde_tbnd tmax aa2 bb2 cc2 /\
    (!t x. &0 <= t /\ t < tmax
           ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) (aa2 t x)) <= a2) /\
    &8 * a2 pow 2 <= lam1 pow 2 /\ &0 < t1 /\ t1 <= tmax /\
    (!k. pde_upto (&0) t1 (:real^N) (D k) /\
         (!t. &0 <= t /\ t < t1 ==> pde_zper (D k t))) /\
    (!k. pde_tsol t1 aa1 bb1 cc1 (\t x. pde_lop aa2 bb2 cc2 (D k) t x) (\x. vec 0)
                  (D (SUC k))) /\
    (!k. &0 < E k /\
         smooth_map_on (interval(lift(&0 - E k),lift t1) PCROSS (:real^N)) (V k) /\
         !t y. &0 <= t /\ t < t1 ==> V k (pastecart (lift t) y) = D k t y)`;;

(* Telescoping sums. *)

let PDE_TELESCOPE1 = prove
 (`!(V:num->A->real^K) FU.
     V 0 = FU 0 /\ (!k. V (SUC k) = \z. FU (SUC k) z - FU k z)
     ==> !n z. vsum(0..n) (\k. V k z) = FU n z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0] THEN VECTOR_ARITH_TAC);;

let PDE_TELESCOPE2 = prove
 (`!(D:num->A->B->real^K) U.
     D 0 = U 0 /\ (!k. D (SUC k) = \t x. U (SUC k) t x - U k t x)
     ==> !n t x. vsum(0..n) (\k. D k t x) = U n t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0] THEN VECTOR_ARITH_TAC);;

(* pde_stop of a sequence converges when its space-time partials of order   *)
(* <= 2 converge.                                                            *)

let PDE_STOP_LIM = prove
 (`!(a:real^(1,N)finite_sum->real^N^N) (b:real^(1,N)finite_sum->num->real^K^K) c
    (W:num->real^(1,N)finite_sum->real^K) Wl z.
     (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ LENGTH l <= 2
          ==> ((\n. iterated_partial l (W n) z) --> iterated_partial l Wl z) sequentially)
     ==> ((\n. pde_stop a b c (W n) z) --> pde_stop a b c Wl z) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_stop] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> ((\n. partial_derivative (1 + i)
                      (partial_derivative (1 + j) ((W:num->real^(1,N)finite_sum->real^K) n))
                      (z:real^(1,N)finite_sum)) -->
               partial_derivative (1 + i)
                 (partial_derivative (1 + j) (Wl:real^(1,N)finite_sum->real^K)) z)
              sequentially`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `[1 + i; 1 + j]`) THEN
    REWRITE_TAC[iterated_partial; ALL; LENGTH; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ((\n. partial_derivative (1 + i) ((W:num->real^(1,N)finite_sum->real^K) n)
                    (z:real^(1,N)finite_sum)) -->
             partial_derivative (1 + i) (Wl:real^(1,N)finite_sum->real^K) z) sequentially`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `[1 + i]`) THEN
    REWRITE_TAC[iterated_partial; ALL; LENGTH; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. (W:num->real^(1,N)finite_sum->real^K) n z) -->
                 (Wl:real^(1,N)finite_sum->real^K) z) sequentially`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `[]:num list`) THEN
    REWRITE_TAC[iterated_partial; ALL; LENGTH] THEN ANTS_TAC THENL [ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC LIM_CMUL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`sequentially`;
                   `\x:real^K. ((b:real^(1,N)finite_sum->num->real^K^K) z i) ** x`;
                   `\n. partial_derivative (1 + i) ((W:num->real^(1,N)finite_sum->real^K) n) z`;
                   `partial_derivative (1 + i) (Wl:real^(1,N)finite_sum->real^K) z`]
                  LIM_LINEAR) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`sequentially`;
                   `\x:real^K. ((c:real^(1,N)finite_sum->real^K^K) z) ** x`;
                   `\n. (W:num->real^(1,N)finite_sum->real^K) n z`;
                   `(Wl:real^(1,N)finite_sum->real^K) z`] LIM_LINEAR) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* The space-time equation of the extension of a solution with forcing g.   *)

let PDE_TSOL_ST_EQ = prove
 (`!t1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1 g u0
    (U:real->real^N->real^K) FU eU t y.
     pde_tsol t1 aa1 bb1 cc1 g u0 U /\
     &0 < eU /\ smooth_map_on (interval(lift(&0 - eU),lift t1) PCROSS (:real^N)) FU /\
     (!t y. &0 <= t /\ t < t1 ==> FU(pastecart (lift t) y) = U t y) /\ &0 < t /\ t < t1
     ==> partial_derivative 1 FU (pastecart (lift t) y) =
         pde_stop (\z. aa1 (drop(fstcart z)) (sndcart z))
                  (\z i. bb1 (drop(fstcart z)) (sndcart z) i)
                  (\z. cc1 (drop(fstcart z)) (sndcart z)) FU (pastecart (lift t) y) + g t y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t1:real`; `aa1:real->real^N->real^N^N`; `bb1:real->real^N->num->real^K^K`;
                 `cc1:real->real^N->real^K^K`; `g:real->real^N->real^K`; `u0:real^N->real^K`;
                 `U:real->real^N->real^K`; `FU:real^(1,N)finite_sum->real^K`; `eU:real`;
                 `t:real`; `y:real^N`] PDE_TSOL_TIME_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC PDE_LOP_STOP_CANON THEN MAP_EVERY EXISTS_TAC [`&0`; `t1:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(&0 - eU),lift t1) PCROSS (:real^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
    UNDISCH_TAC `&0 < eU` THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* The series on a slab (0,T2) x R^N, T2 < t1: smooth, differentiable term  *)
(* by term; the differentiated series converge uniformly on [0,T2] x R^N.   *)

let PDE_ITER_SLAB_SERIES = prove
 (`!tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 a2 t1 (D:num->real->real^N->real^K)
    (V:num->real^(1,N)finite_sum->real^K) E T2.
     pde_itdata tmax lam1 aa1 bb1 cc1 aa2 bb2 cc2 a2 t1 D V E /\ &0 < T2 /\ T2 < t1
     ==> smooth_map_on (interval(lift(&0),lift T2) PCROSS (:real^N))
                       (\z. infsum (from 0) (\k. V k z)) /\
         (!l z. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                z IN interval(lift(&0),lift T2) PCROSS (:real^N)
                ==> ((\k. iterated_partial l (V k) z) sums
                     iterated_partial l (\z. infsum (from 0) (\k. V k z)) z) (from 0)) /\
         (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
              ==> (\z. infsum (from 0) (\k. iterated_partial l (V k) z)) continuous_on
                  (interval[lift(&0),lift T2] PCROSS (:real^N)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_itdata] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                 `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                 `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                 `cc2:real->real^N->real^K^K`; `a2:real`; `t1:real`; `T2:real`;
                 `D:num->real->real^N->real^K`; `V:num->real^(1,N)finite_sum->real^K`;
                 `E:num->real`] PDE_ITER_JET_SUMMABLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "JS")] THEN
  SUBGOAL_THEN `!k. &0 < (E:num->real) k` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. smooth_map_on (interval(lift(&0 - (E:num->real) k),lift t1) PCROSS (:real^N))
                      ((V:num->real^(1,N)finite_sum->real^K) k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interval(lift(&0),lift T2) PCROSS (:real^N) SUBSET
                interval[lift(&0),lift T2] PCROSS (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; INTERVAL_OPEN_SUBSET_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. interval[lift(&0),lift T2] PCROSS (:real^N) SUBSET
        interval(lift(&0 - (E:num->real) k),lift t1) PCROSS (:real^N)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
    GEN_TAC THEN MP_TAC(SPEC `k:num` (ASSUME `!k. &0 < (E:num->real) k`)) THEN
    UNDISCH_TAC `T2 < t1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift(&0),lift T2) PCROSS (:real^N)`;
                 `V:num->real^(1,N)finite_sum->real^K`] SMOOTH_MAP_ON_SERIES) THEN
  ANTS_TAC THENL
   [SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - (E:num->real) n),lift t1) PCROSS (:real^N)` THEN
      ASM_MESON_TAC[SUBSET_TRANS];
      X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
      USE_THEN "JS" (MP_TAC o SPEC `l:num list`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->real` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `x:real^(1,N)finite_sum`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `x IN interval(lift(&0),lift T2) PCROSS (:real^N)` THEN
      UNDISCH_TAC `interval(lift(&0),lift T2) PCROSS (:real^N) SUBSET
                   interval[lift(&0),lift T2] PCROSS (:real^N)` THEN
      SET_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  USE_THEN "JS" (MP_TAC o SPEC `l:num list`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->real` (X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`\k. iterated_partial l ((V:num->real^(1,N)finite_sum->real^K) k)`;
                 `b:num->real`; `interval[lift(&0),lift T2] PCROSS (:real^N)`;
                 `N0:num`] PDE_HEAT_MTEST_ON) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(&0 - (E:num->real) m),lift t1) PCROSS (:real^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
    SIMP_TAC[]]);;

(* The series on (0,t1) x R^N. *)

let PDE_ITER_SERIES_GLOBAL = prove
 (`!tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 a2 t1 (D:num->real->real^N->real^K)
    (V:num->real^(1,N)finite_sum->real^K) E.
     pde_itdata tmax lam1 aa1 bb1 cc1 aa2 bb2 cc2 a2 t1 D V E
     ==> smooth_map_on (interval(lift(&0),lift t1) PCROSS (:real^N))
                       (\z. infsum (from 0) (\k. V k z)) /\
         (!l z. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                z IN interval(lift(&0),lift t1) PCROSS (:real^N)
                ==> ((\k. iterated_partial l (V k) z) sums
                     iterated_partial l (\z. infsum (from 0) (\k. V k z)) z) (from 0)) /\
         (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
              ==> (\z. infsum (from 0) (\k. iterated_partial l (V k) z)) continuous_on
                  {pastecart (lift t) y | &0 <= t /\ t < t1 /\ y IN (:real^N)})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!z. z IN interval(lift(&0),lift t1) PCROSS (:real^N)
        ==> ?T2. &0 < T2 /\ T2 < t1 /\ z IN interval(lift(&0),lift T2) PCROSS (:real^N)`
  (LABEL_TAC "SL") THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    DISCH_TAC THEN EXISTS_TAC `(drop(fstcart(z:real^(1,N)finite_sum)) + t1) / &2` THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    REMOVE_THEN "SL" (MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `T2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `interval(lift(&0),lift T2) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    MP_TAC(ISPECL [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                   `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                   `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                   `cc2:real->real^N->real^K^K`; `a2:real`; `t1:real`;
                   `D:num->real->real^N->real^K`; `V:num->real^(1,N)finite_sum->real^K`;
                   `E:num->real`; `T2:real`] PDE_ITER_SLAB_SERIES) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`l:num list`; `z:real^(1,N)finite_sum`] THEN STRIP_TAC THEN
    REMOVE_THEN "SL" (MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `T2:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                   `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                   `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                   `cc2:real->real^N->real^K^K`; `a2:real`; `t1:real`;
                   `D:num->real->real^N->real^K`; `V:num->real^(1,N)finite_sum->real^K`;
                   `E:num->real`; `T2:real`] PDE_ITER_SLAB_SERIES) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN MATCH_MP_TAC PDE_HEAT_CONT_LOCAL THEN
    X_GEN_TAC `T2:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                   `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                   `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                   `cc2:real->real^N->real^K^K`; `a2:real`; `t1:real`;
                   `D:num->real->real^N->real^K`; `V:num->real^(1,N)finite_sum->real^K`;
                   `E:num->real`; `T2:real`] PDE_ITER_SLAB_SERIES) THEN
    ASM_SIMP_TAC[]]);;

(* The limit u = sum_k D_k is smooth up to t = 0 (PDE_SEELEY). *)

let PDE_ITER_LIMIT_UPTO = prove
 (`!tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 a2 t1 (D:num->real->real^N->real^K)
    (V:num->real^(1,N)finite_sum->real^K) E.
     pde_itdata tmax lam1 aa1 bb1 cc1 aa2 bb2 cc2 a2 t1 D V E
     ==> pde_upto (&0) t1 (:real^N) (\t y. infsum (from 0) (\k. D k t y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                 `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                 `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                 `cc2:real->real^N->real^K^K`; `a2:real`; `t1:real`;
                 `D:num->real->real^N->real^K`; `V:num->real^(1,N)finite_sum->real^K`;
                 `E:num->real`] PDE_ITER_SERIES_GLOBAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "SUMS") (LABEL_TAC "CONT"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_itdata]) THEN
  SUBGOAL_THEN
   `!t y. &0 <= t /\ t < t1
          ==> infsum (from 0)
                (\k. (V:num->real^(1,N)finite_sum->real^K) k (pastecart (lift t) y)) =
              infsum (from 0) (\k. (D:num->real->real^N->real^K) k t y)`
  (LABEL_TAC "EQ") THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN interval(lift(&0),lift t1) PCROSS (:real^N)
        ==> infsum (from 0) (\k. (V:num->real^(1,N)finite_sum->real^K) k w) =
            infsum (from 0)
              (\k. (D:num->real->real^N->real^K) k (drop(fstcart w)) (sndcart w))`
  (LABEL_TAC "EQW") THENL
   [X_GEN_TAC `w:real^(1,N)finite_sum` THEN REWRITE_TAC[PDE_IN_SLAB; IN_UNIV] THEN DISCH_TAC THEN
    USE_THEN "EQ" (MP_TAC o SPECL [`drop(fstcart(w:real^(1,N)finite_sum))`;
                                   `sndcart(w:real^(1,N)finite_sum)`]) THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_SEELEY THEN REWRITE_TAC[OPEN_UNIV] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\z. infsum (from 0)
                      (\k. iterated_partial [] ((V:num->real^(1,N)finite_sum->real^K) k) z)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC; iterated_partial; IN_UNIV] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      USE_THEN "EQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "CONT" MATCH_MP_TAC THEN REWRITE_TAC[ALL]];
    ALL_TAC] THEN
  REWRITE_TAC[pde_upto_classical] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\z. infsum (from 0) (\k. (V:num->real^(1,N)finite_sum->real^K) k z)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  EXISTS_TAC `\z. infsum (from 0)
                    (\k. iterated_partial l ((V:num->real^(1,N)finite_sum->real^K) k) z)` THEN
  CONJ_TAC THENL [USE_THEN "CONT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `iterated_partial l
                (\z. infsum (from 0) (\k. (V:num->real^(1,N)finite_sum->real^K) k z))
                (pastecart (lift t) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INFSUM_UNIQUE THEN USE_THEN "SUMS" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV];
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `interval(lift(&0),lift t1) PCROSS (:real^N)` THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]]);;

(* The limit solves u' = L1 u + f + L2 u: the time derivative of the series *)
(* is the limit of the time derivatives of the iterates U (SUC n), which    *)
(* satisfy U (SUC n)' = L1 U (SUC n) + f + L2 U n (PDE_TSOL_ST_EQ), and the *)
(* space-time partials of the iterates converge (telescoping sums).         *)

let PDE_ITER_LIMIT_EQ = prove
 (`!tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 a2 t1 (D:num->real->real^N->real^K)
    (V:num->real^(1,N)finite_sum->real^K) E f u0 (U:num->real->real^N->real^K) FU e t y.
     pde_itdata tmax lam1 aa1 bb1 cc1 aa2 bb2 cc2 a2 t1 D V E /\
     (!k. pde_tsol t1 aa1 bb1 cc1 (\t x. f t x + pde_lop aa2 bb2 cc2 (U k) t x) u0
                   (U (SUC k))) /\
     (!k. &0 < e k /\
          smooth_map_on (interval(lift(&0 - e k),lift t1) PCROSS (:real^N)) (FU k) /\
          !t y. &0 <= t /\ t < t1 ==> FU k (pastecart (lift t) y) = U k t y) /\
     V 0 = FU 0 /\ (!k. V (SUC k) = \z. FU (SUC k) z - FU k z) /\
     &0 < t /\ t < t1
     ==> ((\s. infsum (from 0) (\k. D k (drop s) y)) has_vector_derivative
          (pde_lop aa1 bb1 cc1 (\t y. infsum (from 0) (\k. D k t y)) t y +
           (f t y + pde_lop aa2 bb2 cc2 (\t y. infsum (from 0) (\k. D k t y)) t y)))
         (at (lift t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                 `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                 `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                 `cc2:real->real^N->real^K^K`; `a2:real`; `t1:real`;
                 `D:num->real->real^N->real^K`; `V:num->real^(1,N)finite_sum->real^K`;
                 `E:num->real`] PDE_ITER_SERIES_GLOBAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "SUMS") (K ALL_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_itdata]) THEN
  SUBGOAL_THEN `pastecart (lift t) (y:real^N) IN interval(lift(&0),lift t1) PCROSS (:real^N)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^(1,N)finite_sum->real^K`; `FU:num->real^(1,N)finite_sum->real^K`]
                PDE_TELESCOPE1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. smooth_map_on (interval(lift(&0),lift t1) PCROSS (:real^N))
                      ((V:num->real^(1,N)finite_sum->real^K) k)` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(&0 - (E:num->real) k),lift t1) PCROSS (:real^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
    SUBGOAL_THEN `&0 < (E:num->real) k` MP_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
        ==> ((\n. iterated_partial l ((FU:num->real^(1,N)finite_sum->real^K) n)
                    (pastecart (lift t) y)) -->
             iterated_partial l
               (\z. infsum (from 0) (\k. (V:num->real^(1,N)finite_sum->real^K) k z))
               (pastecart (lift t) y)) sequentially`
  (LABEL_TAC "LIMS") THENL
   [X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `((\k. iterated_partial l ((V:num->real^(1,N)finite_sum->real^K) k)
              (pastecart (lift t) y)) sums
       iterated_partial l (\z. infsum (from 0) (\k. V k z)) (pastecart (lift t) y)) (from 0)`
    MP_TAC THENL [USE_THEN "SUMS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `(FU:num->real^(1,N)finite_sum->real^K) n =
                  (\z. vsum(0..n) (\k. (V:num->real^(1,N)finite_sum->real^K) k z))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:num list`; `interval(lift(&0),lift t1) PCROSS (:real^N)`;
                   `V:num->real^(1,N)finite_sum->real^K`; `0..n`]
                  PDE_HEAT_ITERATED_PARTIAL_VSUM_OPEN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; FINITE_NUMSEG]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (y:real^N)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc.
      pde_lop aa bb cc (\t y. infsum (from 0) (\k. (D:num->real->real^N->real^K) k t y)) t y =
      pde_stop (\z. aa (drop(fstcart z)) (sndcart z))
               (\z i. bb (drop(fstcart z)) (sndcart z) i)
               (\z. cc (drop(fstcart z)) (sndcart z))
               (\z. infsum (from 0) (\k. (V:num->real^(1,N)finite_sum->real^K) k z))
               (pastecart (lift t) y)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC PDE_LOP_STOP_CANON THEN
    MAP_EVERY EXISTS_TAC [`&0`; `t1:real`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `w:real^N`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN ABS_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `partial_derivative 1
      (\z. infsum (from 0) (\k. (V:num->real^(1,N)finite_sum->real^K) k z))
      (pastecart (lift t) y) =
    pde_stop (\z. (aa1:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
             (\z i. (bb1:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
             (\z. (cc1:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))
             (\z. infsum (from 0) (\k. V k z)) (pastecart (lift t) y) +
    ((f:real->real^N->real^K) t y +
     pde_stop (\z. (aa2:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
              (\z i. (bb2:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
              (\z. (cc2:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))
              (\z. infsum (from 0) (\k. V k z)) (pastecart (lift t) y))`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. partial_derivative 1 ((FU:num->real^(1,N)finite_sum->real^K) (SUC n))
                                         (pastecart (lift t) y)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [USE_THEN "LIMS" (MP_TAC o SPEC `[1]`) THEN
      REWRITE_TAC[iterated_partial; ALL; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP SEQ_OFFSET) THEN REWRITE_TAC[GSYM ADD1];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. partial_derivative 1 ((FU:num->real^(1,N)finite_sum->real^K) (SUC n))
                             (pastecart (lift t) y) =
          pde_stop (\z. (aa1:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
                   (\z i. (bb1:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
                   (\z. (cc1:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))
                   (FU (SUC n)) (pastecart (lift t) y) +
          ((f:real->real^N->real^K) t y +
           pde_stop (\z. (aa2:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))
                    (\z i. (bb2:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i)
                    (\z. (cc2:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z))
                    (FU n) (pastecart (lift t) y))`
    (fun th -> REWRITE_TAC[th]) THENL
     [X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`t1:real`; `aa1:real->real^N->real^N^N`;
                     `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                     `\t x. (f:real->real^N->real^K) t x +
                            pde_lop (aa2:real->real^N->real^N^N)
                                    (bb2:real->real^N->num->real^K^K) cc2
                                    ((U:num->real->real^N->real^K) n) t x`;
                     `u0:real^N->real^K`; `(U:num->real->real^N->real^K) (SUC n)`;
                     `(FU:num->real^(1,N)finite_sum->real^K) (SUC n)`;
                     `(e:num->real) (SUC n)`; `t:real`; `y:real^N`] PDE_TSOL_ST_EQ) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC PDE_LOP_STOP_CANON THEN MAP_EVERY EXISTS_TAC [`&0`; `t1:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `interval(lift(&0 - (e:num->real) n),lift t1) PCROSS (:real^N)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
        REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
        SUBGOAL_THEN `&0 < (e:num->real) n` MP_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC];
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\z. (aa1:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)`;
                     `\z i. (bb1:real->real^N->num->real^K^K) (drop(fstcart z)) (sndcart z) i`;
                     `\z. (cc1:real->real^N->real^K^K) (drop(fstcart z)) (sndcart z)`;
                     `\n. (FU:num->real^(1,N)finite_sum->real^K) (SUC n)`;
                     `\z. infsum (from 0) (\k. (V:num->real^(1,N)finite_sum->real^K) k z)`;
                     `pastecart (lift t) (y:real^N)`] PDE_STOP_LIM) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      X_GEN_TAC `l:num list` THEN STRIP_TAC THEN
      USE_THEN "LIMS" (MP_TAC o SPEC `l:num list`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP SEQ_OFFSET) THEN REWRITE_TAC[GSYM ADD1];
      MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
      MATCH_MP_TAC PDE_STOP_LIM THEN X_GEN_TAC `l:num list` THEN STRIP_TAC THEN
      USE_THEN "LIMS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\r. (\z. infsum (from 0) (\k. (V:num->real^(1,N)finite_sum->real^K) k z))
                    (pastecart r y)` THEN
  EXISTS_TAC `min t (t1 - t)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_SUB_LT] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:real^1` THEN REWRITE_TAC[dist; NORM_1; DROP_SUB; LIFT_DROP] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= drop r /\ drop r < t1` STRIP_ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN MAP_EVERY UNDISCH_TAC [`&0 < t`; `t < t1`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[LIFT_DROP];
    MATCH_MP_TAC PDE_ST_TIME_DERIV THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift(&0),lift t1) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]]);;

(* The data of the iteration from the iterates and their extensions. *)

let PDE_ITER_ITDATA = prove
 (`!tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 a2 t1 f u0 (U:num->real->real^N->real^K) D FU e
    (V:num->real^(1,N)finite_sum->real^K) E.
     pde_tcoeff tmax lam1 aa1 bb1 cc1 /\ pde_tbnd tmax aa2 bb2 cc2 /\
     (!t x. &0 <= t /\ t < tmax
            ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) (aa2 t x)) <= a2) /\
     &8 * a2 pow 2 <= lam1 pow 2 /\ &0 < t1 /\ t1 <= tmax /\
     pde_tsol t1 aa1 bb1 cc1 f u0 (U 0) /\
     (!k. pde_tsol t1 aa1 bb1 cc1 (\t x. f t x + pde_lop aa2 bb2 cc2 (U k) t x) u0
                   (U (SUC k))) /\
     D 0 = U 0 /\ (!k. D (SUC k) = \t x. U (SUC k) t x - U k t x) /\
     (!k. &0 < e k /\
          smooth_map_on (interval(lift(&0 - e k),lift t1) PCROSS (:real^N)) (FU k) /\
          !t y. &0 <= t /\ t < t1 ==> FU k (pastecart (lift t) y) = U k t y) /\
     V 0 = FU 0 /\ (!k. V (SUC k) = \z. FU (SUC k) z - FU k z) /\
     E 0 = e 0 /\ (!k. E (SUC k) = min (e (SUC k)) (e k))
     ==> pde_itdata tmax lam1 aa1 bb1 cc1 aa2 bb2 cc2 a2 t1 D V E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t1:real`; `aa1:real->real^N->real^N^N`; `bb1:real->real^N->num->real^K^K`;
                 `cc1:real->real^N->real^K^K`; `aa2:real->real^N->real^N^N`;
                 `bb2:real->real^N->num->real^K^K`; `cc2:real->real^N->real^K^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`;
                 `U:num->real->real^N->real^K`] PDE_ITER_DIFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. pde_tsol t1 aa1 bb1 cc1
          (\t x. pde_lop aa2 bb2 cc2 ((D:num->real->real^N->real^K) k) t x)
          (\x. vec 0) (D (SUC k))`
  ASSUME_TAC THENL [INDUCT_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. ?g w0. pde_tsol t1 aa1 bb1 cc1 g w0 ((D:num->real->real^N->real^K) k)`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [MAP_EVERY EXISTS_TAC [`f:real->real^N->real^K`; `u0:real^N->real^K`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC
       [`\t x. pde_lop (aa2:real->real^N->real^N^N) (bb2:real->real^N->num->real^K^K) cc2
                       ((D:num->real->real^N->real^K) k) t x`;
        `\x:real^N. vec 0:real^K`] THEN
      FIRST_ASSUM(ACCEPT_TAC o SPEC `k:num`)];
    REWRITE_TAC[pde_tsol] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `!k. pde_upto (&0) t1 (:real^N) ((D:num->real->real^N->real^K) k) /\
                    (!t. &0 <= t /\ t < t1 ==> pde_zper (D k t))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. &0 < (E:num->real) k /\
        smooth_map_on (interval(lift(&0 - E k),lift t1) PCROSS (:real^N))
                      ((V:num->real^(1,N)finite_sum->real^K) k) /\
        !t y. &0 <= t /\ t < t1
              ==> V k (pastecart (lift t) y) = (D:num->real->real^N->real^K) k t y`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
        SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
         [EXISTS_TAC `interval(lift(&0 - (e:num->real) (SUC k)),lift t1) PCROSS (:real^N)`;
          EXISTS_TAC `interval(lift(&0 - (e:num->real) k),lift t1) PCROSS (:real^N)`] THEN
        ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC PCROSS_MONO THEN
        REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[pde_itdata] THEN ASM_REWRITE_TAC[]);;

(* Periodicity and initial value of the limit. *)

let PDE_ITER_LIMIT_ZPER = prove
 (`!t1 (D:num->real->real^N->real^K) t.
     (!k t. &0 <= t /\ t < t1 ==> pde_zper (D k t)) /\ &0 <= t /\ t < t1
     ==> pde_zper (\y. infsum (from 0) (\k. D k t y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_zper] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[pde_zper] o SPECL [`k:num`; `t:real`]) THEN
  ASM_SIMP_TAC[]);;

let PDE_ITER_LIMIT_INIT = prove
 (`!t1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1 aa2 bb2 cc2 f u0
    (U:num->real->real^N->real^K) (D:num->real->real^N->real^K).
     pde_tsol t1 aa1 bb1 cc1 f u0 (U 0) /\
     (!k. pde_tsol t1 aa1 bb1 cc1 (\t x. f t x + pde_lop aa2 bb2 cc2 (U k) t x) u0
                   (U (SUC k))) /\
     D 0 = U 0 /\ (!k. D (SUC k) = \t x. U (SUC k) t x - U k t x)
     ==> !y. infsum (from 0) (\k. D k (&0) y) = u0 y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN
  SUBGOAL_THEN `!n. (U:num->real->real^N->real^K) n (&0) y = u0 y` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pde_tsol]) THEN INDUCT_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN
  MP_TAC(ISPECL [`D:num->real->real^N->real^K`; `U:num->real->real^N->real^K`]
                PDE_TELESCOPE2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[LIM_CONST]);;

(* The limit of the iteration: a solution of u' = L1 u + f + L2 u. *)

let PDE_ITER_LIMIT = prove
 (`!tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 a2 t1 f u0 (U:num->real->real^N->real^K).
     pde_tcoeff tmax lam1 aa1 bb1 cc1 /\ pde_tbnd tmax aa2 bb2 cc2 /\
     (!t x. &0 <= t /\ t < tmax
            ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) (aa2 t x)) <= a2) /\
     &8 * a2 pow 2 <= lam1 pow 2 /\ &0 < t1 /\ t1 <= tmax /\
     pde_tsol t1 aa1 bb1 cc1 f u0 (U 0) /\
     (!k. pde_tsol t1 aa1 bb1 cc1 (\t x. f t x + pde_lop aa2 bb2 cc2 (U k) t x) u0
                   (U (SUC k)))
     ==> ?u. pde_tsol t1 aa1 bb1 cc1 (\t x. f t x + pde_lop aa2 bb2 cc2 u t x) u0 u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?D:num->real->real^N->real^K.
                  D 0 = U 0 /\ !k. D (SUC k) = \t x. U (SUC k) t x - U k t x`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\k. if k = 0 then (U:num->real->real^N->real^K) 0
                    else \t x. U k t x - U (PRE k) t x` THEN
    REWRITE_TAC[NOT_SUC; PRE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ?ek FUk. &0 < ek /\
                 smooth_map_on (interval(lift(&0 - ek),lift t1) PCROSS (:real^N)) FUk /\
                 !t y. &0 <= t /\ t < t1
                       ==> FUk (pastecart (lift t) y) = (U:num->real->real^N->real^K) k t y`
  MP_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `pde_upto (&0) t1 (:real^N) ((U:num->real->real^N->real^K) k)` MP_TAC THENL
     [STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN ASM_MESON_TAC[pde_tsol];
      REWRITE_TAC[pde_upto; IN_UNIV] THEN MESON_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num->real`
      (X_CHOOSE_THEN `FU:num->real^(1,N)finite_sum->real^K` ASSUME_TAC))] THEN
  SUBGOAL_THEN `?V:num->real^(1,N)finite_sum->real^K.
                  V 0 = FU 0 /\ !k. V (SUC k) = \z. FU (SUC k) z - FU k z`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\k. if k = 0 then (FU:num->real^(1,N)finite_sum->real^K) 0
                    else \z. FU k z - FU (PRE k) z` THEN
    REWRITE_TAC[NOT_SUC; PRE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?E:num->real. E 0 = e 0 /\ !k. E (SUC k) = min (e (SUC k)) (e k)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\k. if k = 0 then (e:num->real) 0 else min (e k) (e (PRE k))` THEN
    REWRITE_TAC[NOT_SUC; PRE];
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_itdata tmax lam1 (aa1:real->real^N->real^N^N)
                  (bb1:real->real^N->num->real^K^K) cc1 aa2 bb2 cc2 a2 t1
                  (D:num->real->real^N->real^K) (V:num->real^(1,N)finite_sum->real^K) E`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_ITER_ITDATA THEN
    MAP_EVERY EXISTS_TAC [`f:real->real^N->real^K`; `u0:real^N->real^K`;
                          `U:num->real->real^N->real^K`;
                          `FU:num->real^(1,N)finite_sum->real^K`; `e:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\t y. infsum (from 0) (\k. (D:num->real->real^N->real^K) k t y)` THEN
  REWRITE_TAC[pde_tsol] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_ITER_LIMIT_UPTO THEN
    MAP_EVERY EXISTS_TAC [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                          `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                          `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                          `cc2:real->real^N->real^K^K`; `a2:real`;
                          `V:num->real^(1,N)finite_sum->real^K`; `E:num->real`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ITER_LIMIT_ZPER THEN EXISTS_TAC `t1:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[pde_itdata];
    MATCH_MP_TAC PDE_ITER_LIMIT_INIT THEN
    MAP_EVERY EXISTS_TAC [`t1:real`; `aa1:real->real^N->real^N^N`;
                          `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                          `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                          `cc2:real->real^N->real^K^K`; `f:real->real^N->real^K`;
                          `U:num->real->real^N->real^K`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ITER_LIMIT_EQ THEN
    MAP_EVERY EXISTS_TAC [`tmax:real`; `lam1:real`; `a2:real`; `t1:real`;
                          `V:num->real^(1,N)finite_sum->real^K`; `E:num->real`;
                          `u0:real^N->real^K`; `U:num->real->real^N->real^K`;
                          `FU:num->real^(1,N)finite_sum->real^K`; `e:num->real`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The continuity method on [0,t1), t1 < tmax.  The family                   *)
(* L_s = (1 - s) Laplacian + s L (coefficients mat 1 + s (aa - mat 1), s bb, *)
(* s cc), solvability (pde_solvable), the step PDE_CONT_STEP                 *)
(* (by PDE_ITER_EXISTS and PDE_ITER_LIMIT), the base case (PDE_TORUS_HEAT)   *)
(* and PDE_CONT_METHOD.                                                      *)
(* ========================================================================= *)

let PDE_UPTO_CMUL_SUB = prove
 (`!b (f:real->real^N->real^P) s d.
     pde_upto (&0) b (:real^N) f ==> pde_upto (&0) b (:real^N) (\t x. s % (f t x - d))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^P`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `\z. s % ((FG:real^(1,N)finite_sum->real^P) z - d)`] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; SMOOTH_MAP_ON_CONST; ETA_AX]);;

let PDE_UPTO_CMUL = prove
 (`!b (f:real->real^N->real^P) s.
     pde_upto (&0) b (:real^N) f ==> pde_upto (&0) b (:real^N) (\t x. s % f t x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^P`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `\z. s % (FG:real^(1,N)finite_sum->real^P) z`] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; ETA_AX]);;

let PDE_TCOEFF_MONO = prove
 (`!tmax t1 lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc.
     pde_tcoeff tmax lam aa bb cc /\ t1 <= tmax ==> pde_tcoeff t1 lam aa bb cc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tcoeff] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `tmax:real` THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `tmax:real` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `tmax:real` THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= t`; `t < t1`; `t1 <= tmax`] THEN REAL_ARITH_TAC]);;

let PDE_TBND_MONO = prove
 (`!tmax t1 (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc.
     pde_tbnd tmax aa bb cc /\ t1 <= tmax ==> pde_tbnd t1 aa bb cc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tbnd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN
  EXISTS_TAC `tmax:real` THEN ASM_REWRITE_TAC[]);;

(* The homotopy from the Laplacian to L. *)

let PDE_TCOEFF_HOM = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc s.
     pde_tcoeff tmax lam aa bb cc /\ &0 <= s /\ s <= &1
     ==> pde_tcoeff tmax (min (&1) lam) (\t y. mat 1 + s %% (aa t y - mat 1))
                    (\t y i. s %% bb t y i) (\t y. s %% cc t y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tcoeff] THEN STRIP_TAC THEN
  REWRITE_TAC[VECTORIZE_ADD; VECTORIZE_CMUL; VECTORIZE_SUB] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01];
    MATCH_MP_TAC PDE_UPTO_ADD THEN REWRITE_TAC[PDE_UPTO_CONST] THEN
    MATCH_MP_TAC PDE_UPTO_CMUL_SUB THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC PDE_UPTO_CMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_UPTO_CMUL THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN REWRITE_TAC[pde_zper] THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL; TRANSP_MATRIX_SUB; TRANSP_MAT];
      ALL_TAC] THEN
    X_GEN_TAC `v:real^N` THEN FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_LID; MATRIX_VECTOR_LMUL;
                MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RADD; DOT_RMUL; DOT_RSUB; NORM_POW_2] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= ((v:real^N) dot v) *
                        ((&1 - s) * (&1 - min (&1) lam) + s * (lam - min (&1) lam))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[DOT_POS_LE] THEN MATCH_MP_TAC REAL_LE_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      MAP_EVERY UNDISCH_TAC [`&0 <= s`; `s <= &1`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `s * (lam * ((v:real^N) dot v)) <=
                  s * (v dot ((aa:real->real^N->real^N^N) t y ** v))`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

let PDE_TBND_PERT = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc d.
     pde_tcoeff tmax lam aa bb cc
     ==> pde_tbnd tmax (\t y. d %% (aa t y - mat 1)) (\t y i. d %% bb t y i)
                  (\t y. d %% cc t y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tcoeff; pde_tbnd] THEN STRIP_TAC THEN
  REWRITE_TAC[VECTORIZE_CMUL; VECTORIZE_SUB] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_UPTO_CMUL_SUB THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC PDE_UPTO_CMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_UPTO_CMUL THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN REWRITE_TAC[pde_zper] THEN ASM_SIMP_TAC[]]);;

let PDE_HOM_ADD = prove
 (`!(aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) (cc:real->real^N->real^K^K)
    s s'.
     (\t x. (mat 1 + s %% (aa t x - mat 1)) + (s' - s) %% (aa t x - mat 1)) =
     (\t y. mat 1 + s' %% (aa t y - mat 1)) /\
     (\t x i. s %% bb t x i + (s' - s) %% bb t x i) = (\t y i. s' %% bb t y i) /\
     (\t x. s %% cc t x + (s' - s) %% cc t x) = (\t y. s' %% cc t y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
  REWRITE_TAC[VECTORIZE_ADD; VECTORIZE_CMUL; VECTORIZE_SUB] THEN VECTOR_ARITH_TAC);;

(* Splitting the operator between coefficients and forcing. *)

let PDE_TSOL_COEFF_SPLIT = prove
 (`!t1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1 aa2 bb2 cc2
    (g:real->real^N->real^K) u0 u.
     pde_tsol t1 aa1 bb1 cc1 (\t x. g t x + pde_lop aa2 bb2 cc2 u t x) u0 u
     ==> pde_tsol t1 (\t x. aa1 t x + aa2 t x) (\t x i. bb1 t x i + bb2 t x i)
                  (\t x. cc1 t x + cc2 t x) g u0 u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tsol; PDE_LOP_COEFF_ADD] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

(* Solvability on [0,t1) for all data. *)

let pde_solvable = new_definition
 `pde_solvable t1 (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K)
               (cc:real->real^N->real^K^K) <=>
    !g u0. pde_upto (&0) t1 (:real^N) g /\ (!t. &0 <= t /\ t < t1 ==> pde_zper (g t)) /\
           smooth_map_on (:real^N) u0 /\ pde_zper u0
           ==> ?u. pde_tsol t1 aa bb cc g u0 u`;;

let PDE_CONT_STEP = prove
 (`!tmax lam1 (aa1:real->real^N->real^N^N) (bb1:real->real^N->num->real^K^K) cc1
    aa2 bb2 cc2 a2 t1.
     pde_tcoeff tmax lam1 aa1 bb1 cc1 /\ pde_tbnd tmax aa2 bb2 cc2 /\
     (!t x. &0 <= t /\ t < tmax
            ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) (aa2 t x)) <= a2) /\
     &8 * a2 pow 2 <= lam1 pow 2 /\ &0 < t1 /\ t1 <= tmax /\
     pde_solvable t1 aa1 bb1 cc1
     ==> pde_solvable t1 (\t x. aa1 t x + aa2 t x) (\t x i. bb1 t x i + bb2 t x i)
                      (\t x. cc1 t x + cc2 t x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pde_solvable] THEN
  MAP_EVERY X_GEN_TAC [`g:real->real^N->real^K`; `u0:real^N->real^K`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t1:real`; `tmax:real`; `aa1:real->real^N->real^N^N`;
                 `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                 `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                 `cc2:real->real^N->real^K^K`; `g:real->real^N->real^K`; `u0:real^N->real^K`]
                PDE_ITER_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[PDE_TCOEFF_TBND]; ALL_TAC] THEN
    X_GEN_TAC `h:real->real^N->real^K` THEN STRIP_TAC THEN
    UNDISCH_TAC `pde_solvable t1 (aa1:real->real^N->real^N^N)
                   (bb1:real->real^N->num->real^K^K) cc1` THEN
    REWRITE_TAC[pde_solvable] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `U:num->real->real^N->real^K` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`tmax:real`; `lam1:real`; `aa1:real->real^N->real^N^N`;
                 `bb1:real->real^N->num->real^K^K`; `cc1:real->real^N->real^K^K`;
                 `aa2:real->real^N->real^N^N`; `bb2:real->real^N->num->real^K^K`;
                 `cc2:real->real^N->real^K^K`; `a2:real`; `t1:real`;
                 `g:real->real^N->real^K`; `u0:real^N->real^K`;
                 `U:num->real->real^N->real^K`] PDE_ITER_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[PDE_TSOL_COEFF_SPLIT]);;

(* The base case: the heat equation. *)

let PDE_SOLVABLE_HEAT = prove
 (`!t1. &0 < t1
        ==> pde_solvable t1 (\t y. mat 1:real^N^N) (\t y i. mat 0:real^K^K)
                         (\t y. mat 0:real^K^K)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_solvable] THEN
  MAP_EVERY X_GEN_TAC [`g:real->real^N->real^K`; `u0:real^N->real^K`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t1:real`;
                 `\t x. if &0 <= t /\ t < t1 then (g:real->real^N->real^K) t x else vec 0`;
                 `u0:real^N->real^K`] PDE_TORUS_HEAT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `pde_upto (&0) t1 (:real^N) (g:real->real^N->real^K)` THEN
      REWRITE_TAC[pde_upto] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      X_GEN_TAC `t:real` THEN ASM_CASES_TAC `&0 <= t /\ t < t1` THEN
      ASM_SIMP_TAC[ETA_AX; PDE_ZPER_CONST]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real->real^N->real^K` THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN MATCH_MP_TAC PDE_TSOL_FORCING_EQ THEN
    SIMP_TAC[REAL_LT_IMP_LE]]);;

(* The continuity method: solvability on [0,t1) for every t1 < tmax. *)

let PDE_CONT_STEPSIZE = prove
 (`!A m. &0 <= A /\ &0 < m
         ==> ?d. &0 < d /\ !d'. &0 <= d' /\ d' <= d ==> &8 * (d' * A) pow 2 <= m pow 2`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `m / (&3 * (A + &1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `d':real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m / (&3 * (A + &1)) * (A + &1) = m / &3` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= A` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d' * A /\ d' * A <= m / &3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m / (&3 * (A + &1)) * A` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&8 * (m / &3) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POW_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC(SPEC `m:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

let PDE_CONT_METHOD = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc t1.
     pde_tcoeff tmax lam aa bb cc /\ &0 < t1 /\ t1 < tmax
     ==> pde_solvable t1 aa bb cc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL [ASM_MESON_TAC[pde_tcoeff]; ALL_TAC] THEN
  SUBGOAL_THEN `?t2. t1 < t2 /\ t2 < tmax` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(t1 + tmax) / &2` THEN UNDISCH_TAC `t1 < tmax` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?A. &0 <= A /\
        !t x. &0 <= t /\ t < t2
              ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                         ((aa:real->real^N->real^N^N) t x - mat 1)) <= A`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tmax:real`;
                   `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                            ((aa:real->real^N->real^N^N) t y)`;
                   `t2:real`; `0`] PDE_UPTO_JET_BOUND) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pde_tcoeff]) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC PDE_ZPER_COMPOSE THEN ASM_REWRITE_TAC[ETA_AX];
        MAP_EVERY UNDISCH_TAC [`&0 < t1`; `t1 < t2`] THEN REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `A0:real` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `A0 + norm((vectorize:real^N^N->real^(N,N)finite_prod) (mat 1))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPEC `(vectorize:real^N^N->real^(N,N)finite_prod) (mat 1)` NORM_POS_LE) THEN
      UNDISCH_TAC `&0 <= A0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[VECTORIZE_SUB] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:real^(N,N)finite_prod) <= A0 ==> norm(a - b) <= A0 + norm b`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `[]:num list`; `x:real^N`]) THEN
    REWRITE_TAC[iterated_partial; LENGTH; ALL; LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= t`; `t < t2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real`; `min (&1) lam`] PDE_CONT_STEPSIZE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. pde_solvable t1
          (\t y. mat 1 + min (&1) (&n * d) %% ((aa:real->real^N->real^N^N) t y - mat 1))
          (\t y i. min (&1) (&n * d) %% (bb:real->real^N->num->real^K^K) t y i)
          (\t y. min (&1) (&n * d) %% (cc:real->real^N->real^K^K) t y)`
  (LABEL_TAC "IND") THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[REAL_MUL_LZERO; REAL_ARITH `min (&1) (&0) = &0`; MATRIX_CMUL_LZERO;
                  MATRIX_ADD_RID] THEN
      MATCH_MP_TAC PDE_SOLVABLE_HEAT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= min (&1) (&n * d) /\ min (&1) (&n * d) <= &1 /\
      &0 <= min (&1) (&(SUC n) * d) - min (&1) (&n * d) /\
      min (&1) (&(SUC n) * d) - min (&1) (&n * d) <= d`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
      SUBGOAL_THEN `&0 <= &n * d` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`t2:real`; `min (&1) lam`;
      `\t y. mat 1 + min (&1) (&n * d) %% ((aa:real->real^N->real^N^N) t y - mat 1)`;
      `\t y i. min (&1) (&n * d) %% (bb:real->real^N->num->real^K^K) t y i`;
      `\t y. min (&1) (&n * d) %% (cc:real->real^N->real^K^K) t y`;
      `\t y. (min (&1) (&(SUC n) * d) - min (&1) (&n * d)) %%
             ((aa:real->real^N->real^N^N) t y - mat 1)`;
      `\t y i. (min (&1) (&(SUC n) * d) - min (&1) (&n * d)) %%
               (bb:real->real^N->num->real^K^K) t y i`;
      `\t y. (min (&1) (&(SUC n) * d) - min (&1) (&n * d)) %%
             (cc:real->real^N->real^K^K) t y`;
      `(min (&1) (&(SUC n) * d) - min (&1) (&n * d)) * A`; `t1:real`] PDE_CONT_STEP) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PDE_TCOEFF_MONO THEN EXISTS_TAC `tmax:real` THEN CONJ_TAC THENL
         [MATCH_MP_TAC PDE_TCOEFF_HOM THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `t2 < tmax` THEN REAL_ARITH_TAC];
        MATCH_MP_TAC PDE_TBND_MONO THEN EXISTS_TAC `tmax:real` THEN CONJ_TAC THENL
         [MATCH_MP_TAC PDE_TBND_PERT THEN EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `t2 < tmax` THEN REAL_ARITH_TAC];
        MAP_EVERY X_GEN_TAC [`t:real`; `x:real^N`] THEN STRIP_TAC THEN
        REWRITE_TAC[VECTORIZE_CMUL; NORM_MUL] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `t1 < t2` THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[PDE_HOM_ADD] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  X_CHOOSE_TAC `M:num` (SPEC `inv d` REAL_ARCH_SIMPLE) THEN
  SUBGOAL_THEN `min (&1) (&M * d) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `min (&1) x = &1 <=> &1 <= x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv d * d` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REMOVE_THEN "IND" (MP_TAC o SPEC `M:num`) THEN ASM_REWRITE_TAC[MATRIX_CMUL_LID] THEN
  SUBGOAL_THEN `!X:real^N^N. mat 1 + (X - mat 1) = X` (fun th -> REWRITE_TAC[th; ETA_AX]) THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
  REWRITE_TAC[VECTORIZE_ADD; VECTORIZE_SUB] THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* Patching the solutions on [0,t1), t1 < tmax, into one on [0,tmax)         *)
(* (uniqueness on overlaps), and M4: PDE_TORUS_LIN_HOLDS.                    *)
(* ========================================================================= *)

let PDE_TSOL_MONO = prove
 (`!tmax t1 (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc f u0
    (u:real->real^N->real^K).
     pde_tsol tmax aa bb cc f u0 u /\ t1 <= tmax ==> pde_tsol t1 aa bb cc f u0 u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tsol] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `tmax:real` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= t`; `t < t1`; `t1 <= tmax`] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < t`; `t < t1`; `t1 <= tmax`] THEN REAL_ARITH_TAC]);;

(* The smooth extension of a solution, in the form used for gluing. *)

let PDE_TSOL_EXT = prove
 (`!t1 (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc f u0
    (u:real->real^N->real^K).
     pde_tsol t1 aa bb cc f u0 u
     ==> ?e FV. &0 < e /\
                smooth_map_on (interval(lift(&0 - e),lift t1) PCROSS (:real^N)) FV /\
                !w. &0 <= drop(fstcart w) /\ drop(fstcart w) < t1
                    ==> FV w = u (drop(fstcart w)) (sndcart w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_tsol; pde_upto; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FV:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) (K ALL_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `FV:real^(1,N)finite_sum->real^K`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`drop(fstcart(w:real^(1,N)finite_sum))`;
                                `sndcart(w:real^(1,N)finite_sum)`]) THEN
  ASM_REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND]);;

(* Uniqueness on overlaps. *)

let PDE_PATCH_UNIQ = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc f u0
    (S:real->real->real^N->real^K).
     pde_tcoeff tmax lam aa bb cc /\
     (!t1. &0 < t1 /\ t1 < tmax ==> pde_tsol t1 aa bb cc f u0 (S t1))
     ==> !t1 t2 t y. &0 < t1 /\ t1 < tmax /\ &0 < t2 /\ t2 < tmax /\
                     &0 <= t /\ t < t1 /\ t < t2
                     ==> S t1 t y = S t2 t y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`min t1 t2`; `lam:real`; `aa:real->real^N->real^N^N`;
                 `bb:real->real^N->num->real^K^K`; `cc:real->real^N->real^K^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`;
                 `(S:real->real->real^N->real^K) t1`; `(S:real->real->real^N->real^K) t2`]
                PDE_TORUS_UNIQUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_MIN];
      MATCH_MP_TAC PDE_TCOEFF_MONO THEN EXISTS_TAC `tmax:real` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `t1 < tmax` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC PDE_TSOL_MONO THEN EXISTS_TAC `t1:real` THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      MATCH_MP_TAC PDE_TSOL_MONO THEN EXISTS_TAC `t2:real` THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_MIN]]);;

(* Patching. *)

let PDE_TSOL_PATCH = prove
 (`!tmax lam (aa:real->real^N->real^N^N) (bb:real->real^N->num->real^K^K) cc f u0.
     &0 < tmax /\ pde_tcoeff tmax lam aa bb cc /\
     (!t1. &0 < t1 /\ t1 < tmax ==> ?u. pde_tsol t1 aa bb cc f u0 u)
     ==> ?u. pde_tsol tmax aa bb cc f u0 u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?S:real->real->real^N->real^K.
      !t1. &0 < t1 /\ t1 < tmax ==> pde_tsol t1 aa bb cc f u0 (S t1)`
  (X_CHOOSE_THEN `S:real->real->real^N->real^K` (LABEL_TAC "SOL")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tmax:real`; `lam:real`; `aa:real->real^N->real^N^N`;
                 `bb:real->real^N->num->real^K^K`; `cc:real->real^N->real^K^K`;
                 `f:real->real^N->real^K`; `u0:real^N->real^K`;
                 `S:real->real->real^N->real^K`] PDE_PATCH_UNIQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "UNQ") THEN
  SUBGOAL_THEN
   `!T1 t y. &0 < T1 /\ T1 < tmax /\ &0 <= t /\ t < T1
             ==> (S:real->real->real^N->real^K) ((t + tmax) / &2) t y = S T1 t y`
  (LABEL_TAC "AGR") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "UNQ" MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < T1`; `T1 < tmax`; `&0 <= t`; `t < T1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t < tmax
        ==> pde_tsol ((t + tmax) / &2) aa bb cc f u0
                     ((S:real->real->real^N->real^K) ((t + tmax) / &2))`
  (LABEL_TAC "SOLT") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "SOL" MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= t`; `t < tmax`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tmax / &2`; `aa:real->real^N->real^N^N`; `bb:real->real^N->num->real^K^K`;
                 `cc:real->real^N->real^K^K`; `f:real->real^N->real^K`; `u0:real^N->real^K`;
                 `(S:real->real->real^N->real^K) (tmax / &2)`] PDE_TSOL_EXT) THEN
  ANTS_TAC THENL
   [USE_THEN "SOL" MATCH_MP_TAC THEN UNDISCH_TAC `&0 < tmax` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `F0:real^(1,N)finite_sum->real^K`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F0")))))] THEN
  EXISTS_TAC `\t y. (S:real->real->real^N->real^K) ((t + tmax) / &2) t y` THEN
  REWRITE_TAC[pde_tsol] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pde_upto; IN_UNIV] THEN
    MAP_EVERY EXISTS_TAC
     [`e0:real`;
      `\z. if drop(fstcart z) < tmax / &2 then (F0:real^(1,N)finite_sum->real^K) z
           else (S:real->real->real^N->real^K) ((drop(fstcart z) + tmax) / &2)
                  (drop(fstcart z)) (sndcart z)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "F0" (MP_TAC o SPEC `pastecart (lift t) (y:real^N)`) THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "AGR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < tmax` THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    X_GEN_TAC `z:real^(1,N)finite_sum` THEN REWRITE_TAC[PDE_IN_SLAB; IN_UNIV] THEN STRIP_TAC THEN
    ASM_CASES_TAC `drop(fstcart(z:real^(1,N)finite_sum)) < tmax / &2` THENL
     [EXISTS_TAC `interval(lift(&0 - e0),lift(tmax / &2)) PCROSS (:real^N)` THEN
      ASM_REWRITE_TAC[PDE_IN_SLAB; IN_UNIV] THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `F0:real^(1,N)finite_sum->real^K` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN
      REWRITE_TAC[PDE_IN_SLAB; IN_UNIV] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(drop(fstcart(z:real^(1,N)finite_sum)) + tmax) / &2`;
                   `aa:real->real^N->real^N^N`; `bb:real->real^N->num->real^K^K`;
                   `cc:real->real^N->real^K^K`; `f:real->real^N->real^K`; `u0:real^N->real^K`;
                   `(S:real->real->real^N->real^K)
                      ((drop(fstcart(z:real^(1,N)finite_sum)) + tmax) / &2)`]
                  PDE_TSOL_EXT) THEN
    ANTS_TAC THENL
     [USE_THEN "SOL" MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [`drop(fstcart(z:real^(1,N)finite_sum)) < tmax`;
                             `~(drop(fstcart(z:real^(1,N)finite_sum)) < tmax / &2)`;
                             `&0 < tmax`] THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `F1:real^(1,N)finite_sum->real^K`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F1")))))] THEN
    EXISTS_TAC `interval(lift(tmax / &4),
                         lift((drop(fstcart(z:real^(1,N)finite_sum)) + tmax) / &2)) PCROSS
                (:real^N)` THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
     [REWRITE_TAC[PDE_IN_SLAB; IN_UNIV] THEN
      MAP_EVERY UNDISCH_TAC [`drop(fstcart(z:real^(1,N)finite_sum)) < tmax`;
                             `~(drop(fstcart(z:real^(1,N)finite_sum)) < tmax / &2)`;
                             `&0 < tmax`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `F1:real^(1,N)finite_sum->real^K` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(&0 - e1),
                           lift((drop(fstcart(z:real^(1,N)finite_sum)) + tmax) / &2)) PCROSS
                  (:real^N)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < e1`; `&0 < tmax`] THEN REAL_ARITH_TAC] THEN
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN REWRITE_TAC[PDE_IN_SLAB; IN_UNIV] THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "F1" (MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`tmax / &4 < drop(fstcart(w:real^(1,N)finite_sum))`;
                             `&0 < tmax`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THENL
     [USE_THEN "F0" (MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`tmax / &4 < drop(fstcart(w:real^(1,N)finite_sum))`;
                               `&0 < tmax`] THEN REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "UNQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`tmax / &4 < drop(fstcart(w:real^(1,N)finite_sum))`;
                             `drop(fstcart(z:real^(1,N)finite_sum)) < tmax`;
                             `~(drop(fstcart(z:real^(1,N)finite_sum)) < tmax / &2)`;
                             `&0 < tmax`] THEN REAL_ARITH_TAC;
      CONV_TAC SYM_CONV THEN USE_THEN "AGR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`tmax / &4 < drop(fstcart(w:real^(1,N)finite_sum))`;
                             `drop(fstcart(z:real^(1,N)finite_sum)) < tmax`;
                             `~(drop(fstcart(z:real^(1,N)finite_sum)) < tmax / &2)`;
                             `&0 < tmax`] THEN REAL_ARITH_TAC];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
    USE_THEN "SOLT" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[pde_tsol]] THEN
    STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= t`; `t < tmax`] THEN REAL_ARITH_TAC;
    USE_THEN "SOLT" (MP_TAC o SPEC `&0`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; SIMP_TAC[pde_tsol]];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "SOLT" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; REWRITE_TAC[pde_tsol]] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `y:real^N`] o last o CONJUNCTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `t < tmax` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[PDE_LOP_LOP0; ETA_AX] THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\s. (S:real->real->real^N->real^K) ((t + tmax) / &2) (drop s) y` THEN
    EXISTS_TAC `min t ((tmax - t) / &2)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `t < tmax` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `r:real^1` THEN REWRITE_TAC[dist; NORM_1; DROP_SUB; LIFT_DROP] THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "AGR" MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < t`; `t < tmax`] THEN REAL_ARITH_TAC]);;

(* M4. *)

let PDE_TORUS_LIN_HOLDS = prove
 (`!(n:N->bool) (k:K->bool). PDE_TORUS_LIN_STATEMENT n k`,
  REWRITE_TAC[PDE_TORUS_LIN_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PDE_TSOL_PATCH THEN EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t1:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tmax:real`; `lam:real`; `aa:real->real^N->real^N^N`;
                 `bb:real->real^N->num->real^K^K`; `cc:real->real^N->real^K^K`; `t1:real`]
                PDE_CONT_METHOD) THEN
  ASM_REWRITE_TAC[pde_solvable] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PDE_UPTO_SUBINTERVAL THEN EXISTS_TAC `tmax:real` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

