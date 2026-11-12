(* ========================================================================= *)
(* pc_pde_rdt_limit: the Ricci-DeTurck existence, part 10.  The limit of the *)
(* frozen-coefficient iterates and the theorem PDE_RDT_FROM_MLIN: cutoffs    *)
(* for a given cover, the limit family (uniform convergence of all           *)
(* space-time jets), its ball properties, the fixed point of the step by the *)
(* contraction, hence a Ricci-DeTurck flow from g0 on a uniform interval.    *)
(* ========================================================================= *)

needs "src/pc_pde_rdt_st.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Admissible cutoffs for a GIVEN finite chart cover, vanishing              *)
(* off the pulled-back pieces: shrink the open cover by the inverse images   *)
(* of the interiors of the pieces (paracompact shrinking), then take smooth  *)
(* cutoffs (MFD_SMOOTH_CUTOFF), set to zero off the space.                   *)
(* ------------------------------------------------------------------------- *)

let RDT_MFD_SMOOTH_TOPSPACE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (f:A->real) g.
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(f x)) /\
     (!x. x IN topspace top ==> g x = f x)
     ==> mfd_smooth atlas (\x. lift(g x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o REWRITE_RULE[mfd_smooth] o
    check (fun th -> rdt_has_const "mfd_smooth" th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC TEXT_SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `(\x. lift((f:A->real) x)) o chart_inv (c:(A->bool)#(A->real^N))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let RDT_CUTOFFS_EXIST = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks
     ==> ?psi. pde_cutoffs (top,atlas) n0 cs psi /\
               !i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[pde_cover]) THEN
  ABBREV_TAC `W = \i. {x:A | x IN FST((cs:num->(A->bool)#(A->real^N)) i) /\
                             SND(cs i) x IN interior((ks:num->real^N->bool) i)}` THEN
  SUBGOAL_THEN
   `!i. i < n0 ==> open_in top ((W:num->A->bool) i) /\
                   W i SUBSET FST((cs:num->(A->bool)#(A->real^N)) i) /\
                   W i SUBSET IMAGE (chart_inv (cs i)) ((ks:num->real^N->bool) i) /\
                   W i = IMAGE (chart_inv (cs i)) (interior(ks i))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "W" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `interior((ks:num->real^N->bool) i) SUBSET
                  IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`
    ASSUME_TAC THENL [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDM_CHART_PREIMAGE_OPEN THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_SIMP_TAC[OPEN_INTERIOR];
      SET_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      EXISTS_TAC `SND((cs:num->(A->bool)#(A->real^N)) i) x` THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `x:A` THEN EQ_TAC THENL
       [STRIP_TAC THEN EXISTS_TAC `SND((cs:num->(A->bool)#(A->real^N)) i) x` THEN
        ASM_SIMP_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(y:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`
        ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `{(W:num->A->bool) i | i < n0}`]
    PARACOMPACT_HAUSDORFF_INDEXED_SHRINKING) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_PARACOMPACT_SPACE] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN
       `{(W:num->A->bool) i | i < n0} =
        {IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) i)) (interior((ks:num->real^N->bool) i)) |
         i < n0}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
        REWRITE_TAC[pde_cover] THEN MESON_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:(A->bool)->(A->bool)` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. i < n0 ==> open_in top ((v:(A->bool)->(A->bool)) ((W:num->A->bool) i)) /\
                   top closure_of (v (W i)) SUBSET W i`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `(W:num->A->bool) i` o check (fun th ->
      rdt_has_const "closure_of" th && is_forall(concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n0
        ==> ?(chi:A->real) V L. mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift(chi x)) /\
                      (!x. &0 <= chi x /\ chi x <= &1) /\
                      open_in top V /\
                      top closure_of ((v:(A->bool)->(A->bool)) ((W:num->A->bool) i)) SUBSET V /\
                      (!x. x IN V ==> chi x = &1) /\
                      compact_in top L /\ L SUBSET W i /\
                      (!x:A. x IN topspace top DIFF L ==> chi x = &0)`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC MFD_SMOOTH_CUTOFF THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:num->A->real` (X_CHOOSE_THEN `V:num->A->bool`
    (X_CHOOSE_THEN `L:num->A->bool` (LABEL_TAC "cut")))) THEN
  EXISTS_TAC `\i (x:A). if x IN topspace top then (chi:num->A->real) i x else &0` THEN
  REWRITE_TAC[pde_cutoffs] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cut" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC RDT_MFD_SMOOTH_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `(chi:num->A->real) i`] THEN
      ASM_SIMP_TAC[];
      GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS];
      EXISTS_TAC `(L:num->A->bool) i` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?i. i < n0 /\ (x:A) IN (v:(A->bool)->(A->bool)) ((W:num->A->bool) i)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS (IMAGE (v:(A->bool)->(A->bool)) {(W:num->A->bool) i | i < n0}) =
                   topspace top` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE; EXISTS_IN_GSPEC] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "cut" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `(V:num->A->bool) i`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(x:A) IN top closure_of ((v:(A->bool)->(A->bool)) ((W:num->A->bool) i))`
      MP_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s t (x:A). s SUBSET t /\ x IN s ==> x IN t`) THEN
        EXISTS_TAC `(v:(A->bool)->(A->bool)) ((W:num->A->bool) i)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_SIMP_TAC[];
        ASM SET_TAC[]];
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:A) IN topspace top` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ASM_SIMP_TAC[]]];
    MAP_EVERY X_GEN_TAC [`i:num`; `x:A`] THEN STRIP_TAC THEN
    USE_THEN "cut" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(x:A) IN (L:num->A->bool) i` ASSUME_TAC THENL
     [UNDISCH_TAC `~((if (x:A) IN topspace top then (chi:num->A->real) i x else &0) = &0)` THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[IN_DIFF];
      ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* A real lemma, and a smooth tensor with vanishing level-0 norm vanishes on *)
(* the space (interpolation gives vanishing norms at all levels, the Sobolev *)
(* bound gives vanishing chart values on the pieces, and the pieces cover    *)
(* the space).                                                               *)
(* ------------------------------------------------------------------------- *)

let RDT_LE_ALL_DIV = prove
 (`!y c. &0 <= c /\ (!e. &0 < e ==> y <= c / e) ==> y <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&2 * (c + &1) / y`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD
    `&0 < y /\ &0 <= c ==> c / (&2 * (c + &1) / y) = (c * y) / (&2 * (c + &1))`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= c ==> &0 < &2 * (c + &1)`] THEN
  MP_TAC(SPECL [`c:real`; `y:real`] REAL_LE_MUL) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ASM_REAL_ARITH_TAC);;

let RDT_MNORM2_ZERO = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi (w:A->real^N^N).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     pde_tensor_smooth atlas w /\ pde_mnorm2 atlas n0 cs psi 0 w = &0
     ==> !x. x IN topspace top ==> w x = mat 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. pde_mnorm2 atlas n0 cs psi j (w:A->real^N^N) = &0` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC RDT_LE_ALL_DIV THEN
    EXISTS_TAC `&(dimindex(:N)) * pde_mnorm2 atlas n0 cs psi (j + 2) (w:A->real^N^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `w:A->real^N^N`; `j:num`; `e:real`] RDT_MNORM2_INTERP) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; real_div; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `0`] PDE_MNORM_SOBOLEV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
  SUBGOAL_THEN
   `!i y. i < n0 /\ y IN (ks:num->real^N->bool) i
          ==> metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (w:A->real^N^N) y = mat 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VECTORIZE_EQ_0; GSYM NORM_EQ_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:A->real^N^N`; `i:num`; `[]:num list`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[PDE_INDEX_LISTS_NIL; iterated_partial; o_THM; REAL_MUL_RZERO] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `norm((vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (w:A->real^N^N) y)) pow 2 =
      &0`
    MP_TAC THENL
     [ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_POW_2]; SIMP_TAC[REAL_POW_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [pde_cover] o
    check (fun th -> rdt_has_const "pde_cover" th)) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A` o REWRITE_RULE[EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:A->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\
    (y:real^N) IN (ks:num->real^N->bool) i /\ y IN IMAGE (SND(cs i)) (FST(cs i))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC PDE_ME_METRIC_LOCAL_EQ_0 THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `(cs:num->(A->bool)#(A->real^N)) i`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The iterates rdt_iter from g0 on [a,a+tau): they stay in the              *)
(* ball and solve the steps, contract at level 0, are bounded and Cauchy at  *)
(* every level, and their space jets are bounded and Cauchy on the pieces.   *)
(* ------------------------------------------------------------------------- *)

let RDT_SQ_LE_IMP = prove
 (`!x A. x pow 2 <= A ==> x <= A + &1`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `x - &1 / &2` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC);;

let RDT_LIM_ITER_FACTS = prove
 (`!(u:A->bool) (n:N->bool) (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
    n0 cs ks psi s B K tau (g0:A->real^N^N) a.
     PDE_MLIN_STATEMENT u n /\
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s /\ &0 <= B /\ &0 < K /\ &0 < tau /\
     riemannian_metric atlas g0 /\ pde_cbound atlas n0 cs ks (s + 3) B g0 /\
     pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (\t. g0) /\
     (!g v. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g /\
            pde_rdt_step (top,atlas) a (a + tau) g0 g v
            ==> pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 v) /\
     (!g g' v v' D.
        pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g /\
        pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g' /\
        pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 v' /\
        pde_rdt_step (top,atlas) a (a + tau) g0 g v /\
        pde_rdt_step (top,atlas) a (a + tau) g0 g' v' /\
        (!t. a <= t /\ t < a + tau
             ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g t x - g' t x) +
                 real_integral (real_interval[a,t])
                   (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g r x - g' r x)) <= D)
        ==> !t. a <= t /\ t < a + tau
                ==> pde_mnorm2 atlas n0 cs psi 0 (\x. v t x - v' t x) +
                    real_integral (real_interval[a,t])
                      (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. v r x - v' r x)) <= D / &2)
     ==> (!k. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0
                (rdt_iter top atlas a (a + tau) g0 k) /\
              pde_rdt_step (top,atlas) a (a + tau) g0 (rdt_iter top atlas a (a + tau) g0 k)
                (rdt_iter top atlas a (a + tau) g0 (SUC k))) /\
         rdt_iter top atlas a (a + tau) g0 0 = (\t. g0) /\
         (!j k t. a <= t /\ t < a + tau
                  ==> pde_mnorm2 atlas n0 cs psi 0
                        (\x. rdt_iter top atlas a (a + tau) g0 (j + k) t x -
                             rdt_iter top atlas a (a + tau) g0 k t x) +
                      real_integral (real_interval[a,t])
                        (\r. pde_mnorm2 atlas n0 cs psi 1
                               (\x. rdt_iter top atlas a (a + tau) g0 (j + k) r x -
                                    rdt_iter top atlas a (a + tau) g0 k r x))
                      <= (&4 * K * (&1 + tau)) / &2 pow k) /\
         (!l. ?M. !k t. a <= t /\ t < a + tau
                        ==> pde_mnorm2 atlas n0 cs psi l (rdt_iter top atlas a (a + tau) g0 k t)
                            <= M) /\
         (!l e. &0 < e
                ==> ?k0. !m k t. k0 <= k /\ k <= m /\ a <= t /\ t < a + tau
                                 ==> pde_mnorm2 atlas n0 cs psi l
                                       (\x. rdt_iter top atlas a (a + tau) g0 m t x -
                                            rdt_iter top atlas a (a + tau) g0 k t x) <= e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `g = rdt_iter (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a (a + tau)
                    (g0:A->real^N^N)` THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:N->bool`] RDT_ITER_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
    `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`; `s:num`;
    `K:real`; `tau:real`; `g0:A->real^N^N`; `a:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(g:num->real->A->real^N^N) 0 = (\t. g0)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[rdt_iter]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!k t. a <= t /\ t < a + tau
           ==> pde_tensor_smooth atlas ((g:num->real->A->real^N^N) k t)) /\
    (!k. pde_tfam_from atlas a (a + tau) (g k))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THENL [STRIP_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && rdt_has_const "pde_rdt_step" th)) THEN
    REWRITE_TAC[pde_rdt_ball] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j k t. a <= t /\ t < a + tau
            ==> pde_mnorm2 atlas n0 cs psi 0
                  (\x. (g:num->real->A->real^N^N) (j + k) t x - g k t x) +
                real_integral (real_interval[a,t])
                  (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g (j + k) r x - g k r x))
                <= (&4 * K * (&1 + tau)) / &2 pow k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_ITER_CAUCHY0 THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`; `s:num`; `g0:A->real^N^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. ?M. !k t. a <= t /\ t < a + tau
                  ==> pde_mnorm2 atlas n0 cs psi l ((g:num->real->A->real^N^N) k t) <= M`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_ITER_ALL_LEVELS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`; `s:num`; `B:real`;
                          `K:real`; `g0:A->real^N^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RDT_ITER_CAUCHY_LEVELS THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`;
                        `&4 * K * (&1 + tau)`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `!x y e. &0 <= y /\ x + y <= e ==> x <= e`) THEN
  EXISTS_TAC `real_integral (real_interval[a,t])
                (\r. pde_mnorm2 atlas n0 cs psi 1
                       (\x. (g:num->real->A->real^N^N) (j + k) r x - g k r x))` THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `a:real`; `a + tau`; `(g:num->real->A->real^N^N) (j + k)`;
                 `(g:num->real->A->real^N^N) k`; `t:real`] RDT_DQ_NONNEG) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Uniform Cauchy property of all space-time jets of the iterates in the     *)
(* charts of the cover, on (a,t1] x ks i for t1 < a + tau.                   *)
(* ------------------------------------------------------------------------- *)

let RDT_LIM_ST_CAUCHY = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s K tau
    (g0:A->real^N^N) a (g:num->real->A->real^N^N).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     &0 < K /\ &0 < tau /\ riemannian_metric atlas g0 /\
     (!k. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (g k) /\
          pde_rdt_step (top,atlas) a (a + tau) g0 (g k) (g (SUC k))) /\
     g 0 = (\t. g0) /\
     (!j k t. a <= t /\ t < a + tau
              ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g (j + k) t x - g k t x) +
                  real_integral (real_interval[a,t])
                    (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g (j + k) r x - g k r x))
                  <= (&4 * K * (&1 + tau)) / &2 pow k) /\
     (!l. ?M. !k t. a <= t /\ t < a + tau ==> pde_mnorm2 atlas n0 cs psi l (g k t) <= M)
     ==> !i l t1 e. i < n0 /\ ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l /\
                    t1 < a + tau /\ &0 < e
                    ==> ?k0. !m k t y. k0 <= k /\ k <= m /\ a < t /\ t <= t1 /\ y IN ks i
                                       ==> norm(iterated_partial l (rdt_strep atlas (cs i) (g m))
                                                  (pastecart (lift t) y) -
                                                iterated_partial l (rdt_strep atlas (cs i) (g k))
                                                  (pastecart (lift t) y)) <= e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "al" o check (fun th ->
    is_forall(concl th) && rdt_has_const "pde_mnorm2" th &&
    is_exists(snd(strip_forall(concl th))))) THEN
  FIRST_X_ASSUM(LABEL_TAC "dq" o check (fun th ->
    is_forall(concl th) && rdt_has_const "real_integral" th)) THEN
  SUBGOAL_THEN
   `(!k. pde_rdt_step (top,atlas) a (a + tau) g0 ((g:num->real->A->real^N^N) k) (g (SUC k))) /\
    (!k. pde_tfam_from atlas a (a + tau) (g k)) /\
    (!k t. a <= t /\ t < a + tau
           ==> riemannian_metric atlas (g k t) /\ pde_cbound atlas n0 cs ks 0 K (g k t) /\
               pde_tensor_smooth atlas (g k t))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL [ALL_TAC; ALL_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && rdt_has_const "pde_rdt_ball" th)) THEN
    REWRITE_TAC[pde_rdt_ball] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j k t. a <= t /\ t < a + tau
            ==> pde_mnorm2 atlas n0 cs psi 0
                  (\x. (g:num->real->A->real^N^N) (j + k) t x - g k t x)
                <= (&4 * K * (&1 + tau)) / &2 pow k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!x y e. &0 <= y /\ x + y <= e ==> x <= e`) THEN
    EXISTS_TAC `real_integral (real_interval[a,t])
                  (\r. pde_mnorm2 atlas n0 cs psi 1
                         (\x. (g:num->real->A->real^N^N) (j + k) r x - g k r x))` THEN
    USE_THEN "dq" (fun th -> ASM_SIMP_TAC[th]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `a:real`; `a + tau`; `(g:num->real->A->real^N^N) (j + k)`;
                   `(g:num->real->A->real^N^N) k`; `t:real`] RDT_DQ_NONNEG) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\ compact((ks:num->real^N->bool) i) /\
    ks i SUBSET IMAGE (SND(cs i)) (FST(cs i))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the space jets on ks i are bounded *)
  SUBGOAL_THEN
   `!q. ALL (\j. 1 <= j /\ j <= dimindex(:N)) q
        ==> ?M. !k t y. a <= t /\ t < a + tau /\ y IN (ks:num->real^N->bool) i
                        ==> norm(iterated_partial q
                                   ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                    metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                      ((g:num->real->A->real^N^N) k t)) y) <= M`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:num list` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `LENGTH(q:num list)`] PDE_MNORM_SOBOLEV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
    USE_THEN "al" (X_CHOOSE_TAC `M:real` o SPEC `LENGTH(q:num list) + dimindex(:N)`) THEN
    EXISTS_TAC `abs C * abs M + &1` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RDT_SQ_LE_IMP THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * pde_mnorm2 atlas n0 cs psi (LENGTH(q:num list) + dimindex(:N))
                      ((g:num->real->A->real^N^N) k t)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> rdt_has_const "pde_index_lists" th)) THEN
      ASM_SIMP_TAC[pde_index_lists; IN_ELIM_THM; LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= pde_mnorm2 atlas n0 cs psi (LENGTH(q:num list) + dimindex(:N))
              ((g:num->real->A->real^N^N) k t) /\
      pde_mnorm2 atlas n0 cs psi (LENGTH(q:num list) + dimindex(:N)) (g k t) <= M`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_SIMP_TAC[];
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs C * pde_mnorm2 atlas n0 cs psi (LENGTH(q:num list) + dimindex(:N))
                          ((g:num->real->A->real^N^N) k t)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `a:real`; `a + tau`; `g0:A->real^N^N`;
                 `g:num->real->A->real^N^N`; `(ks:num->real^N->bool) i`] RDT_ITER_ST_CAUCHY) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN EXISTS_TAC `K:real` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `pde_cbound atlas n0 cs ks 0 K ((g:num->real->A->real^N^N) k t)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[pde_cbound] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`[]:num list`; `y:real^N`]) ASSUME_TAC) THEN
    ASM_SIMP_TAC[PDE_INDEX_LISTS_NIL; iterated_partial; o_THM];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `a:real`; `a + tau`; `&4 * K * (&1 + tau)`; `g:num->real->A->real^N^N`]
      RDT_ITER_CAUCHY_JETS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_ARITH `&0 <= &4`;
                   REAL_ARITH `&0 < tau ==> &0 <= &1 + tau`];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `l':num list`; `e':real`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num list`; `t1:real`; `e:real`]) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The limit family of the iterates (PDM_TFAM_LIMIT): a family               *)
(* smooth up to a in every chart, the pointwise limit of the iterates.       *)
(* ------------------------------------------------------------------------- *)

let RDT_LIM_EXISTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s K tau
    (g0:A->real^N^N) a (g:num->real->A->real^N^N).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     &0 < K /\ &0 < tau /\ riemannian_metric atlas g0 /\
     (!k. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (g k) /\
          pde_rdt_step (top,atlas) a (a + tau) g0 (g k) (g (SUC k))) /\
     g 0 = (\t. g0) /\
     (!j k t. a <= t /\ t < a + tau
              ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g (j + k) t x - g k t x) +
                  real_integral (real_interval[a,t])
                    (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g (j + k) r x - g k r x))
                  <= (&4 * K * (&1 + tau)) / &2 pow k) /\
     (!l. ?M. !k t. a <= t /\ t < a + tau ==> pde_mnorm2 atlas n0 cs psi l (g k t) <= M)
     ==> ?gb. pde_tfam_from atlas a (a + tau) gb /\
              (!t x. ~(a <= t /\ t < a + tau /\ x IN topspace top) ==> gb t x = mat 0) /\
              (!t x. a <= t /\ t < a + tau /\ x IN topspace top
                     ==> ((\k. (vectorize:real^N^N->real^(N,N)finite_prod) (g k t x)) -->
                          vectorize(gb t x)) sequentially)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> LABEL_TAC "stc" (MATCH_MP RDT_LIM_ST_CAUCHY th) THEN
                       STRIP_ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `a:real`; `a + tau`;
                 `g:num->real->A->real^N^N`] PDM_TFAM_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_ADDR] THEN CONJ_TAC THENL
     [GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
        is_forall(concl th) && rdt_has_const "pde_rdt_ball" th)) THEN
      SIMP_TAC[pde_rdt_ball];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `l:num list`; `t1:real`] THEN STRIP_TAC THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    USE_THEN "stc" (MP_TAC o SPECL [`i:num`; `l:num list`; `t1:real`; `d / &2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN EXISTS_TAC `k0:num` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `p:num`; `t:real`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN (ks:num->real^N->bool) i` ASSUME_TAC THENL
     [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[GSYM RDT_STREP_ALT] THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= d / &2 /\ &0 < d ==> x < d`) THEN ASM_REWRITE_TAC[] THEN
    DISJ_CASES_TAC(ARITH_RULE `p <= m \/ m <= p:num`) THENL
     [USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[NORM_SUB] THEN USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gb:real->A->real^N^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gb:real->A->real^N^N` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Limits of pointwise bounds of matrices, the chart-norm limit              *)
(* of the iterates at a fixed time, and the uniform convergence of the       *)
(* iterates to the limit family in every chart norm.                         *)
(* ------------------------------------------------------------------------- *)

let RDT_LIM_ELLIPTIC = prove
 (`!(G:num->real^N^N) G0 B.
     ((\k. (vectorize:real^N^N->real^(N,N)finite_prod) (G k)) --> vectorize G0) sequentially /\
     (!k. norm((vectorize:real^N^N->real^(N,N)finite_prod) (G k)) <= B /\ transp(G k) = G k /\
          !v. norm v pow 2 <= B * (v dot (G k ** v)))
     ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) G0) <= B /\ transp G0 = G0 /\
         !v. norm v pow 2 <= B * (v dot (G0 ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`sequentially`;
      `\k. (vectorize:real^N^N->real^(N,N)finite_prod) ((G:num->real^N^N) k)`;
      `(vectorize:real^N^N->real^(N,N)finite_prod) G0`; `B:real`] LIM_NORM_UBOUND) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\k. (vectorize:real^N^N->real^(N,N)finite_prod) ((G:num->real^N^N) k)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\k. (vectorize:real^N^N->real^(N,N)finite_prod) ((G:num->real^N^N) k)) =
      (\k. vectorize(transp(matrify(vectorize(G k)))))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[MATRIFY_VECTORIZE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) (transp G0) =
      vectorize(transp(matrify(vectorize G0)))`
    SUBST1_TAC THENL [REWRITE_TAC[MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`sequentially`;
      `\w:real^(N,N)finite_prod. (vectorize:real^N^N->real^(N,N)finite_prod) (transp(matrify w))`;
      `\k. (vectorize:real^N^N->real^(N,N)finite_prod) ((G:num->real^N^N) k)`;
      `(vectorize:real^N^N->real^(N,N)finite_prod) G0`] LIM_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL;
                VECTORIZE_ADD; VECTORIZE_CMUL];
    X_GEN_TAC `v:real^N` THEN
    SUBGOAL_THEN `!x. ((\a. (G:num->real^N^N) a ** x) --> G0 ** x) sequentially` ASSUME_TAC
    THENL [ASM_REWRITE_TAC[LIM_MATRIX_VECTORIZE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `((\k. lift(B * (v dot ((G:num->real^N^N) k ** v)))) --> lift(B * (v dot (G0 ** v))))
      sequentially`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`sequentially`; `\w:real^N. lift(B * (v dot w))`;
                     `\k. (G:num->real^N^N) k ** v`; `(G0:real^N^N) ** v`] LIM_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[linear; DOT_RADD; DOT_RMUL] THEN
      REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL] THEN
      CONJ_TAC THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`sequentially`; `\k. lift(B * (v dot ((G:num->real^N^N) k ** v)))`;
                   `lift(B * (v dot ((G0:real^N^N) ** v)))`; `norm(v:real^N) pow 2`; `1`]
      LIM_COMPONENT_LBOUND) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY; DIMINDEX_1; LE_REFL;
                    GSYM drop; LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let RDT_LIM_AT_T = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi
    (vv:num->A->real^N^N) v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     (!k. pde_tensor_smooth atlas (vv k)) /\
     (!x. x IN topspace top
          ==> ((\k. (vectorize:real^N^N->real^(N,N)finite_prod) (vv k x)) --> vectorize(v x))
              sequentially) /\
     (!l e. &0 < e ==> ?k0. !m k. k0 <= k /\ k <= m
                                  ==> pde_mnorm2 atlas n0 cs psi l (\x. vv m x - vv k x) <= e)
     ==> !l. ((\k. pde_mnorm2 atlas n0 cs psi l (\x. vv k x - v x)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "cl" o check (fun th ->
    is_forall(concl th) && rdt_has_const "pde_mnorm2" th)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `vv:num->A->real^N^N`] PDM_MNORM_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`q:num`; `d:real`] THEN DISCH_TAC THEN
    USE_THEN "cl" (MP_TAC o SPECL [`q:num`; `d / &5`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "n0")) THEN EXISTS_TAC `N0:num` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `p:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `q:num`; `\x. (vv:num->A->real^N^N) m x - vv N0 x`;
                   `\x. (vv:num->A->real^N^N) p x - vv N0 x`] RDT_MNORM2_SUB_LE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN CONJ_TAC THEN
      MATCH_MP_TAC MFD_TENSOR2_SMOOTH_SUB THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[GSYM PDM_TENSOR_SMOOTH_EQ; ETA_AX];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\x. ((vv:num->A->real^N^N) m x - vv N0 x) - (vv p x - vv N0 x)) =
                  (\x. vv m x - vv p x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATRIX_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= d / &5 /\ b <= d / &5 /\ &0 < d
                             ==> x <= &2 * a + &2 * b ==> x < d`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "n0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> (v:A->real^N^N) x = w x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\k. (vectorize:real^N^N->real^(N,N)finite_prod) ((vv:num->A->real^N^N) k x)` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY];
    ALL_TAC] THEN
  X_GEN_TAC `l:num` THEN
  SUBGOAL_THEN
   `(\k. pde_mnorm2 atlas n0 cs psi l (\x. (vv:num->A->real^N^N) k x - v x)) =
    (\k. pde_mnorm2 atlas n0 cs psi l (\x. vv k x - w x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC RDT_MNORM2_CONG THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN MESON_TAC[];
    ASM_REWRITE_TAC[]]);;

let RDT_LIM_MNORM2_CONV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi a b
    (g:num->real->A->real^N^N) gb.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     (!k t. a <= t /\ t < b ==> pde_tensor_smooth atlas (g k t)) /\
     (!t. a <= t /\ t < b ==> pde_tensor_smooth atlas (gb t)) /\
     (!t x. a <= t /\ t < b /\ x IN topspace top
            ==> ((\k. (vectorize:real^N^N->real^(N,N)finite_prod) (g k t x)) -->
                 vectorize(gb t x)) sequentially) /\
     (!l e. &0 < e ==> ?k0. !m k t. k0 <= k /\ k <= m /\ a <= t /\ t < b
                                    ==> pde_mnorm2 atlas n0 cs psi l (\x. g m t x - g k t x) <= e)
     ==> (!t l. a <= t /\ t < b
                ==> ((\k. pde_mnorm2 atlas n0 cs psi l (\x. g k t x - gb t x)) ---> &0)
                    sequentially) /\
         (!l e. &0 < e ==> ?k0. !k t. k0 <= k /\ a <= t /\ t < b
                                      ==> pde_mnorm2 atlas n0 cs psi l (\x. gb t x - g k t x)
                                          <= e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "cl" o check (fun th ->
    is_forall(concl th) && rdt_has_const "pde_mnorm2" th)) THEN
  SUBGOAL_THEN
   `!t l. a <= t /\ t < b
          ==> ((\k. pde_mnorm2 atlas n0 cs psi l
                      (\x. (g:num->real->A->real^N^N) k t x - gb t x)) ---> &0) sequentially`
  (LABEL_TAC "at") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `\k. (g:num->real->A->real^N^N) k t`; `(gb:real->A->real^N^N) t`]
      RDT_LIM_AT_T) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`q:num`; `d:real`] THEN DISCH_TAC THEN
      USE_THEN "cl" (MP_TAC o SPECL [`q:num`; `d:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `k:num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`l:num`; `e:real`] THEN DISCH_TAC THEN
  USE_THEN "cl" (MP_TAC o SPECL [`l:num`; `e / &4`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN EXISTS_TAC `k0:num` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `t:real`] THEN STRIP_TAC THEN
  USE_THEN "at" (MP_TAC o SPECL [`t:real`; `l:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  ABBREV_TAC `m = MAX N k` THEN
  SUBGOAL_THEN `(N:num) <= m /\ (k:num) <= m` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `l:num`; `\x. (g:num->real->A->real^N^N) m t x - g k t x`;
                 `\x. (g:num->real->A->real^N^N) m t x - gb t x`] RDT_MNORM2_SUB_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN CONJ_TAC THEN
    MATCH_MP_TAC MFD_TENSOR2_SMOOTH_SUB THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[GSYM PDM_TENSOR_SMOOTH_EQ; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. ((g:num->real->A->real^N^N) m t x - g k t x) - (g m t x - gb t x)) =
                (\x. gb t x - g k t x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATRIX_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= e / &4 /\ abs b < e / &4 ==> x <= &2 * a + &2 * b ==> x <= e`) THEN
  CONJ_TAC THENL
   [USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The limit family is in the ball of radius 4K: it starts at                *)
(* g0, it is Riemannian with the pointwise bounds of radius K (limits of the *)
(* chart values on the pieces), and its level-s norm is at most 2K + 2K.     *)
(* ------------------------------------------------------------------------- *)

let RDT_LIM_RIEM_CBOUND = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks K
    (vv:num->A->real^N^N) v.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     mfd_tensor2_smooth atlas v /\ &0 < K /\
     (!k. riemannian_metric atlas (vv k) /\ pde_cbound atlas n0 cs ks 0 K (vv k)) /\
     (!x. x IN topspace top
          ==> ((\k. (vectorize:real^N^N->real^(N,N)finite_prod) (vv k x)) --> vectorize(v x))
              sequentially)
     ==> riemannian_metric atlas v /\ pde_cbound atlas n0 cs ks 0 K v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[pde_cover] o
    check (fun th -> rdt_has_const "pde_cover" th)) THEN
  FIRST_X_ASSUM(LABEL_TAC "pt" o check (fun th ->
    is_forall(concl th) && rdt_has_const "-->" th)) THEN
  SUBGOAL_THEN
   `!i y. i < n0 /\ y IN (ks:num->real^N->bool) i
          ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                     (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (v:A->real^N^N) y))
              <= K /\
              transp(metric_local atlas (cs i) v y) = metric_local atlas (cs i) v y /\
              !w. norm w pow 2 <= K * (w dot (metric_local atlas (cs i) v y ** w))`
  (LABEL_TAC "lim") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\
                  (y:real^N) IN IMAGE (SND(cs i)) (FST(cs i))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!k. norm((vectorize:real^N^N->real^(N,N)finite_prod)
                 (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                    ((vv:num->A->real^N^N) k) y)) <= K /\
          transp(metric_local atlas (cs i) (vv k) y) = metric_local atlas (cs i) (vv k) y /\
          !w. norm w pow 2 <= K * (w dot (metric_local atlas (cs i) (vv k) y ** w))`
    ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN
      SUBGOAL_THEN `riemannian_metric atlas ((vv:num->A->real^N^N) k) /\
                    pde_cbound atlas n0 cs ks 0 K (vv k)` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[riemannian_metric; metric_field; pde_cbound] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `(cs:num->(A->bool)#(A->real^N)) i`)
                                 (MP_TAC o SPEC `i:num`)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`[]:num list`; `y:real^N`]) ASSUME_TAC) THEN
      ASM_REWRITE_TAC[PDE_INDEX_LISTS_NIL; iterated_partial; o_THM] THEN DISCH_TAC THEN
      STRIP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC RDT_LIM_ELLIPTIC THEN
    EXISTS_TAC `\k. metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                      ((vv:num->A->real^N^N) k) y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDM_METRIC_LOCAL_LIM THEN
    USE_THEN "pt" MATCH_MP_TAC THEN
    ASM_MESON_TAC[PDM_CHART_INV_C; PDM_CHART_OPEN_C; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas (v:A->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_RIEM_FROM_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `n0:num`; `cs:num->(A->bool)#(A->real^N)`;
                          `ks:num->real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [pde_cover] o
        check (fun th -> rdt_has_const "pde_cover" th)) THEN
      DISCH_THEN(MP_TAC o SPEC `x:A` o REWRITE_RULE[EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
      ASM_REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\
        (y:real^N) IN (ks:num->real^N->bool) i /\ y IN IMAGE (SND(cs i)) (FST(cs i))`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(cs:num->(A->bool)#(A->real^N)) i`;
                     `\z:A. transp((v:A->real^N^N) z) - v z`;
                     `chart_inv ((cs:num->(A->bool)#(A->real^N)) i) (y:real^N)`]
        PDE_ME_METRIC_LOCAL_EQ_0) THEN
      REWRITE_TAC[MATRIX_SUB_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[METRIC_LOCAL_SUB; RDT_METRIC_LOCAL_TRANSP; MATRIX_SUB_REFL];
      MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`; `w:real^N`] THEN STRIP_TAC THEN
      USE_THEN "lim" (MP_TAC o SPECL [`i:num`; `y:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT2 o CONJUNCT2) THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `&0 < K * (w dot (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                          (v:A->real^N^N) y ** w))`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `norm(w:real^N) pow 2` THEN
        ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT];
        ASM_SIMP_TAC[REAL_LT_MUL_EQ]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pde_cbound] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LE; LENGTH_EQ_NIL] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[iterated_partial; o_THM] THEN
    USE_THEN "lim" (MP_TAC o SPECL [`i:num`; `y:real^N`]) THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "lim" (MP_TAC o SPECL [`i:num`; `y:real^N`]) THEN
    ASM_SIMP_TAC[]]);;

let RDT_LIM_BALL = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s K tau
    (g0:A->real^N^N) a (g:num->real->A->real^N^N) gb.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     &0 < K /\ &0 < tau /\
     (!k. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (g k)) /\
     pde_tfam_from atlas a (a + tau) gb /\
     (!t x. a <= t /\ t < a + tau /\ x IN topspace top
            ==> ((\k. (vectorize:real^N^N->real^(N,N)finite_prod) (g k t x)) -->
                 vectorize(gb t x)) sequentially) /\
     (!t l. a <= t /\ t < a + tau
            ==> ((\k. pde_mnorm2 atlas n0 cs psi l (\x. g k t x - gb t x)) ---> &0)
                sequentially)
     ==> pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau g0 gb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "at" o check (fun th ->
    is_forall(concl th) && rdt_has_const "pde_mnorm2" th)) THEN
  FIRST_X_ASSUM(LABEL_TAC "pt" o check (fun th ->
    is_forall(concl th) && rdt_has_const "-->" th)) THEN
  FIRST_X_ASSUM(LABEL_TAC "bl" o check (fun th ->
    is_forall(concl th) && rdt_has_const "pde_rdt_ball" th)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  SUBGOAL_THEN
   `!k t. a <= t /\ t < a + tau
          ==> riemannian_metric atlas ((g:num->real->A->real^N^N) k t) /\
              pde_cbound atlas n0 cs ks 0 K (g k t) /\
              pde_mnorm2 atlas n0 cs psi s (g k t) <= K /\
              pde_tensor_smooth atlas (g k t)`
  (LABEL_TAC "gk") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "bl" (MP_TAC o SPEC `k:num`) THEN
    REWRITE_TAC[pde_rdt_ball] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < a + tau ==> pde_tensor_smooth atlas ((gb:real->A->real^N^N) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `a + tau`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pde_rdt_ball] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\k. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((g:num->real->A->real^N^N) k a x)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [USE_THEN "pt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN
       `(\k. (vectorize:real^N^N->real^(N,N)finite_prod) ((g:num->real->A->real^N^N) k a x)) =
        (\k. vectorize((g0:A->real^N^N) x))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN AP_TERM_TAC THEN
        USE_THEN "bl" (MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[pde_rdt_ball] THEN
        STRIP_TAC THEN ASM_SIMP_TAC[];
        REWRITE_TAC[LIM_CONST]]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `riemannian_metric atlas ((gb:real->A->real^N^N) t) /\ pde_cbound atlas n0 cs ks 0 K (gb t)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_LIM_RIEM_CBOUND THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `\k. (g:num->real->A->real^N^N) k t`] THEN
    ASM_SIMP_TAC[GSYM PDM_TENSOR_SMOOTH_EQ] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN USE_THEN "pt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RDT_CBOUND_MONO THEN MAP_EVERY EXISTS_TAC [`0`; `K:real`] THEN
    ASM_REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "at" (MP_TAC o SPECL [`t:real`; `s:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `K:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (MP_TAC o SPEC `k:num`)) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_TAC THEN
  USE_THEN "gk" (MP_TAC o SPECL [`k:num`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `(g:num->real->A->real^N^N) k t`;
                 `\x. (g:num->real->A->real^N^N) k t x - gb t x`] RDT_MNORM2_SUB_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MATCH_MP_TAC MFD_TENSOR2_SMOOTH_SUB THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[GSYM PDM_TENSOR_SMOOTH_EQ; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_mnorm2 atlas n0 cs psi s
      (\x. (g:num->real->A->real^N^N) k t x - (\x. g k t x - gb t x) x) =
    pde_mnorm2 atlas n0 cs psi s (gb t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RDT_MNORM2_CONG THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATRIX_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `\x. (g:num->real->A->real^N^N) k t x - gb t x`; `s:num`] PDE_ME_MNORM2_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MATCH_MP_TAC MFD_TENSOR2_SMOOTH_SUB THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[GSYM PDM_TENSOR_SMOOTH_EQ; ETA_AX];
    ALL_TAC] THEN
  UNDISCH_TAC `abs(pde_mnorm2 atlas n0 cs psi s
                 (\x. (g:num->real->A->real^N^N) k t x - gb t x)) < K` THEN
  UNDISCH_TAC `pde_mnorm2 atlas n0 cs psi s ((g:num->real->A->real^N^N) k t) <= K` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The limit family is a fixed point of the step (contraction                *)
(* with radius 4K against the iterates).                                     *)
(* ------------------------------------------------------------------------- *)

let RDT_REAL_INTEGRAL_LE_CONST = prove
 (`!f a t e. a <= t /\ f real_integrable_on real_interval[a,t] /\
             (!r. a <= r /\ r <= t ==> f r <= e)
             ==> real_integral (real_interval[a,t]) f <= e * (t - a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[a,t]) (\r:real. e)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_SIMP_TAC[REAL_INTEGRABLE_CONST; IN_REAL_INTERVAL];
    ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LE_REFL]]);;

let RDT_LE_ALL_POS = prove
 (`!x. &0 <= x /\ (!e. &0 < e ==> x <= e) ==> x = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x / &2`) THEN ASM_REAL_ARITH_TAC);;

let RDT_LIM_FIXED = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s K tau
    (g0:A->real^N^N) a (g:num->real->A->real^N^N) gb v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     &0 < K /\ &0 < tau /\
     (!k. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (g k) /\
          pde_rdt_step (top,atlas) a (a + tau) g0 (g k) (g (SUC k))) /\
     pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau g0 gb /\
     pde_rdt_step (top,atlas) a (a + tau) g0 gb v /\
     (!l e. &0 < e ==> ?k0. !k t. k0 <= k /\ a <= t /\ t < a + tau
                                  ==> pde_mnorm2 atlas n0 cs psi l (\x. gb t x - g k t x) <= e) /\
     (!g g' v v' D.
        pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau g0 g /\
        pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau g0 g' /\
        pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau g0 v' /\
        pde_rdt_step (top,atlas) a (a + tau) g0 g v /\
        pde_rdt_step (top,atlas) a (a + tau) g0 g' v' /\
        (!t. a <= t /\ t < a + tau
             ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g t x - g' t x) +
                 real_integral (real_interval[a,t])
                   (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g r x - g' r x)) <= D)
        ==> !t. a <= t /\ t < a + tau
                ==> pde_mnorm2 atlas n0 cs psi 0 (\x. v t x - v' t x) +
                    real_integral (real_interval[a,t])
                      (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. v r x - v' r x)) <= D / &2)
     ==> !t x. a <= t /\ t < a + tau /\ x IN topspace top ==> v t x = gb t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "con" o check (fun th ->
    is_forall(concl th) && rdt_has_const "real_integral" th)) THEN
  FIRST_X_ASSUM(LABEL_TAC "uc" o check (fun th ->
    is_forall(concl th) && rdt_has_const "pde_mnorm2" th &&
    not(rdt_has_const "real_integral" th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "it" o check (fun th ->
    is_forall(concl th) && rdt_has_const "pde_rdt_step" th &&
    not(rdt_has_const "real_integral" th))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  SUBGOAL_THEN
   `pde_tfam_from atlas a (a + tau) (gb:real->A->real^N^N) /\
    pde_tfam_from atlas a (a + tau) (v:real->A->real^N^N) /\
    (!k. pde_tfam_from atlas a (a + tau) ((g:num->real->A->real^N^N) k))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau (g0:A->real^N^N) gb` THEN
      SIMP_TAC[pde_rdt_ball];
      UNDISCH_TAC `pde_rdt_step (top,atlas) a (a + tau) (g0:A->real^N^N) gb v` THEN
      SIMP_TAC[pde_rdt_step; pde_mlin_sol];
      GEN_TAC THEN USE_THEN "it" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[pde_rdt_ball]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau (g0:A->real^N^N)
          ((g:num->real->A->real^N^N) k)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RDT_BALL_MONO THEN EXISTS_TAC `K:real` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "it" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[] THEN DISCH_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < a + tau
        ==> pde_mnorm2 atlas n0 cs psi 0 (\x. (v:real->A->real^N^N) t x - gb t x) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `pde_tensor_smooth atlas (\x. (v:real->A->real^N^N) t x - gb t x)` ASSUME_TAC
    THENL
     [REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                     `a + tau`; `\t x. (v:real->A->real^N^N) t x - gb t x`; `t:real`]
        PDE_ML_TFAM_SLICE) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PDE_ME_TFAM_SUB THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC RDT_LE_ALL_POS THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ABBREV_TAC `e1 = e / (&3 + tau)` THEN
    SUBGOAL_THEN `&0 < e1 /\ e1 * (&3 + tau) = e` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "e1" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "uc" (MP_TAC o SPECL [`0:num`; `e1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "u0")) THEN
    USE_THEN "uc" (MP_TAC o SPECL [`1:num`; `e1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "u1")) THEN
    ABBREV_TAC `k = MAX k0 k1` THEN
    SUBGOAL_THEN `(k0:num) <= k /\ (k1:num) <= k /\ k0 <= SUC k` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
    (* the distance of gb and g k *)
    SUBGOAL_THEN
     `!t'. a <= t' /\ t' < a + tau
           ==> pde_mnorm2 atlas n0 cs psi 0
                 (\x. (gb:real->A->real^N^N) t' x - (g:num->real->A->real^N^N) k t' x) +
               real_integral (real_interval[a,t'])
                 (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. gb r x - g k r x))
               <= e1 * (&1 + tau)`
    ASSUME_TAC THENL
     [X_GEN_TAC `t':real` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= e1 /\ y <= e1 * tau ==> x + y <= e1 * (&1 + tau)`) THEN
      CONJ_TAC THENL [USE_THEN "u0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e1 * (t' - a)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RDT_REAL_INTEGRAL_LE_CONST THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                         `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                         `psi:num->A->real`; `a:real`; `a + tau`; `gb:real->A->real^N^N`;
                         `(g:num->real->A->real^N^N) k`; `t':real`] RDT_DQ_NONNEG) THEN
          ASM_SIMP_TAC[];
          REPEAT STRIP_TAC THEN USE_THEN "u1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    (* the contraction *)
    USE_THEN "con" (MP_TAC o SPECL [`gb:real->A->real^N^N`; `(g:num->real->A->real^N^N) k`;
                                    `v:real->A->real^N^N`; `(g:num->real->A->real^N^N) (SUC k)`;
                                    `e1 * (&1 + tau)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "it" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `a:real`; `a + tau`; `v:real->A->real^N^N`;
                   `(g:num->real->A->real^N^N) (SUC k)`; `t:real`] RDT_DQ_NONNEG) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    USE_THEN "u0" (MP_TAC o SPECL [`SUC k`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `0:num`; `\x. (v:real->A->real^N^N) t x - g (SUC k) t x`;
                   `\x. (gb:real->A->real^N^N) t x - g (SUC k) t x`] RDT_MNORM2_SUB_LE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                       `a + tau`; `\t x. (v:real->A->real^N^N) t x - g (SUC k) t x`; `t:real`]
          PDE_ML_TFAM_SLICE);
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                       `a + tau`; `\t x. (gb:real->A->real^N^N) t x - g (SUC k) t x`; `t:real`]
          PDE_ML_TFAM_SLICE)] THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PDE_ME_TFAM_SUB THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pde_mnorm2 atlas n0 cs psi 0
        (\x. (\x. (v:real->A->real^N^N) t x - g (SUC k) t x) x -
             (\x. (gb:real->A->real^N^N) t x - g (SUC k) t x) x) =
      pde_mnorm2 atlas n0 cs psi 0 (\x. v t x - gb t x)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RDT_MNORM2_CONG THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
        REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATRIX_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `e1 * (&3 + tau) = e` THEN
    UNDISCH_TAC `pde_mnorm2 atlas n0 cs psi 0
                   (\x. (gb:real->A->real^N^N) t x - (g:num->real->A->real^N^N) (SUC k) t x)
                 <= e1` THEN
    UNDISCH_TAC `pde_mnorm2 atlas n0 cs psi 0
                   (\x. (v:real->A->real^N^N) t x - (g:num->real->A->real^N^N) (SUC k) t x) +
                 real_integral (real_interval[a,t])
                   (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. v r x - g (SUC k) r x))
                 <= (e1 * (&1 + tau)) / &2` THEN
    UNDISCH_TAC `&0 <= real_integral (real_interval[a,t])
                   (\r. pde_mnorm2 atlas n0 cs psi 1
                          (\x. (v:real->A->real^N^N) r x - (g:num->real->A->real^N^N) (SUC k) r x))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM MATRIX_SUB_EQ] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `\x. (v:real->A->real^N^N) t x - gb t x`] RDT_MNORM2_ZERO) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `a + tau`; `\t x. (v:real->A->real^N^N) t x - gb t x`; `t:real`]
      PDE_ML_TFAM_SLICE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_ME_TFAM_SUB THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The limit of the iterates is a Ricci-DeTurck flow from g0, and the        *)
(* theorem PDE_RDT_FROM_MLIN: the uniform-time existence of Ricci-DeTurck    *)
(* flows from the linear existence statement.                                *)
(* ------------------------------------------------------------------------- *)

let RDT_LIM_FLOW = prove
 (`!(u:A->bool) (n:N->bool) (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
    n0 cs ks psi s B K tau (g0:A->real^N^N) a.
     PDE_MLIN_STATEMENT u n /\
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s /\ &0 <= B /\ &0 < K /\ &0 < tau /\
     riemannian_metric atlas g0 /\ pde_cbound atlas n0 cs ks (s + 3) B g0 /\
     pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (\t. g0) /\
     (!g v. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g /\
            pde_rdt_step (top,atlas) a (a + tau) g0 g v
            ==> pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 v) /\
     (!g g' v v' D.
        pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g /\
        pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g' /\
        pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 v' /\
        pde_rdt_step (top,atlas) a (a + tau) g0 g v /\
        pde_rdt_step (top,atlas) a (a + tau) g0 g' v' /\
        (!t. a <= t /\ t < a + tau
             ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g t x - g' t x) +
                 real_integral (real_interval[a,t])
                   (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g r x - g' r x)) <= D)
        ==> !t. a <= t /\ t < a + tau
                ==> pde_mnorm2 atlas n0 cs psi 0 (\x. v t x - v' t x) +
                    real_integral (real_interval[a,t])
                      (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. v r x - v' r x)) <= D / &2) /\
     (!g g' v v' D.
        pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau g0 g /\
        pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau g0 g' /\
        pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau g0 v' /\
        pde_rdt_step (top,atlas) a (a + tau) g0 g v /\
        pde_rdt_step (top,atlas) a (a + tau) g0 g' v' /\
        (!t. a <= t /\ t < a + tau
             ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g t x - g' t x) +
                 real_integral (real_interval[a,t])
                   (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g r x - g' r x)) <= D)
        ==> !t. a <= t /\ t < a + tau
                ==> pde_mnorm2 atlas n0 cs psi 0 (\x. v t x - v' t x) +
                    real_integral (real_interval[a,t])
                      (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. v r x - v' r x)) <= D / &2)
     ==> ?gb. pde_rdt_flow_from (top,atlas) g0 a (a + tau) gb /\
              !x. x IN topspace top ==> gb a x = g0 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "c4" o check (fun th ->
    is_forall(concl th) && rdt_has_const "real_integral" th &&
    can (find_term ((=) `&4 * K`)) (concl th))) THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:N->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `B:real`; `K:real`; `tau:real`; `g0:A->real^N^N`; `a:real`]
    RDT_LIM_ITER_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `g = rdt_iter (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a (a + tau)
                    (g0:A->real^N^N)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(!k. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau (g0:A->real^N^N)
           ((g:num->real->A->real^N^N) k)) /\
    (!k. pde_rdt_step (top,atlas) a (a + tau) g0 (g k) (g (SUC k)))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `K:real`; `tau:real`; `g0:A->real^N^N`; `a:real`;
                 `g:num->real->A->real^N^N`] RDT_LIM_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gb:real->A->real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(!k t. a <= t /\ t < a + tau ==> pde_tensor_smooth atlas ((g:num->real->A->real^N^N) k t)) /\
    (!t. a <= t /\ t < a + tau ==> pde_tensor_smooth atlas ((gb:real->A->real^N^N) t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `a + tau`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && rdt_has_const "pde_rdt_ball" th &&
      not(rdt_has_const "pde_rdt_step" th))) THEN
    SIMP_TAC[pde_rdt_ball];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `a:real`; `a + tau`; `g:num->real->A->real^N^N`; `gb:real->A->real^N^N`]
    RDT_LIM_MNORM2_CONV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "at") (LABEL_TAC "uc")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `K:real`; `tau:real`; `g0:A->real^N^N`; `a:real`;
                 `g:num->real->A->real^N^N`; `gb:real->A->real^N^N`] RDT_LIM_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < a + tau ==> riemannian_metric atlas ((gb:real->A->real^N^N) t)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau (g0:A->real^N^N) gb` THEN
    SIMP_TAC[pde_rdt_ball];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:N->bool`] RDT_STEP_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `a:real`; `a + tau`; `g0:A->real^N^N`; `gb:real->A->real^N^N`]) THEN
  ASM_REWRITE_TAC[REAL_LT_ADDR] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real->A->real^N^N`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `K:real`; `tau:real`; `g0:A->real^N^N`; `a:real`;
                 `g:num->real->A->real^N^N`; `gb:real->A->real^N^N`; `v:real->A->real^N^N`]
    RDT_LIM_FIXED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  EXISTS_TAC `gb:real->A->real^N^N` THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> (gb:real->A->real^N^N) a x = g0 x` ASSUME_TAC THENL
   [UNDISCH_TAC `pde_rdt_ball (top,atlas) n0 cs ks psi s (&4 * K) a tau (g0:A->real^N^N) gb` THEN
    SIMP_TAC[pde_rdt_ball];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pde_rdt_flow_from; REAL_LT_ADDR] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\r. ((v:real->A->real^N^N) r x)$i$j`; `min (t - a) (a + tau - t)`] THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(v:real->A->real^N^N) r x = gb r x` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_trhess atlas ((gb:real->A->real^N^N) t) g0 ((v:real->A->real^N^N) t) x =
    pde_trhess atlas (gb t) g0 (gb t) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_TRHESS_CONG THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `pde_rdt_step (top,atlas) a (a + tau) (g0:A->real^N^N) gb v` THEN
  REWRITE_TAC[pde_rdt_step; pde_mlin_sol] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`; `i:num`; `j:num`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[MATRIX_ARITH `!P R:real^N^N. P + (R - P) = R`]);;

let PDE_RDT_FROM_MLIN = prove
 (`!(u:A->bool) (n:N->bool).
        PDE_MLIN_STATEMENT u n ==> PDE_RDT_UNIFORM_STATEMENT u n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[PDE_RDT_UNIFORM_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                       `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`] RDT_CUTOFFS_EXIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `psi:num->A->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(2 * dimindex(:N) + 4) + 3` THEN X_GEN_TAC `B:real` THEN
  ABBREV_TAC `B' = max B (&0)` THEN
  SUBGOAL_THEN `&0 <= B' /\ B <= B'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `2 * dimindex(:N) + 4`; `(2 * dimindex(:N) + 4) + 3`; `B':real`]
    RDT_BALL_INV) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `tau1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inv"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `2 * dimindex(:N) + 4`; `(2 * dimindex(:N) + 4) + 3`; `B':real`; `K:real`]
    RDT_CONTRACT) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "con"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `2 * dimindex(:N) + 4`; `(2 * dimindex(:N) + 4) + 3`; `B':real`; `&4 * K`]
    RDT_CONTRACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "con4"))) THEN
  EXISTS_TAC `min tau1 (min tau2 tau3)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`g0:A->real^N^N`; `a:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_cbound atlas n0 cs ks ((2 * dimindex(:N) + 4) + 3) B' (g0:A->real^N^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_CBOUND_MONO THEN
    MAP_EVERY EXISTS_TAC [`(2 * dimindex(:N) + 4) + 3`; `B:real`] THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < min tau1 (min tau2 tau3) /\ min tau1 (min tau2 tau3) <= tau1 /\
                min tau1 (min tau2 tau3) <= tau2 /\ min tau1 (min tau2 tau3) <= tau3`
  MP_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `tau = min tau1 (min tau2 tau3)` THEN STRIP_TAC THEN
  USE_THEN "inv" (MP_TAC o SPECL [`tau:real`; `g0:A->real^N^N`; `a:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "con" (MP_TAC o SPECL [`tau:real`; `g0:A->real^N^N`; `a:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "con4" (MP_TAC o SPECL [`tau:real`; `g0:A->real^N^N`; `a:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC RDT_LIM_FLOW THEN
  MAP_EVERY EXISTS_TAC [`u:A->bool`; `n:N->bool`; `n0:num`; `cs:num->(A->bool)#(A->real^N)`;
                        `ks:num->real^N->bool`; `psi:num->A->real`; `2 * dimindex(:N) + 4`;
                        `B':real`; `K:real`] THEN
  ASM_REWRITE_TAC[LE_REFL]);;

