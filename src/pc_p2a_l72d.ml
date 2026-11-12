(* ========================================================================= *)
(* pc_p2a_l72d: O10 part 4, compactness for a single box with top tt (the    *)
(* base time): a sequence of p2a_admx curves from x in the compact set C of  *)
(* a box datum, with bounded L-length, has a subsequence converging at every *)
(* backward time in the slice topology; the limit starts at x and stays in C *)
(* (P2AK_SB_LIMIT).  Route: a fixed partition of [0,sqrt b] with mesh h,     *)
(* h E <= r^2 (stay-in-chart), on each piece a constant chart along a        *)
(* subsequence (pigeonhole) and Arzela-Ascoli in that chart, finitely many   *)
(* pieces by induction.                                                      *)
(* The first part: subsequences, pigeonhole, uniqueness of limits,           *)
(* partitions.                                                               *)
(* ========================================================================= *)

needs "src/pc_p2a_l72c.ml";;

prioritize_real();;
type_invention_error := true;;

let P2AK_SUBSEQ_O = prove
 (`!(r:num->num) t. p3_subseq r /\ p3_subseq t ==> p3_subseq (r o t)`,
  REWRITE_TAC[p3_subseq; o_THM] THEN MESON_TAC[]);;

let P2AK_SUBSEQ_ID = prove
 (`p3_subseq (\n:num. n)`,
  REWRITE_TAC[p3_subseq]);;

let P2AK_SUBSEQ_INDUCT = prove
 (`!(P:num->(num->num)->bool) M.
     (!i r t. P i r /\ p3_subseq t ==> P i (r o t)) /\
     (!i r. i < M /\ p3_subseq r ==> ?t. p3_subseq t /\ P i (r o t))
     ==> ?r. p3_subseq r /\ !i. i < M ==> P i r`,
  GEN_TAC THEN INDUCT_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `\n:num. n` THEN REWRITE_TAC[P2AK_SUBSEQ_ID; LT];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`M:num`; `r:num->num`] o check (fun th ->
    can (find_term ((=) `M:num`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[ARITH_RULE `M < SUC M`] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(r:num->num) o (t:num->num)` THEN ASM_SIMP_TAC[P2AK_SUBSEQ_O] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i:num = M` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "o")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let P2AK_PIGEON = prove
 (`!(f:num->A) s. FINITE s /\ (!n. f n IN s)
                  ==> ?a t. a IN s /\ p3_subseq t /\ !n. f(t n) = a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a:A. a IN s /\ INFINITE {n:num | (f:num->A) n = a}` STRIP_ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; INFINITE]) THEN
    SUBGOAL_THEN `FINITE(UNIONS (IMAGE (\a:A. {n:num | f n = a}) s))` MP_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `UNIONS (IMAGE (\a:A. {n:num | f n = a}) s) = (:num)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[GSYM INFINITE; num_INFINITE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INFINITE_ENUMERATE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `t:num->num`] THEN ASM_REWRITE_TAC[p3_subseq] THEN
  X_GEN_TAC `n:num` THEN
  UNDISCH_TAC `IMAGE (t:num->num) (:num) = {n | (f:num->A) n = a}` THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(t:num->num) n`) THEN MESON_TAC[]);;

let P2AK_LIM_UNIQUE = prove
 (`!(top:A topology) (z:num->A) y1 y2.
     hausdorff_space top /\ y1 IN topspace top /\ y2 IN topspace top /\
     (!O. open_in top O /\ y1 IN O ==> ?N. !n. N <= n ==> z n IN O) /\
     (!O. open_in top O /\ y2 IN O ==> ?N. !n. N <= n ==> z n IN O)
     ==> y1 = y2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y1:A`; `y2:A`] o GEN_REWRITE_RULE I [hausdorff_space]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O1:A->bool` (X_CHOOSE_THEN `O2:A->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `O2:A->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `O1:A->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN
  REWRITE_TAC[ARITH_RULE `(N1:num) <= N1 + N2 /\ (N2:num) <= N1 + N2`] THEN
  ASM SET_TAC[]);;

let P2AK_PARTITION_INDEX = prove
 (`!S M s. &0 < S /\ 1 <= M /\ &0 <= s /\ s <= S
           ==> ?i. i < M /\ &i * (S / &M) <= s /\ s <= &(SUC i) * (S / &M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `h = S / &M` THEN
  SUBGOAL_THEN `&0 < h /\ &M * h = S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_LMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(SPEC `\i. &i * h <= s` num_MAX) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO];
      EXISTS_TAC `M:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      SUBGOAL_THEN `&j * h <= &M * h` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RMUL_EQ]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `m:num < M` THENL
   [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `m:num = M` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(m:num < M) /\ m <= M ==> m = M`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&m * h <= &M * h` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  EXISTS_TAC `M - 1` THEN
  SUBGOAL_THEN `SUC(M - 1) = M:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M * h` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE] THEN ARITH_TAC);;

let P2AK_COMPACT_TRANSFER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b t C.
     p2a_region V W a b /\ a < t /\ t <= b /\ compact_in (p2a_vtop V b) C /\ C SUBSET W
     ==> compact_in (p2a_vtop V t) C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IN_SUBTOPOLOGY_IMP_COMPACT THEN
  EXISTS_TAC `W:A->bool` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `t:real`]
                P2A_REGION_SUBTOP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY]);;

(* ------------------------------------------------------------------------- *)
(* The piece predicate (a constant chart and uniform chart convergence on   *)
(* [p,q] along the subsequence), one piece at a time, and the limit curve   *)
(* (the slice-topology limit, chosen by SELECT).                            *)
(* ------------------------------------------------------------------------- *)

let p2ak_pp = new_definition
 `p2ak_pp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
          (W:A->bool) (tt:real) (gs:num->real->A) (Fs:A->bool) (R:A->real)
          (p:real) (q:real) (sub:num->num) <=>
    ?k (Y:real^1->real^N).
      k IN Fs /\ Y continuous_on interval[lift p,lift q] /\
      (!s. p <= s /\ s <= q
           ==> Y(lift s) IN cball(SND(chart_at (p2a_vatlas V tt) k) k,&2 * R k)) /\
      (!n s. p <= s /\ s <= q
             ==> gs (sub n) (s pow 2) IN FST(chart_at (p2a_vatlas V tt) k) INTER W) /\
      (!e. &0 < e
           ==> ?N. !n s. N <= n /\ p <= s /\ s <= q
                         ==> dist(SND(chart_at (p2a_vatlas V tt) k) (gs (sub n) (s pow 2)),
                                  Y(lift s)) < e)`;;

let P2AK_PP_SUBSEQ = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W tt gs Fs R p q sub t.
     p2ak_pp V W tt gs Fs R p q sub /\ p3_subseq t
     ==> p2ak_pp V W tt gs Fs R p q (sub o t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ak_pp; o_THM] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:A`; `Y:real^1->real^N`] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p3_subseq t` THEN REWRITE_TAC[p3_subseq] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MONOTONE_BIGGER) THEN SIMP_TAC[]);;

let P2AK_SB_PIECE_STEP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' C T1 Fs R r lam Gm Rm tt (x:A) b (gs:num->real->A) Lb p q (r0:num->num).
     p2ak_bxd V W a' tt C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\ b <= T1 /\ &0 <= Lb /\
     (!n. p2a_admx V tt x b (gs n) /\ p2a_L_length V tt (gs n) b <= Lb /\
          !tau. &0 <= tau /\ tau <= b ==> gs n tau IN C) /\
     &0 <= p /\ p < q /\ q pow 2 <= b /\
     (q - p) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm)) <= r pow 2 /\
     p3_subseq r0
     ==> ?t. p3_subseq t /\ p2ak_pp V W tt gs Fs R p q (r0 o t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  ABBREV_TAC `ch = chart_at (p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `&0 <= b /\ &0 <= p pow 2 /\ p pow 2 <= b` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `p pow 2 <= q pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `p:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  (* the chart of the start point, constant along a subsequence *)
  SUBGOAL_THEN
   `!n. ?k:A. k IN Fs /\
              (gs:num->real->A) ((r0:num->num) n) (p pow 2) IN FST((ch:A->(A->bool)#(A->real^N)) k) INTER W /\
              dist(SND(ch k) (gs (r0 n) (p pow 2)),SND(ch k) k) < (R:A->real) k`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(r0:num->num) n` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `kf:num->A`) THEN
  MP_TAC(ISPECL [`kf:num->A`; `Fs:A->bool`] P2AK_PIGEON) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:A` (X_CHOOSE_THEN `t1:num->num` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `g = \n. (gs:num->real->A) ((r0:num->num) ((t1:num->num) n))` THEN
  ABBREV_TAC `phi = SND((ch:A->(A->bool)#(A->real^N)) K)` THEN
  ABBREV_TAC `U = FST((ch:A->(A->bool)#(A->real^N)) K)` THEN
  SUBGOAL_THEN
   `!n. (g:num->real->A) n (p pow 2) IN U INTER W /\
        dist((phi:A->real^N)(g n (p pow 2)),phi K) < (R:A->real) K`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "g" THEN MAP_EVERY EXPAND_TAC ["phi"; "U"] THEN
    BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(t1:num->num) n` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `kf:num->A`)) (concl th) &&
      can (find_term ((=) `R:A->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)) tt x b ((g:num->real->A) n) /\
        p2a_L_length V tt (g n) b <= Lb /\
        (!tau. &0 <= tau /\ tau <= b ==> g n tau IN C)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "g" THEN BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* each curve stays in the chart ball *)
  SUBGOAL_THEN
   `!n s. p <= s /\ s <= q
          ==> (g:num->real->A) n (s pow 2) IN U INTER W /\
              dist((phi:A->real^N)(g n (s pow 2)),phi(g n (p pow 2))) <= r`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`;
                   `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                   `tt:real`; `x:A`; `b:real`; `(g:num->real->A) n`; `Lb:real`; `K:A`;
                   `p:real`; `q:real`] P2AK_BXD_STAY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k:A. k IN Fs ==> r <= (R:A->real) k` ASSUME_TAC THENL
   [X_GEN_TAC `k:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s. p <= s /\ s <= q
          ==> dist((phi:A->real^N) K,phi((g:num->real->A) n (s pow 2))) <= &2 * (R:A->real) K`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `r:real`)) (concl th) &&
      can (find_term ((=) `g:num->real->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `R:A->real`)) (concl th) &&
      can (find_term ((=) `g:num->real->A`)) (concl th))) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `K:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `r:real`)) (concl th) &&
      can (find_term ((=) `Fs:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(phi:A->real^N) K`; `(phi:A->real^N)((g:num->real->A) n (p pow 2))`;
                   `(phi:A->real^N)((g:num->real->A) n (s pow 2))`] DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`(phi:A->real^N) K`; `(phi:A->real^N)((g:num->real->A) n (p pow 2))`]
                  DIST_SYM) THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((g:num->real->A) n (s pow 2))`;
                   `(phi:A->real^N)((g:num->real->A) n (p pow 2))`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s s'. p <= s /\ s <= s' /\ s' <= q
             ==> dist((phi:A->real^N)((g:num->real->A) n (s' pow 2)),phi(g n (s pow 2))) pow 2
                 <= (s' - s) * E`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`;
                   `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                   `tt:real`; `x:A`; `b:real`; `(g:num->real->A) n`; `Lb:real`; `K:A`;
                   `s:real`; `s':real`] P2AK_BXD_FE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `u:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `r:real`)) (concl th) &&
        can (find_term ((=) `g:num->real->A`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[IN_CBALL] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `u:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&2 * (R:A->real) K`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (R:A->real) K` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `K:A` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `r:real`)) (concl th) &&
          can (find_term ((=) `Fs:A->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* Arzela-Ascoli for the chart curves on [p,q] *)
  MP_TAC(ISPECL [`\n v. (phi:A->real^N)((g:num->real->A) n (drop v pow 2))`;
                 `interval[lift p,lift q]`; `norm((phi:A->real^N) K) + &2 * (R:A->real) K`]
                ARZELA_ASCOLI) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&2 * (R:A->real) K`)) (concl th))) THEN
      ASM_REWRITE_TAC[dist] THEN NORM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `e:real`] THEN STRIP_TAC THEN
    EXISTS_TAC `e pow 2 / (E + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(s - y) * E < e pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e pow 2 / (E + &1) * E` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < e pow 2 / (E + &1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `e pow 2 / (E + &1) * E = e pow 2 - e pow 2 / (E + &1)` SUBST1_TAC THENL
       [SUBGOAL_THEN `~(E + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM dist] THEN
    SUBGOAL_THEN `dist((phi:A->real^N)((g:num->real->A) n (s pow 2)),phi(g n (y pow 2))) pow 2
                  < e pow 2` MP_TAC THENL
     [ASM_CASES_TAC `s <= y` THENL
       [SUBGOAL_THEN `abs(s - y) = y - s` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`; `y:real`] o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `E:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `abs(s - y) = s - y` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:real`; `s:real`] o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `E:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN
    SIMP_TAC[REAL_ABS_DIST; REAL_ARITH `abs e = e <=> &0 <= e`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:real^1->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t2:num->num` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `(t1:num->num) o (t2:num->num)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AK_SUBSEQ_O THEN ASM_REWRITE_TAC[p3_subseq]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. (gs:num->real->A) (((r0:num->num) o (t1:num->num) o (t2:num->num)) n) =
                    (g:num->real->A) (t2 n)` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "g" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
  REWRITE_TAC[p2ak_pp] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`K:A`; `Y:real^1->real^N`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_CBALL] THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `dist((phi:A->real^N) K,(Y:real^1->real^N)(lift s)) - &2 * (R:A->real) K`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPECL [`N:num`; `lift s`])) THEN
    REWRITE_TAC[GE; LE_REFL; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(t2:num->num) N`; `s:real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&2 * (R:A->real) K`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[dist] THEN NORM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(t2:num->num) n`; `s:real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `r:real`)) (concl th) &&
      can (find_term ((=) `g:num->real->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `lift s`]) THEN
    ASM_REWRITE_TAC[GE; IN_INTERVAL_1; LIFT_DROP; dist]]);;

let P2AK_SB_LIMIT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' C T1 Fs R r lam Gm Rm tt (x:A) b (gs:num->real->A) Lb.
     p2ak_bxd V W a' tt C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     &0 < b /\ b <= T1 /\ &0 <= Lb /\
     (!n. p2a_admx V tt x b (gs n) /\ p2a_L_length V tt (gs n) b <= Lb /\
          !tau. &0 <= tau /\ tau <= b ==> gs n tau IN C)
     ==> ?sub gamma.
           p3_subseq sub /\ gamma (&0) = x /\
           (!tau. &0 <= tau /\ tau <= b
                  ==> gamma tau IN C /\
                      !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                          ==> ?N. !n. N <= n ==> gs (sub n) tau IN O)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm)` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `S = sqrt b` THEN
  SUBGOAL_THEN `&0 < S /\ S pow 2 = b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `?M. 1 <= M /\ S * E <= &M * r pow 2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `(S * E) / r pow 2` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `m + 1` THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&m * r pow 2` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(S * E) / r pow 2 <= &m` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `h = S / &M` THEN
  SUBGOAL_THEN `&0 < h /\ &M * h = S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_LMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `h * E <= r pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `h * E = (S * E) / &M` SUBST1_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the pieces *)
  MP_TAC(ISPECL [`\i sub. p2ak_pp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) W tt (gs:num->real->A) Fs R
                                    (&i * h) (&(SUC i) * h) sub`; `M:num`] P2AK_SUBSEQ_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AK_PP_SUBSEQ THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `r0:num->num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2AK_SB_PIECE_STEP THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `C:A->bool`; `T1:real`; `r:real`; `lam:real`; `Gm:real`;
                          `Rm:real`; `x:A`; `b:real`; `Lb:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(SUC i) * h <= S` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN UNDISCH_TAC `&M * h = S` THEN EXPAND_TAC "S" THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "b" THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
                      ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      REWRITE_TAC[REAL_ARITH `(&i + &1) * h - &i * h = h`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= b
          ==> ?y:A. y IN topspace(p2a_vtop (V:(real->A topology)#
                         (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) /\
                    !O. open_in (p2a_vtop V (tt - tau)) O /\ y IN O
                        ==> ?N. !n. N <= n ==> (gs:num->real->A) ((sub:num->num) n) tau IN O`
  MP_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real`; `M:num`; `sqrt tau`] P2AK_PARTITION_INDEX) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE] THEN UNDISCH_TAC `sqrt b = S` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_pp")) (concl th))) THEN
    ASM_REWRITE_TAC[p2ak_pp] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:A` (X_CHOOSE_THEN `Y:real^1->real^N` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(sqrt tau) pow 2 = tau` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `a' < tt - tau /\ tt - tau <= tt` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(Y:real^1->real^N)(lift(sqrt tau)) IN IMAGE (phi:A->real^N) (U INTER W)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
      MATCH_MP_TAC(SET_RULE `!s t (x:real^N). s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `cball((phi:A->real^N) k,&2 * (R:A->real) k)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`;
                   `phi:A->real^N`; `(Y:real^1->real^N)(lift(sqrt tau))`] P2A_CHART_PIECE_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    EXISTS_TAC `chart_inv (U INTER W,phi:A->real^N) ((Y:real^1->real^N)(lift(sqrt tau)))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)`; `W:A->bool`; `a':real`; `tt:real`; `tt - tau`]
                    P2A_REGION_SLICE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
        concl th = `open_in (p2a_vtop (V:(real->A topology)#
          (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) W`)) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`;
                   `phi:A->real^N`; `tt - tau`; `O:A->bool`;
                   `(Y:real^1->real^N)(lift(sqrt tau))`] P2A_CHART_INV_NBHD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Y:real^1->real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `sqrt tau`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N:num`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `sqrt tau`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sub:num->num`)) (concl th) &&
      not(can (find_term ((=) `e:real`)) (concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) tau)` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `O:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`;
                   `phi:A->real^N`; `(gs:num->real->A) ((sub:num->num) n) tau`]
                  P2A_REGION_CHART_INV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `gamma = \tau. @y:A. y IN topspace(p2a_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) /\
                   !O. open_in (p2a_vtop V (tt - tau)) O /\ y IN O
                       ==> ?N. !n. N <= n ==> (gs:num->real->A) ((sub:num->num) n) tau IN O` THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= b
          ==> (gamma:real->A) tau IN topspace(p2a_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) /\
              !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                  ==> ?N. !n. N <= n ==> (gs:num->real->A) ((sub:num->num) n) tau IN O`
  ASSUME_TAC THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN EXPAND_TAC "gamma" THEN
    CONV_TAC SELECT_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `gamma:real->A`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. hausdorff_space(p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN SIMP_TAC[p2a_svs];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AK_LIM_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`p2a_vtop (V:(real->A topology)#
                             (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - &0)`;
                          `\n. (gs:num->real->A) ((sub:num->num) n) (&0)`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    REWRITE_TAC[REAL_LE_REFL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!n. (gs:num->real->A) ((sub:num->num) n) (&0) = x /\
                      x IN topspace(p2a_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - &0))`
    ASSUME_TAC THENL
     [X_GEN_TAC `n:num` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
      REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closed_in (p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) C`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AK_COMPACT_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `tt:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[closed_in] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) (tt - tau)) DIFF C` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(sub:num->num) N` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `tau:real` o CONJUNCT2 o CONJUNCT2) THEN ASM_SIMP_TAC[]);;

