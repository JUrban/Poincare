(* ========================================================================= *)
(* pc_p2a_l72h: O10 view-X form, part 2, MT Lemma 7.2(a) and (c) for         *)
(* p2a_admx minimizing sequences in the boxes of a p2a_cbox.  (a): the fat   *)
(* boxes (chart balls of radius 3 R) form a p2a_cbox containing the limit    *)
(* curve.  (c): good pieces in box charts with a general top (BVP solutions, *)
(* almost-minimality through P2AXR_REPLACE_X), made uniform by sequential    *)
(* compactness, give a limit curve that is admissible, C^1 without corners   *)
(* and of L-length at most the infimum.                                      *)
(* The first part: fat boxes, (a), windows and the local-to-uniform lemma.   *)
(* ========================================================================= *)

needs "src/pc_p2a_l72g.ml";;

prioritize_real();;
type_invention_error := true;;

(* Fat boxes: the closed chart balls of radius 3 R j k of the box charts of *)
(* box j (compact in the slices over (A0 j,b j], containing C j).           *)

let p2aj_fat = new_definition
 `p2aj_fat (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
           (W:num->A->bool) (b:num->real) (Fs:num->A->bool) (R:num->A->real) (j:num) =
    {y | ?k. k IN Fs j /\ y IN FST(chart_at (p2a_vatlas V (b j)) k) INTER W j /\
             SND(chart_at (p2a_vatlas V (b j)) k) y IN
             cball(SND(chart_at (p2a_vatlas V (b j)) k) k,&3 * R j k)}`;;

let P2AJ_FAT_COMPACT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm j s.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ j <= nb /\ A0 j < s /\ s <= b j
     ==> compact_in (p2a_vtop V s) (p2aj_fat V W b Fs R j) /\
         p2aj_fat V W b Fs R j SUBSET W j /\ C j SUBSET p2aj_fat V W b Fs R j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd] o check (fun th ->
    not(is_forall(concl th)) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `(b:num->real) j`] P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  (* each chart ball *)
  SUBGOAL_THEN
   `!k:A. k IN (Fs:num->A->bool) j
          ==> {y | y IN FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) k) INTER
                        (W:num->A->bool) j /\
                   SND(chart_at (p2a_vatlas V (b j)) k) y IN
                   cball(SND(chart_at (p2a_vatlas V (b j)) k) k,&3 * (R:num->A->real) j k)} =
              {y | y IN FST(chart_at (p2a_vatlas V (b j)) k) /\
                   SND(chart_at (p2a_vatlas V (b j)) k) y IN
                   cball(SND(chart_at (p2a_vatlas V (b j)) k) k,&3 * R j k)} /\
              compact_in (p2a_vtop V (b j))
               {y | y IN FST(chart_at (p2a_vatlas V (b j)) k) /\
                    SND(chart_at (p2a_vatlas V (b j)) k) y IN
                    cball(SND(chart_at (p2a_vatlas V (b j)) k) k,&3 * R j k)}`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)`;
                   `FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))`;
                   `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))`] CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
    SUBGOAL_THEN `cball(SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k,
                        &3 * (R:num->A->real) j k) SUBSET
                  IMAGE (SND(chart_at (p2a_vatlas V (b j)) k))
                        (FST(chart_at (p2a_vatlas V (b j)) k) INTER (W:num->A->bool) j)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k,
                        &6 * (R:num->A->real) j k)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `y:A` THEN
      EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `?z:A. z IN FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) INTER
                          (W:num->A->bool) j /\
                          SND(chart_at (p2a_vatlas V (b j)) k) z =
                          SND(chart_at (p2a_vatlas V (b j)) k) y`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(y:A) = z` (fun th -> REWRITE_TAC[th]) THENL
       [ALL_TAC; ASM SET_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
        not(can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th)))) THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `y:A` th) THEN MP_TAC(SPEC `z:A` th)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(z:A) IN FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))`
      (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; MESON_TAC[]];
      MATCH_MP_TAC MFDC_CHART_COMPACT THEN
      EXISTS_TAC `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[PAIR; COMPACT_CBALL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)))
                        (FST(chart_at (p2a_vatlas V (b j)) k) INTER (W:num->A->bool) j)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2aj_fat (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b Fs R j =
    UNIONS (IMAGE (\k:A. {y | y IN FST(chart_at (p2a_vatlas V ((b:num->real) j)) k) /\
                              SND(chart_at (p2a_vatlas V (b j)) k) y IN
                              cball(SND(chart_at (p2a_vatlas V (b j)) k) k,
                                    &3 * (R:num->A->real) j k)})
                  ((Fs:num->A->bool) j))`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2aj_fat; EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN
    EQ_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC) THEN EXISTS_TAC `k:A` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_IN_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN X_GEN_TAC `k:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2AK_COMPACT_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN SET_TAC[];
    REWRITE_TAC[p2aj_fat] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; p2aj_fat; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term ((=) `(C:num->A->bool) j`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* (a): the fat boxes form a p2a_cbox (eta / 2, times [A0 j + eta / 2,b j],  *)
(* regions over (A0 j,b j]) containing the limit (P2AJ_LIM_STRICT).          *)

let P2AJ_FAT_CBOX = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm
     ==> p2a_cbox V (\t. {y | ?j. j < nb /\ A0 j + eta / &2 <= t /\ t <= b j /\
                                  y IN p2aj_fat V W b Fs R j})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  REWRITE_TAC[p2a_cbox] THEN
  MAP_EVERY EXISTS_TAC [`nb:num`; `W:num->A->bool`; `\j. p2aj_fat (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b Fs R j`;
                        `\j. (A0:num->real) j + eta / &2`; `b:num->real`; `eta / &2`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  TRY(CONJ_TAC THENL [ALL_TAC; MESON_TAC[]]) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `((A0:num->real) j + eta / &2) - eta / &2 = A0 j` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                   `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                   `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                   `Rm:real`; `j:num`; `(b:num->real) j`] P2AJ_FAT_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      CONJ_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2ak_bxd] o check (fun th ->
      not(is_forall(concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
    SIMP_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                   `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                   `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                   `Rm:real`; `j:num`; `s:real`] P2AJ_FAT_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; ASM_REAL_ARITH_TAC];
      SIMP_TAC[]]]);;

(* A strict window: away from s = 0 the times of a window are strictly below *)
(* the top.                                                                   *)

let P2AJ_WINDOW_STRICT = prove
 (`!tt A0 b' p q sa sb.
     &0 < p /\ sa < p /\ p <= q /\ q < sb /\
     (!s. sa < s /\ s < sb ==> A0 < tt - s pow 2 /\ tt - s pow 2 <= b')
     ==> ?sa'. sa' < p /\ &0 < sa' /\
               !s. sa' < s /\ s < sb ==> A0 < tt - s pow 2 /\ tt - s pow 2 < b'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `max sa (p / &2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(s + max sa (p / &2)) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `((s + max sa (p / &2)) / &2) pow 2 < s pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* A property of short pieces that holds locally holds for all pieces of a  *)
(* uniform length (sequential compactness of [a,c]).                         *)

let P2AJ_LOCAL_UNIFORM = prove
 (`!(G:real->real->bool) a c.
     (!s0. a <= s0 /\ s0 <= c
           ==> ?r. &0 < r /\ !p p'. s0 - r < p /\ p <= p' /\ p' < s0 + r ==> G p p')
     ==> ?h. &0 < h /\ !p p'. a <= p /\ p <= p' /\ p' <= c /\ p' - p <= h ==> G p p'`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "LOC") THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; NOT_FORALL_THM;
                                   TAUT `~(p ==> q) <=> p /\ ~q`; REAL_NOT_LT]) THEN
  DISCH_THEN(LABEL_TAC "NEG") THEN
  SUBGOAL_THEN `!n:num. ?p p'. a <= p /\ p <= p' /\ p' <= c /\ p' - p <= inv(&n + &1) /\
                               ~((G:real->real->bool) p p')` MP_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "NEG" (MP_TAC o SPEC `inv(&n + &1)`) THEN
    MATCH_MP_TAC(TAUT `~p /\ (q ==> r) ==> (p \/ q ==> r)`) THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_NOT_LE; REAL_LT_INV_EQ] THEN MP_TAC(SPEC `n:num` REAL_POS) THEN
      REAL_ARITH_TAC;
      MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `pf:num->real` (X_CHOOSE_THEN `qf:num->real` (LABEL_TAC "PQ"))) THEN
  MP_TAC(ISPECL [`lift a`; `lift c`] COMPACT_INTERVAL) THEN REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. lift((pf:num->real) n)`) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    USE_THEN "PQ" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^1` (X_CHOOSE_THEN `rr:num->num` STRIP_ASSUME_TAC)) THEN
  USE_THEN "LOC" (MP_TAC o SPEC `drop l`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(l:real^1) IN interval[lift a,lift c]` THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r0 / &2` o REWRITE_RULE[LIM_SEQUENTIALLY] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "-->")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[o_THM; DIST_REAL; GSYM drop; LIFT_DROP]] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  SUBGOAL_THEN `?N2. ~(N2 = 0) /\ inv(&N2) < r0 / &2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `r0 / &2` REAL_ARCH_INV) THEN
    SUBGOAL_THEN `&0 < r0 / &2` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `n = (rr:num->num) (N1 + N2)` THEN
  SUBGOAL_THEN `N2 <= n:num` ASSUME_TAC THENL
   [MP_TAC(ISPEC `rr:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `N1 + N2:num`) THEN EXPAND_TAC "n" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&n + &1) < r0 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `~(N2 = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN UNDISCH_TAC `N2 <= n:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N1:num`)) (concl th))) THEN
  ASM_REWRITE_TAC[LE_ADD] THEN DISCH_TAC THEN
  USE_THEN "PQ" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  UNDISCH_TAC `~((G:real->real->bool) ((pf:num->real) n) ((qf:num->real) n))` THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `abs((pf:num->real) n - drop l) < r0 / &2` THEN ASM_REAL_ARITH_TAC);;

(* Box charts with a general top. *)

(* ------------------------------------------------------------------------- *)
(* Box charts with a general top b' (region over (a',b']): the piece energy *)
(* bound, the replacement of a piece of a p2a_admx curve by a chart curve,  *)
(* BVP data, almost-minimality, the L-integral over a good piece, and the   *)
(* integrability of the L-integrand from the bounds on [t,b].               *)
(* ------------------------------------------------------------------------- *)

(* The chart curve of a piece of a p2a_admx curve in a box chart with a     *)
(* general top: p2ak_sq, the chart Lagrangian integral and the energy bound. *)

let P2AJ_BXD_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' C T1 Fs R r lam Gm Rm tt (x:A) b (gamma:real->A) Lb Rm0 k s1 s2 sa sb.
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     p2a_admx V tt x b gamma /\ &0 <= Rm0 /\ Rm <= Rm0 /\
     (!tau. &0 <= tau /\ tau <= b
            ==> --(sqrt tau * Rm0) <= p2a_L_integrand V tt gamma b tau) /\
     p2a_L_length V tt gamma b <= Lb /\
     k IN Fs /\ &0 < s1 /\ s1 < s2 /\ s2 pow 2 <= b /\ sa < s1 /\ s2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     (!s. s1 <= s /\ s <= s2 ==> b' - T1 <= tt - s pow 2) /\
     (!s. s1 <= s /\ s <= s2
          ==> gamma(s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
              SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2)) IN cball(SND (chart_at (p2a_vatlas V b') k) k,&6 * R k))
     ==> ?K. p2ak_sq (IMAGE (SND (chart_at (p2a_vatlas V b') k)) (FST (chart_at (p2a_vatlas V b') k) INTER W)) s1 s2
                     (\v. SND (chart_at (p2a_vatlas V b') k) (gamma(drop v pow 2)))
                     (\v. vector_derivative (\v. SND (chart_at (p2a_vatlas V b') k) (gamma(drop v pow 2))) (at v))
                     K (K INTER real_interval[s1,s2]) /\
             (\s. p2a_llag (p2a_rlocal V W b' (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))) tt s
                    (SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2)))
                    (vector_derivative (\v. SND (chart_at (p2a_vatlas V b') k) (gamma(drop v pow 2))) (at (lift s))))
             real_integrable_on real_interval[s1,s2] /\
             real_integral (real_interval[s1,s2])
               (\s. p2a_llag (p2a_rlocal V W b' (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))) tt s
                      (SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2)))
                      (vector_derivative (\v. SND (chart_at (p2a_vatlas V b') k) (gamma(drop v pow 2))) (at (lift s)))) =
             real_integral (real_interval[s1 pow 2,s2 pow 2]) (p2a_L_integrand V tt gamma b) /\
             real_integral (real_interval[s1,s2])
               (\s. norm(vector_derivative (\v. SND (chart_at (p2a_vatlas V b') k) (gamma(drop v pow 2))) (at (lift s))) pow 2)
             <= &2 / lam * (Lb + &4 * b * sqrt b * Rm0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b /\ s2 <= sqrt b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `s2:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `s1:real`; `s2:real`; `sa:real`; `sb:real`;
                 `cball((phi:A->real^N) k,&6 * (R:A->real) k)`; `lam:real`; `Rm:real`]
                P2AK_PIECE_SQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `u:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`tt - s pow 2`; `y:real^N`; `u:real^N`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `T1:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K:real->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `real_integral (real_interval[s1 pow 2,s2 pow 2])
                  (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) b)
                <= Lb + &2 * (sqrt b * Rm0) * (b - &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AK_INT_PIECE_UPPER THEN
    UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b (gamma:real->A)` THEN
    REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM p2a_L_length] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(sqrt tau * Rm0)` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `Rm0:real`)) (concl th))) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 pow 2 * Rm * (s2 - s1) <= b * Rm0 * sqrt b` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 / lam * (real_integral (real_interval[s1 pow 2,s2 pow 2])
                           (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) b) +
                         &2 * s2 pow 2 * Rm * (s2 - s1))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;

(* Replacing a piece of a p2a_admx curve by a chart curve in a box chart  *)
(* with a general top (strict window below the top).                        *)

let P2AJ_REPLACE_PIECE_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) b (gamma:real->A) W a' b'' U (phi:A->real^N) (sol:real^1->real^N) p q sa sb.
     p2a_svs V /\ p2a_admx V tt x b gamma /\ p2a_region V W a' b'' /\
     (U,phi) IN p2a_vatlas V b'' /\
     &0 < p /\ p < q /\ q pow 2 <= b /\ sa < p /\ q < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'') /\
     gamma(p pow 2) IN U INTER W /\ gamma(q pow 2) IN U INTER W /\
     sol(lift p) = phi(gamma(p pow 2)) /\ sol(lift q) = phi(gamma(q pow 2)) /\
     (!s. p <= s /\ s <= q
          ==> sol(lift s) IN IMAGE phi (U INTER W) /\ sol differentiable (at (lift s)) /\
              (\v. vector_derivative sol (at v)) continuous (at (lift s)))
     ==> ?c. p2a_admx V tt x b c /\ c b = gamma b /\
             p2a_L_length V tt c b =
             p2a_L_length V tt gamma b -
             real_integral (real_interval[p pow 2,q pow 2]) (p2a_L_integrand V tt gamma b) +
             p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt sol p q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < q /\ &0 < p pow 2 /\ p pow 2 < q pow 2 /\ &0 < b`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `p:real` REAL_LE_POW_2) THEN
      SUBGOAL_THEN `&0 < p pow 2 /\ p pow 2 < q pow 2` MP_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
                        MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
                        ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `a' < b''` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `p:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`; `sol:real^1->real^N`; `p:real`; `q:real`;
                 `sa:real`; `sb:real`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `sig = \tau. chart_inv (U INTER W,phi:A->real^N) ((sol:real^1->real^N)(lift(sqrt tau)))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(sig:real->A) (p pow 2) = (gamma:real->A)(p pow 2) /\ sig (q pow 2) = gamma(q pow 2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; LIFT_DROP] THEN
    CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN DISCH_TAC THEN
  ASM_CASES_TAC `q pow 2 < b` THENL
   [MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `gamma:real->A`; `sig:real->A`;
                   `b:real`; `p pow 2`; `q pow 2`] P2AXR_REPLACE_X) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `\tau. if tau <= p pow 2 then (gamma:real->A) tau
                      else if tau <= q pow 2 then (sig:real->A) tau else gamma tau` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `q2 < b ==> ~(b <= q2)`; COND_ID] THEN
    SUBGOAL_THEN `real_integral (real_interval[p pow 2,q pow 2]) (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (sig:real->A) b) =
                  real_integral (real_interval[p pow 2,q pow 2]) (p2a_L_integrand V tt sig (q pow 2))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC P2AK_RINT_OPEN_EQ THEN
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`p pow 2`; `q pow 2`] THEN
      REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `q pow 2 = b` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `sig:real->A`; `gamma:real->A`;
                 `\tau. if tau <= p pow 2 then (gamma:real->A) tau else sig tau`;
                 `b:real`; `p pow 2`] P2AXR_SEG_GLUE_X) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AXR_ADMX_RESTRICT THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      CONJ_TAC THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      (SUBGOAL_THEN `tau = p pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]])];
    ALL_TAC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `\tau. if tau <= p pow 2 then (gamma:real->A) tau else sig tau` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `p2 < b ==> ~(b <= p2)`] THEN
  SUBGOAL_THEN `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) (p pow 2) =
                real_integral (real_interval[&0,p pow 2]) (p2a_L_integrand V tt gamma b)`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2a_L_length] THEN
    MATCH_MP_TAC P2AK_RINT_OPEN_EQ THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `p pow 2`] THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[&0,p pow 2]) (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) b) +
                real_integral (real_interval[p pow 2,b]) (p2a_L_integrand V tt gamma b) =
                p2a_L_length V tt gamma b` MP_TAC THENL
   [REWRITE_TAC[p2a_L_length] THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
    UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b (gamma:real->A)` THEN REWRITE_TAC[p2a_admx] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* BVP data for a box chart with a general top over an s-range whose times *)
(* lie strictly inside the region.                                          *)

let P2AJ_BOX_BVP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' C T1 Fs R r lam Gm Rm tt k E sa sb.
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\ k IN Fs /\
     &0 <= sa /\ sa < sb /\ a' < tt - sb pow 2 /\ tt - sa pow 2 < b' /\ &0 < E
     ==> ?delta rho sol.
           p2ak_bvpd (ball(SND (chart_at (p2a_vatlas V b') k) k,&6 * R k))
                     (p2a_rlocal V W b' (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k)))
                     tt (cball(SND (chart_at (p2a_vatlas V b') k) k,&3 * R k)) E sa sb delta rho sol`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`] P2A_REGION_LRICCI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball((phi:A->real^N) k,&6 * (R:A->real) k) SUBSET IMAGE phi (U INTER W)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((phi:A->real^N) k,&6 * (R:A->real) k)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AK_BVPD_EXISTS THEN MAP_EVERY EXISTS_TAC [`a':real`; `b':real`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AK_LSMOOTH_SUBSET THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AK_LRICCI_SUBSET THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_CBALL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC);;

(* Almost-minimality of a piece of a minimizing sequence of p2a_admx curves *)
(* against chart curves in a box chart with a general top.                  *)

let P2AJ_ALMOST_MIN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) b (g:num->real->A) q Lam W a' b'' U (phi:A->real^N)
    (soln:num->real^1->real^N) p p' N0 sa sb.
     p2a_svs V /\ p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     (!n. p2a_admx V tt x b (g n) /\ g n b = q) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> p2a_L_length V tt (g n) b <= Lam + e) /\
     (!gamma'. p2a_admx V tt x b gamma' /\ gamma' b = q
               ==> Lam <= p2a_L_length V tt gamma' b) /\
     &0 < p /\ p < p' /\ p' pow 2 <= b /\ sa < p /\ p' < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'') /\
     (!n. N0 <= n
          ==> g n (p pow 2) IN U INTER W /\ g n (p' pow 2) IN U INTER W /\
              soln n (lift p) = phi(g n (p pow 2)) /\
              soln n (lift p') = phi(g n (p' pow 2)) /\
              (!s. p <= s /\ s <= p'
                   ==> soln n (lift s) IN IMAGE phi (U INTER W) /\
                       soln n differentiable (at (lift s)) /\
                       (\v. vector_derivative (soln n) (at v)) continuous (at (lift s))))
     ==> !e. &0 < e
             ==> ?N. !n. N <= n
                         ==> real_integral (real_interval[p pow 2,p' pow 2])
                               (p2a_L_integrand V tt (g n) b)
                             <= p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt (soln n) p p' + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Lam:real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "real_lt")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N0 + N1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `soln:num->real^1->real^N`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N1:num`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th) &&
    can (find_term ((=) `q:A`)) (concl th) && not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `b:real`;
                 `(g:num->real->A) n`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `(soln:num->real^1->real^N) n`; `p:real`; `p':real`;
                 `sa:real`; `sb:real`] P2AJ_REPLACE_PIECE_X) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real->A` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Lam:real`)) (concl th) &&
    can (find_term ((=) `q:A`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The L-integral of a curve over a good piece in a box chart with a       *)
(* general top is the chart L-length of its chart curve.                    *)

let P2AJ_GOOD_LINT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b'' tt (gamma:real->A) b U (phi:A->real^N) (Y:real^1->real^N) p p' sa sb.
     p2a_svs V /\ p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < p /\ p < p' /\ p' pow 2 <= b /\ sa < p /\ p' < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b'') /\
     (!s. p <= s /\ s <= p'
          ==> Y(lift s) IN IMAGE phi (U INTER W) /\
              Y differentiable (at (lift s)) /\
              (\v. vector_derivative Y (at v)) continuous (at (lift s)) /\
              gamma(s pow 2) = chart_inv (U INTER W,phi) (Y(lift s)))
     ==> (p2a_L_integrand V tt gamma b has_real_integral
          p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt Y p p')
         (real_interval[p pow 2,p' pow 2])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `Y:real^1->real^N`; `p:real`; `p':real`;
                 `sa:real`; `sb:real`] P2A_CHART_SEG_LINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE_FINITE THEN
  MAP_EVERY EXISTS_TAC
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt
       (\tau. chart_inv (U INTER W,phi:A->real^N) ((Y:real^1->real^N)(lift(sqrt tau))))
       (p' pow 2)`;
    `{p pow 2,p' pow 2}`] THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  X_GEN_TAC `t:real` THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_REAL_INTERVAL; DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC P2A_LINT_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`p pow 2`; `p' pow 2`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
     [MP_TAC(SPEC `p:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sqrt s` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ASM_SIMP_TAC[SQRT_POW_2] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC];
      SIMP_TAC[]]]);;

(* Integrability on [0,b] and the bound, from the bounds on [t,b] and a    *)
(* lower bound of the integrand (monotone convergence).                    *)

let P2AJ_INT_FROM_EPS = prove
 (`!(f:real->real) b K Lam.
     &0 < b /\ &0 <= K /\
     (!tau. &0 <= tau /\ tau <= b ==> --K <= f tau) /\
     (!t. &0 < t /\ t < b
          ==> f real_integrable_on real_interval[t,b] /\
              real_integral (real_interval[t,b]) f <= Lam + K * t)
     ==> f real_integrable_on real_interval[&0,b] /\
         real_integral (real_interval[&0,b]) f <= Lam`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "LOW") (LABEL_TAC "EPS")))) THEN
  (* the increasing sequence of truncations *)
  ABBREV_TAC `tk = \k. b / &(k + 2)` THEN
  SUBGOAL_THEN
   `!k. &0 < (tk:num->real) k /\ tk k < b /\ tk (SUC k) <= tk k`
  (LABEL_TAC "TK") THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "tk" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &(k + 2) /\ &1 < &(k + 2) /\ &(k + 2) <= &(SUC k + 2)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      MP_TAC(ISPECL [`&1`; `&(k + 2)`; `b:real`] REAL_LT_RMUL) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 < t ==> ?N. !k. N <= k ==> (tk:num->real) k <= t` (LABEL_TAC "TK0") THENL
   [REPEAT STRIP_TAC THEN MP_TAC(SPEC `b / t` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN EXPAND_TAC "tk" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &(k + 2) /\ &N <= &(k + 2)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `b / t <= &N` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`&N`; `&(k + 2)`; `t:real`] REAL_LE_RMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `b <= &N * t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `fk = \k tau. if tau IN real_interval[(tk:num->real) k,b] then (f:real->real) tau + K
                 else &0` THEN
  SUBGOAL_THEN
   `!k. (fk:num->real->real) k real_integrable_on real_interval[&0,b] /\
        real_integral (real_interval[&0,b]) (fk k) =
        real_integral (real_interval[(tk:num->real) k,b]) f + K * (b - tk k)`
  (LABEL_TAC "FK") THENL
   [X_GEN_TAC `k:num` THEN
    USE_THEN "TK" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    USE_THEN "EPS" (MP_TAC o SPEC `(tk:num->real) k`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `real_interval[(tk:num->real) k,b] INTER real_interval[&0,b] =
                  real_interval[tk k,b]` ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(fk:num->real->real) k =
                  (\tau. if tau IN real_interval[(tk:num->real) k,b]
                         then (\tau. (f:real->real) tau + K) tau else &0)` SUBST1_TAC THENL
     [EXPAND_TAC "fk" THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_INTEGRABLE_RESTRICT_INTER; REAL_INTEGRAL_RESTRICT_INTER] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\tau. (f:real->real) tau + K) real_integrable_on real_interval[(tk:num->real) k,b]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST; ETA_AX];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real->real`; `\tau:real. (K:real)`; `real_interval[(tk:num->real) k,b]`]
                  REAL_INTEGRAL_ADD) THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* monotone convergence *)
  MP_TAC(ISPECL [`fk:num->real->real`; `\tau. (f:real->real) tau + K`; `real_interval[&0,b]`]
                REAL_MONOTONE_CONVERGENCE_INCREASING_AE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`k:num`; `tau:real`] THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN EXPAND_TAC "fk" THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      USE_THEN "TK" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
      USE_THEN "LOW" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
      X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_SING] THEN
      STRIP_TAC THEN MATCH_MP_TAC REALLIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      USE_THEN "TK0" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN EXPAND_TAC "fk" THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
      EXISTS_TAC `abs Lam + K * b` THEN X_GEN_TAC `k:num` THEN
      USE_THEN "FK" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "TK" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
      USE_THEN "EPS" (MP_TAC o SPEC `(tk:num->real) k`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `--K * (b - (tk:num->real) k) <= real_integral (real_interval[tk k,b]) f`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`(tk:num->real) k`; `b:real`; `--K`] REAL_INTEGRAL_CONST) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
        MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
        X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        USE_THEN "LOW" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MC")) THEN
  SUBGOAL_THEN `(f:real->real) real_integrable_on real_interval[&0,b]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\tau. (f:real->real) tau + K`; `\tau:real. (K:real)`; `real_interval[&0,b]`]
                  REAL_INTEGRABLE_SUB) THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    REWRITE_TAC[REAL_ARITH `(a + b) - b:real = a`; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\k. real_integral (real_interval[&0,b]) ((fk:num->real->real) k)`;
                 `real_integral (real_interval[&0,b]) (\tau. (f:real->real) tau + K)`;
                 `Lam + K * b`] REALLIM_UBOUND) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN
    USE_THEN "FK" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "TK" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    USE_THEN "EPS" (MP_TAC o SPEC `(tk:num->real) k`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `\tau:real. (K:real)`; `real_interval[&0,b]`] REAL_INTEGRAL_ADD) THEN
  ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC);;

(* Good pieces in box charts with a general top. *)

(* ------------------------------------------------------------------------- *)
(* A good piece in a box chart with a general top: along a subsequence of  *)
(* p2a_admx curves whose pieces converge in the chart (P2AJ_BOX_PIECE_LIMIT) *)
(* and are almost minimal against chart curves, the limit piece is the BVP  *)
(* solution between its end points, of chart L-length at most the liminf.   *)
(* ------------------------------------------------------------------------- *)

let P2AJ_GOOD_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' C T1 Fs R r lam Gm Rm tt (x:A) b (g:num->real->A) Lb Rm0 (gamma:real->A)
    eps sB sa sb p p' k N0 Eb delta rho (sol:real->real->real^N->real^N->real^1->real^N).
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     &0 <= Lb /\ &0 <= Rm0 /\ Rm <= Rm0 /\
     (!n. p2a_admx V tt x b (g n) /\ p2a_L_length V tt (g n) b <= Lb /\
          (!tau. &0 <= tau /\ tau <= b
                 ==> --(sqrt tau * Rm0) <= p2a_L_integrand V tt (g n) b tau)) /\
     &0 < eps /\ eps <= p /\ p < p' /\ p' <= sB /\ p' pow 2 <= b /\ k IN Fs /\
     sa < eps /\ sB < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     (!s. eps <= s /\ s <= sB ==> b' - T1 <= tt - s pow 2) /\
     (!n s. N0 <= n /\ p <= s /\ s <= p'
            ==> g n (s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
                dist(SND (chart_at (p2a_vatlas V b') k) (g n (s pow 2)),SND (chart_at (p2a_vatlas V b') k) k) <= &2 * R k) /\
     (!n s s'. N0 <= n /\ p <= s /\ s <= s' /\ s' <= p'
               ==> dist(SND (chart_at (p2a_vatlas V b') k) (g n (s' pow 2)),SND (chart_at (p2a_vatlas V b') k) (g n (s pow 2))) pow 2
                   <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0))) /\
     (!s. p <= s /\ s <= p'
          ==> gamma(s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
              dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2)),SND (chart_at (p2a_vatlas V b') k) k) <= &2 * R k /\
              ((\n. SND (chart_at (p2a_vatlas V b') k) (g n (s pow 2))) --> SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2))) sequentially) /\
     (!s s'. p <= s /\ s <= s' /\ s' <= p'
             ==> dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s' pow 2)),SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2))) pow 2
                 <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0))) /\
     p2ak_bvpd (ball(SND (chart_at (p2a_vatlas V b') k) k,&6 * R k)) (p2a_rlocal V W b' (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))) tt
               (cball(SND (chart_at (p2a_vatlas V b') k) k,&3 * R k)) Eb eps sB delta rho sol /\
     p' - p <= delta /\
     (p' - p) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0)) <= (rho / &2) pow 2 /\
     &2 / lam * (Lb + &4 * b * sqrt b * Rm0) <= Eb /\
     &2 * (&2 / lam * (Gm / &2 * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0)) +
                       &4 * sB pow 2 * Rm * (sB - eps))) <= Eb /\
     (!soln. (!n. N0 <= n
                  ==> g n (p pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\ g n (p' pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
                      soln n (lift p) = SND (chart_at (p2a_vatlas V b') k) (g n (p pow 2)) /\
                      soln n (lift p') = SND (chart_at (p2a_vatlas V b') k) (g n (p' pow 2)) /\
                      (!s. p <= s /\ s <= p'
                           ==> soln n (lift s) IN IMAGE (SND (chart_at (p2a_vatlas V b') k)) (FST (chart_at (p2a_vatlas V b') k) INTER W) /\
                               soln n differentiable (at (lift s)) /\
                               (\v. vector_derivative (soln n) (at v)) continuous (at (lift s))))
             ==> !e. &0 < e
                     ==> ?N. !n. N <= n
                             ==> real_integral (real_interval[p pow 2,p' pow 2])
                                   (p2a_L_integrand V tt (g n) b)
                                 <= p2a_cL (p2a_rlocal V W b' (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))) tt
                                           (soln n) p p' + e)
     ==> (!s. p <= s /\ s <= p'
              ==> sol p p' (SND (chart_at (p2a_vatlas V b') k) (gamma(p pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma(p' pow 2))) (lift s) IN
                  IMAGE (SND (chart_at (p2a_vatlas V b') k)) (FST (chart_at (p2a_vatlas V b') k) INTER W) /\
                  sol p p' (SND (chart_at (p2a_vatlas V b') k) (gamma(p pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma(p' pow 2)))
                    differentiable (at (lift s)) /\
                  (\v. vector_derivative (sol p p' (SND (chart_at (p2a_vatlas V b') k) (gamma(p pow 2)))
                                                   (SND (chart_at (p2a_vatlas V b') k) (gamma(p' pow 2)))) (at v))
                    continuous (at (lift s)) /\
                  gamma(s pow 2) =
                  chart_inv (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))
                    (sol p p' (SND (chart_at (p2a_vatlas V b') k) (gamma(p pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma(p' pow 2))) (lift s))) /\
         (!e. &0 < e
              ==> ?N. !n. N <= n
                          ==> p2a_cL (p2a_rlocal V W b' (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))) tt
                                (sol p p' (SND (chart_at (p2a_vatlas V b') k) (gamma(p pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma(p' pow 2))))
                                p p'
                              <= real_integral (real_interval[p pow 2,p' pow 2])
                                   (p2a_L_integrand V tt (g n) b) + e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm0)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b /\ &0 < p /\ &0 < (R:A->real) k /\ a' < b'` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `p':real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `p:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bvpd]) THEN
  FIRST_X_ASSUM(LABEL_TAC "C" o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `s1n:num->real`)) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "B" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
  ABBREV_TAC `ya = (phi:A->real^N)((gamma:real->A)(p pow 2))` THEN
  ABBREV_TAC `yb = (phi:A->real^N)((gamma:real->A)(p' pow 2))` THEN
  (* the limit end points and the main BVP solution *)
  SUBGOAL_THEN `ya IN cball((phi:A->real^N) k,&3 * (R:A->real) k) /\
                yb IN cball((phi:A->real^N) k,&3 * (R:A->real) k) /\
                norm((yb:real^N) - ya) <= rho /\ norm(yb - ya) pow 2 <= (p' - p) * E`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `p:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `p':real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`p:real`; `p':real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      not(can (find_term ((=) `g:num->real->A`)) (concl th)) &&
      can (find_term ((=) `E:real`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[dist] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_CBALL] THEN EXPAND_TAC "ya" THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(p pow 2))`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_CBALL] THEN EXPAND_TAC "yb" THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(p' pow 2))`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - p) * E` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rho / &2) pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "B" (MP_TAC o SPECL [`p:real`; `p':real`; `ya:real^N`; `yb:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  (* the s-form family on the ball and the bounds there *)
  SUBGOAL_THEN
   `p2a_lsmooth (ball((phi:A->real^N) k,&6 * (R:A->real) k)) sa sb
      (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AK_LSMOOTH_SUBSET THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2A_REGION_LSMOOTH THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((phi:A->real^N) k,&6 * (R:A->real) k)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y u. eps <= s /\ s <= sB /\ y IN ball((phi:A->real^N) k,&6 * (R:A->real) k)
            ==> lam * norm u pow 2 <=
                u dot (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi) (tt - s pow 2) y ** u) /\
                u dot (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi) (tt - s pow 2) y ** u)
                <= Gm * norm u pow 2 /\
                abs(lscalar (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi) (tt - s pow 2)) y) <= Rm`
  (LABEL_TAC "BD") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `T1:real`)) (concl th) &&
        can (find_term ((=) `sB:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  (* per-curve facts on sub-pieces *)
  SUBGOAL_THEN
   `!n s1 s2. p <= s1 /\ s1 < s2 /\ s2 <= p'
              ==> (?K. p2ak_sq (ball((phi:A->real^N) k,&6 * (R:A->real) k)) s1 s2
                         (\v. phi((g:num->real->A) (n + N0) (drop v pow 2)))
                         (\v. vector_derivative (\v. phi((g:num->real->A) (n + N0) (drop v pow 2))) (at v))
                         K (K INTER real_interval[s1,s2])) /\
                  (\s. p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi)) tt s (phi((g:num->real->A) (n + N0) (s pow 2)))
                         (vector_derivative (\v. phi((g:num->real->A) (n + N0) (drop v pow 2))) (at (lift s))))
                  real_integrable_on real_interval[s1,s2] /\
                  real_integral (real_interval[s1,s2])
                    (\s. p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi)) tt s (phi((g:num->real->A) (n + N0) (s pow 2)))
                           (vector_derivative (\v. phi((g:num->real->A) (n + N0) (drop v pow 2))) (at (lift s)))) =
                  real_integral (real_interval[s1 pow 2,s2 pow 2])
                    (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((g:num->real->A) (n + N0)) b) /\
                  real_integral (real_interval[s1,s2])
                    (\s. norm(vector_derivative (\v. phi((g:num->real->A) (n + N0) (drop v pow 2))) (at (lift s))) pow 2)
                  <= E`
  (LABEL_TAC "PC") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `n + N0:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th) &&
      can (find_term ((=) `Rm0:real`)) (concl th))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < s1 /\ s2 pow 2 <= b /\ sa < s1 /\ s2 < sb /\
                  (!s. s1 <= s /\ s <= s2 ==> b' - T1 <= tt - s pow 2) /\
                  (!s. s1 <= s /\ s <= s2
                       ==> (g:num->real->A) (n + N0) (s pow 2) IN U INTER W /\
                           (phi:A->real^N)(g (n + N0) (s pow 2)) IN
                           cball(phi k,&6 * (R:A->real) k))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p' pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `T1:real`)) (concl th) &&
          can (find_term ((=) `sB:real`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`n + N0:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `N0:num`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
        ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[IN_CBALL] THEN
        MP_TAC(ISPECL [`(phi:A->real^N) k`;
                       `(phi:A->real^N)((g:num->real->A) (n + N0) (s pow 2))`] DIST_SYM) THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `C:A->bool`; `T1:real`;
                   `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                   `tt:real`; `x:A`; `b:real`; `(g:num->real->A) (n + N0)`; `Lb:real`;
                   `Rm0:real`; `k:A`; `s1:real`; `s2:real`; `sa:real`; `sb:real`]
                  P2AJ_BXD_PIECE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `K:real->bool` THEN
    MATCH_MP_TAC P2AK_SQ_MONO THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    ASM_REWRITE_TAC[LIFT_DROP; IN_BALL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + N0:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`;
                   `(phi:A->real^N)((g:num->real->A) (n + N0) (s pow 2))`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* further per-curve facts *)
  SUBGOAL_THEN
   `!n s. p <= s /\ s <= p'
          ==> (phi:A->real^N)((g:num->real->A) (n + N0) (s pow 2)) IN cball(phi k,&3 * (R:A->real) k) /\
              (g:num->real->A) (n + N0) (s pow 2) IN U INTER W`
  (LABEL_TAC "KC") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + N0:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((g:num->real->A) (n + N0) (s pow 2))`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s s'. p <= s /\ s <= s' /\ s' <= p'
             ==> norm((phi:A->real^N)((g:num->real->A) (n + N0) (s' pow 2)) - phi((g:num->real->A) (n + N0) (s pow 2))) <= rho`
  (LABEL_TAC "NR") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + N0:num`; `s:real`; `s':real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term ((=) `E:real`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s' - s) * E` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - p) * E` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rho / &2) pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. p <= s /\ s <= p'
        ==> ((\n. (phi:A->real^N)((g:num->real->A) (n + N0) (s pow 2))) --> phi((gamma:real->A)(s pow 2))) sequentially`
  (LABEL_TAC "CV") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `e:real` THEN DISCH_TAC THEN
                         MP_TAC(SPEC `e:real` (CONJUNCT2(CONJUNCT2 th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!d. &0 <= d /\ d pow 2 <= (p' - p) * E ==> d <= rho` (LABEL_TAC "SQR") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - p) * E` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rho / &2) pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* almost-minimality of the sequence on the piece *)
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N. !n. N <= n
                    ==> real_integral (real_interval[p pow 2,p' pow 2])
                          (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((g:num->real->A) n) b)
                        <= p2a_cL (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)) tt
                             ((sol:real->real->real^N->real^N->real^1->real^N) p p'
                                (phi((g:num->real->A) n (p pow 2))) (phi((g:num->real->A) n (p' pow 2)))) p p' + e`
  (LABEL_TAC "AM") THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC
      `\n. (sol:real->real->real^N->real^N->real^1->real^N) p p'
             ((phi:A->real^N)((g:num->real->A) n (p pow 2))) (phi((g:num->real->A) n (p' pow 2)))` o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_var t && fst(dest_var t) = "soln")) (concl th))) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `p:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `p':real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `p:real`; `p':real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term ((=) `E:real`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; REWRITE_TAC[dist] THEN DISCH_TAC] THEN
    SUBGOAL_THEN `norm((phi:A->real^N)((g:num->real->A) n (p' pow 2)) - phi((g:num->real->A) n (p pow 2))) <= rho`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - p) * E` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rho / &2) pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "B" (MP_TAC o SPECL [`p:real`; `p':real`; `(phi:A->real^N)((g:num->real->A) n (p pow 2))`;
                                  `(phi:A->real^N)((g:num->real->A) n (p' pow 2))`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_CBALL] THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((g:num->real->A) n (p pow 2))`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th) &&
      can (find_term ((=) `(g:num->real->A) n`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `(g:num->real->A) n`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; DISCH_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
      ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL];
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE);
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT o
                  MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE)];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th) &&
      can (find_term ((=) `ya:real^N`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ya:real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; DISCH_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
      ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL];
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE);
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT o
                  MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE);
      ALL_TAC] THEN
    SUBGOAL_THEN `(phi:A->real^N)((gamma:real->A)(s pow 2)) = (sol:real->real->real^N->real^N->real^1->real^N) p p' ya yb (lift s)`
    (SUBST1_TAC o SYM) THENL
     [ASM_CASES_TAC `s:real = p` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `s:real = p'` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `p < s /\ s < p'` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`p:real`; `s:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th) &&
        not(can (find_term ((=) `g:num->real->A`)) (concl th)) &&
        can (find_term ((=) `E:real`)) (concl th))) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; ASM_REWRITE_TAC[dist] THEN DISCH_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `p':real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th) &&
        not(can (find_term ((=) `g:num->real->A`)) (concl th)) &&
        can (find_term ((=) `E:real`)) (concl th))) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; ASM_REWRITE_TAC[dist] THEN DISCH_TAC] THEN
      MP_TAC(ISPECL
        [`ball((phi:A->real^N) k,&6 * (R:A->real) k)`;
         `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)`; `tt:real`;
         `cball((phi:A->real^N) k,&3 * (R:A->real) k)`; `Eb:real`; `eps:real`; `sB:real`;
         `delta:real`; `rho:real`; `sol:real->real->real^N->real^N->real^1->real^N`;
         `sa:real`; `sb:real`; `lam:real`; `Gm:real`; `Rm:real`; `E:real`;
         `\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`;
         `\n:num v:real^1. (phi:A->real^N)((g:num->real->A) (n + N0) (drop v pow 2))`;
         `p:real`; `s:real`; `p':real`] P2AK_UNIQ_CHART) THEN
      REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[CONVEX_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_CBALL] THEN
        MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(s pow 2))`] DIST_SYM) THEN
        ASM_REAL_ARITH_TAC;
        USE_THEN "SQR" MATCH_MP_TAC THEN REWRITE_TAC[NORM_POS_LE] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s - p) * E` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        USE_THEN "SQR" MATCH_MP_TAC THEN REWRITE_TAC[NORM_POS_LE] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - s) * E` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= a * b ==> x <= b * a`) THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= a * b ==> x <= b * a`) THEN FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `n:num` THEN REPEAT CONJ_TAC THENL
         [USE_THEN "KC" (MP_TAC o SPECL [`n:num`; `p:real`]) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          USE_THEN "KC" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          USE_THEN "NR" (MP_TAC o SPECL [`n:num`; `p:real`; `p':real`]) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          USE_THEN "NR" (MP_TAC o SPECL [`n:num`; `p:real`; `s:real`]) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          USE_THEN "NR" (MP_TAC o SPECL [`n:num`; `s:real`; `p':real`]) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
        X_GEN_TAC `n:num` THEN
        USE_THEN "PC" (MP_TAC o SPECL [`n:num`; `p:real`; `s:real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `K1:real->bool`) STRIP_ASSUME_TAC) THEN
        USE_THEN "PC" (MP_TAC o SPECL [`n:num`; `s:real`; `p':real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `K2:real->bool`) STRIP_ASSUME_TAC) THEN
        USE_THEN "PC" (MP_TAC o SPECL [`n:num`; `p:real`; `p':real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `K3:real->bool`) STRIP_ASSUME_TAC) THEN
        REPEAT CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`K1:real->bool`; `(K1:real->bool) INTER real_interval[p,s]`] THEN
          ASM_REWRITE_TAC[];
          MAP_EVERY EXISTS_TAC [`K2:real->bool`; `(K2:real->bool) INTER real_interval[s,p']`] THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E:real` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E:real` THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]];
        USE_THEN "CV" (MP_TAC o SPEC `p:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        USE_THEN "CV" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        USE_THEN "CV" (MP_TAC o SPEC `p':real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        USE_THEN "AM" (MP_TAC o SPEC `e:real`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `N:num`)] THEN
        EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        USE_THEN "PC" (MP_TAC o SPECL [`n:num`; `p:real`; `p':real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `K3:real->bool`) STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `N:num`)) (concl th))) THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `a':real`; `b':real`] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the BVP length between the limit end points is at most the liminf *)
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. (phi:A->real^N)((g:num->real->A) (n + N0) (p pow 2)) IN
          cball(phi k,&3 * (R:A->real) k) /\
        norm(phi(g(n + N0)(p' pow 2)) - phi(g(n + N0)(p pow 2))) <= rho`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN CONJ_TAC THENL
     [USE_THEN "KC" (MP_TAC o SPECL [`n:num`; `p:real`]) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "NR" (MP_TAC o SPECL [`n:num`; `p:real`; `p':real`]) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. (phi:A->real^N)((g:num->real->A) (n + N0) (p pow 2))) --> ya)
    sequentially /\
    ((\n. (phi:A->real^N)((g:num->real->A) (n + N0) (p' pow 2))) --> yb)
    sequentially`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "CV" (MP_TAC o SPEC `p:real`) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; ASM_REWRITE_TAC[]];
      USE_THEN "CV" (MP_TAC o SPEC `p':real`) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  USE_THEN "C" (MP_TAC o SPECL [`p:real`; `p':real`; `ya:real^N`; `yb:real^N`;
     `\n:num. (p:real)`; `\n:num. (p':real)`;
     `\n. (phi:A->real^N)((g:num->real->A) (n + N0) (p pow 2))`;
     `\n. (phi:A->real^N)((g:num->real->A) (n + N0) (p' pow 2))`]) THEN
  REWRITE_TAC[LIM_CONST] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + N0:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N0 <= n:num /\ (n - N0) + N0 = n:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `N + N0 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - N0:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N:num`)) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `N + N0 <= n:num` THEN ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  USE_THEN "PC" (MP_TAC o SPECL [`n - N0:num`; `p:real`; `p':real`]) THEN
  ANTS_TAC THENL [P2AK_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `K:real->bool`) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `p:real`] o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N0:num`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
  ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `p:real`; `p':real`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `N0:num`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
    can (find_term ((=) `E:real`)) (concl th))) THEN
  ANTS_TAC THENL [P2AK_ARITH_TAC; REWRITE_TAC[dist] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`ball((phi:A->real^N) k,&6 * (R:A->real) k)`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)`; `tt:real`;
                 `cball((phi:A->real^N) k,&3 * (R:A->real) k)`; `Eb:real`; `eps:real`; `sB:real`;
                 `delta:real`; `rho:real`; `sol:real->real->real^N->real^N->real^1->real^N`;
                 `sa:real`; `sb:real`; `p:real`; `p':real`;
                 `\v:real^1. (phi:A->real^N)((g:num->real->A) n (drop v pow 2))`;
                 `\v. vector_derivative
                        (\v:real^1. (phi:A->real^N)((g:num->real->A) n (drop v pow 2)))
                        (at v)`;
                 `K:real->bool`; `(K:real->bool) INTER real_interval[p,p']`] P2AK_BVPD_LE) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_CBALL] THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`;
                     `(phi:A->real^N)((g:num->real->A) n (p pow 2))`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "SQR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E:real` THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;



(* The same with the almost-minimality from a minimizing sequence.        *)

let P2AJ_GOOD_PIECE_MIN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' C T1 Fs R r lam Gm Rm tt (x:A) b (g:num->real->A) Lb Rm0 (gamma:real->A)
    eps sB sa sb p p' k N0 Eb delta rho (sol:real->real->real^N->real^N->real^1->real^N) q Lam.
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     &0 <= Lb /\ &0 <= Rm0 /\ Rm <= Rm0 /\
     (!n. p2a_admx V tt x b (g n) /\ p2a_L_length V tt (g n) b <= Lb /\
          (!tau. &0 <= tau /\ tau <= b
                 ==> --(sqrt tau * Rm0) <= p2a_L_integrand V tt (g n) b tau)) /\
     &0 < eps /\ eps <= p /\ p < p' /\ p' <= sB /\ p' pow 2 <= b /\ k IN Fs /\
     sa < eps /\ sB < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 < b') /\
     (!s. eps <= s /\ s <= sB ==> b' - T1 <= tt - s pow 2) /\
     (!n s. N0 <= n /\ p <= s /\ s <= p'
            ==> g n (s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
                dist(SND (chart_at (p2a_vatlas V b') k) (g n (s pow 2)),SND (chart_at (p2a_vatlas V b') k) k) <= &2 * R k) /\
     (!n s s'. N0 <= n /\ p <= s /\ s <= s' /\ s' <= p'
               ==> dist(SND (chart_at (p2a_vatlas V b') k) (g n (s' pow 2)),SND (chart_at (p2a_vatlas V b') k) (g n (s pow 2))) pow 2
                   <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0))) /\
     (!s. p <= s /\ s <= p'
          ==> gamma(s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
              dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2)),SND (chart_at (p2a_vatlas V b') k) k) <= &2 * R k /\
              ((\n. SND (chart_at (p2a_vatlas V b') k) (g n (s pow 2))) --> SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2))) sequentially) /\
     (!s s'. p <= s /\ s <= s' /\ s' <= p'
             ==> dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s' pow 2)),SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2))) pow 2
                 <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0))) /\
     p2ak_bvpd (ball(SND (chart_at (p2a_vatlas V b') k) k,&6 * R k)) (p2a_rlocal V W b' (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))) tt
               (cball(SND (chart_at (p2a_vatlas V b') k) k,&3 * R k)) Eb eps sB delta rho sol /\
     p' - p <= delta /\
     (p' - p) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0)) <= (rho / &2) pow 2 /\
     &2 / lam * (Lb + &4 * b * sqrt b * Rm0) <= Eb /\
     &2 * (&2 / lam * (Gm / &2 * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0)) +
                       &4 * sB pow 2 * Rm * (sB - eps))) <= Eb /\
     (!n. g n b = q) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> p2a_L_length V tt (g n) b <= Lam + e) /\
     (!gamma'. p2a_admx V tt x b gamma' /\ gamma' b = q
               ==> Lam <= p2a_L_length V tt gamma' b)
     ==> (!s. p <= s /\ s <= p'
              ==> sol p p' (SND (chart_at (p2a_vatlas V b') k) (gamma(p pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma(p' pow 2))) (lift s) IN
                  IMAGE (SND (chart_at (p2a_vatlas V b') k)) (FST (chart_at (p2a_vatlas V b') k) INTER W) /\
                  sol p p' (SND (chart_at (p2a_vatlas V b') k) (gamma(p pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma(p' pow 2)))
                    differentiable (at (lift s)) /\
                  (\v. vector_derivative (sol p p' (SND (chart_at (p2a_vatlas V b') k) (gamma(p pow 2)))
                                                   (SND (chart_at (p2a_vatlas V b') k) (gamma(p' pow 2)))) (at v))
                    continuous (at (lift s)) /\
                  gamma(s pow 2) =
                  chart_inv (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))
                    (sol p p' (SND (chart_at (p2a_vatlas V b') k) (gamma(p pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma(p' pow 2))) (lift s))) /\
         (!e. &0 < e
              ==> ?N. !n. N <= n
                          ==> p2a_cL (p2a_rlocal V W b' (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))) tt
                                (sol p p' (SND (chart_at (p2a_vatlas V b') k) (gamma(p pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma(p' pow 2))))
                                p p'
                              <= real_integral (real_interval[p pow 2,p' pow 2])
                                   (p2a_L_integrand V tt (g n) b) + e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b'`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!soln. (!n. N0 <= n
                ==> (g:num->real->A) n (p pow 2) IN FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A)) INTER W /\
                    g n (p' pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
                    soln n (lift p) = SND (chart_at (p2a_vatlas V b') k) (g n (p pow 2)) /\
                    soln n (lift p') = SND (chart_at (p2a_vatlas V b') k) (g n (p' pow 2)) /\
                    (!s. p <= s /\ s <= p'
                         ==> soln n (lift s) IN IMAGE (SND (chart_at (p2a_vatlas V b') k)) (FST (chart_at (p2a_vatlas V b') k) INTER W) /\
                             soln n differentiable (at (lift s)) /\
                             (\v. vector_derivative (soln n) (at v)) continuous (at (lift s))))
           ==> !e. &0 < e
                   ==> ?N. !n. N <= n
                           ==> real_integral (real_interval[p pow 2,p' pow 2])
                                 (p2a_L_integrand V tt (g n) b)
                               <= p2a_cL (p2a_rlocal V W b' (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))) tt
                                         (soln n) p p' + e`
  ASSUME_TAC THENL
   [X_GEN_TAC `soln:num->real^1->real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2AJ_ALMOST_MIN THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `q:A`; `Lam:real`; `a':real`; `N0:num`; `sa:real`; `sb:real`] THEN
    ASM_REWRITE_TAC[PAIR] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC_ALL P2AJ_GOOD_PIECE) THEN ASM_REWRITE_TAC[]);;

(* The multi-box minimizing datum and good pieces of the limit. *)

(* ------------------------------------------------------------------------- *)
(* The multi-box minimizing datum and good pieces of the limit curve: near  *)
(* every time s0 > 0 the pieces of the limit lie in one box chart and are   *)
(* BVP solutions there (P2AJ_LOCAL_GOOD), uniformly on [eps,sqrt tau0]     *)
(* (P2AJ_MB_GOOD).                                                          *)
(* ------------------------------------------------------------------------- *)

let p2aj_lim = new_definition
 `p2aj_lim (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
           (tt:real) (x:A) (nb:num) (W:num->A->bool) (A0:num->real) (a:num->real)
           (b:num->real) (C:num->A->bool) (eta:real) (Fs:num->A->bool) (R:num->A->real)
           (r:real) (lam:real) (Gm:real) (Rm:real) (tau0:real) (gs:num->real->A) (Lb:real)
           (q:A) (sub:num->num) (gamma:real->A) (Lam:real) <=>
    p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ &0 <= Lb /\ &0 < tau0 /\
    (!n. p2a_admx V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
         !tau. &0 < tau /\ tau <= tau0
               ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gs n tau IN C j) /\
    (!n. gs n tau0 = q) /\
    p3_subseq sub /\ gamma (&0) = x /\
    (!tau. &0 <= tau /\ tau <= tau0
           ==> gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
               !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                   ==> ?N. !n. N <= n ==> gs (sub n) tau IN O) /\
    (!e. &0 < e ==> ?N. !n. N <= n ==> p2a_L_length V tt (gs (sub n)) tau0 <= Lam + e) /\
    (!gamma'. p2a_admx V tt x tau0 gamma' /\ gamma' tau0 = q
              ==> Lam <= p2a_L_length V tt gamma' tau0)`;;

(* A good piece [p,p'] of the limit curve: in a box chart (strict window),  *)
(* the limit is chart_inv of a C^1 chart curve whose chart L-length is at   *)
(* most the liminf of the L-integrals of the sequence over the piece.       *)

let p2aj_good = new_definition
 `p2aj_good (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
            (tt:real) (nb:num) (W:num->A->bool) (A0:num->real) (b:num->real) (tau0:real)
            (gs:num->real->A) (sub:num->num) (gamma:real->A) (p:real) (p':real) <=>
    ?j U phi (Y:real^1->real^N).
      j <= nb /\ (U,phi) IN p2a_vatlas V (b j) /\
      (?sa sb. sa < p /\ p' < sb /\
               !s. sa < s /\ s < sb ==> A0 j < tt - s pow 2 /\ tt - s pow 2 < b j) /\
      (!s. p <= s /\ s <= p'
           ==> Y(lift s) IN IMAGE phi (U INTER W j) /\
               Y differentiable (at (lift s)) /\
               (\v. vector_derivative Y (at v)) continuous (at (lift s)) /\
               gamma(s pow 2) = chart_inv (U INTER W j,phi) (Y(lift s))) /\
      (!e. &0 < e
           ==> ?N. !n. N <= n
                   ==> p2a_cL (p2a_rlocal V (W j) (b j) (U INTER W j,phi)) tt Y p p'
                       <= real_integral (real_interval[p pow 2,p' pow 2])
                            (p2a_L_integrand V tt (gs (sub n)) tau0) + e)`;;

(* Squares near s0 > 0.                                                       *)

let P2AJ_SQ_NBHD = prove
 (`!s0 d. &0 < s0 /\ &0 < d
          ==> ?r1. &0 < r1 /\ r1 <= s0 /\
                   !p. abs(p - s0) < r1 ==> abs(p pow 2 - s0 pow 2) < d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < d / (&3 * s0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min s0 (d / (&3 * s0))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `p:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `p pow 2 - s0 pow 2 = (p - s0) * (p + s0)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(p - s0) * (&3 * s0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `d / (&3 * s0) * (&3 * s0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `d / (&3 * s0) * (&3 * s0) = d` (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
    MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC]);;

(* A positive radius below six bounds.                                       *)

let P2AJ_RR_CHOICE = prove
 (`!c1 c2 c3 c4 c5 c6 E.
     &0 < c1 /\ &0 < c2 /\ &0 < c3 /\ &0 < c4 /\ &0 < c5 /\ &0 < c6 /\ &0 <= E
     ==> ?rr. &0 < rr /\ rr <= c1 /\ rr <= c2 /\ rr <= c3 /\ &2 * rr <= c4 /\
              &2 * rr * (E + &1) <= c5 /\ &2 * rr * (E + &1) <= c6`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * (E + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c5 / (&2 * (E + &1)) /\ &0 < c6 / (&2 * (E + &1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?m. &0 < m /\ m <= c1 /\ m <= c2 /\ m <= c3 /\ m <= c4 / &2 /\
        m <= c5 / (&2 * (E + &1)) /\ m <= c6 / (&2 * (E + &1))`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min c1 (min c2 (min c3 (min (c4 / &2)
                  (min (c5 / (&2 * (E + &1))) (c6 / (&2 * (E + &1)))))))` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&2 * m * (E + &1) = m * (&2 * (E + &1))`] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]);;

(* The box chart around the limit point at a time s0^2 > 0: a box below its *)
(* top with a window of times strictly inside, and a radius of s around s0  *)
(* on which the limit stays in the chart ball of radius R (continuity).     *)

let P2AJ_LOCAL_BOX = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gs:num->real->A) Lb tau0 sub gamma s0.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ &0 <= Lb /\ &0 < tau0 /\
     (!n. p2a_admx V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
          !tau. &0 < tau /\ tau <= tau0
                ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gs n tau IN C j) /\
     p3_subseq sub /\
     (!tau. &0 <= tau /\ tau <= tau0
            ==> gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
                !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                    ==> ?N. !n. N <= n ==> gs (sub n) tau IN O) /\
     &0 < s0 /\ s0 pow 2 <= tau0
     ==> ?j k sa sb r1.
           j < nb /\ k IN Fs j /\ &0 < sa /\ sa < s0 /\ s0 < sb /\
           (!s. sa < s /\ s < sb ==> a j - eta / &2 < tt - s pow 2 /\ tt - s pow 2 < b j) /\
           &0 < r1 /\
           !p. abs(p - s0) < r1 /\ p pow 2 <= tau0
               ==> gamma(p pow 2) IN FST(chart_at (p2a_vatlas V (b j)) k) INTER W j /\
                   dist(SND(chart_at (p2a_vatlas V (b j)) k) (gamma(p pow 2)),
                        SND(chart_at (p2a_vatlas V (b j)) k) k) < R j k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  SUBGOAL_THEN `&0 < s0 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `gs:num->real->A`; `Lb:real`; `tau0:real`; `sub:num->num`;
                 `gamma:real->A`; `s0 pow 2`] P2AJ_LIM_STRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd] o check (fun th ->
    not(is_forall(concl th)) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(gamma:real->A)(s0 pow 2)` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
    can (find_term ((=) `(C:num->A->bool) j`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the window *)
  MP_TAC(ISPECL [`tt:real`; `(a:num->real) j - eta / &2`; `(b:num->real) j`; `s0:real`;
                 `s0:real`] P2AJ_WINDOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sa1:real` (X_CHOOSE_THEN `sb1:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:real`; `(a:num->real) j - eta / &2`; `(b:num->real) j`; `s0:real`;
                 `s0:real`; `sa1:real`; `sb1:real`] P2AJ_WINDOW_STRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sa2:real` STRIP_ASSUME_TAC) THEN
  (* continuity in the chart *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))`; `SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))`; `tt - s0 pow 2`; `(gamma:real->A)(s0 pow 2)`;
                 `(R:num->A->real) j k - dist(SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) ((gamma:real->A)(s0 pow 2)),SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k)`]
                P2A_CHART_PREIMAGE_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PAIR] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `gs:num->real->A`; `Lb:real`; `tau0:real`; `sub:num->num`;
                 `gamma:real->A`; `s0 pow 2`; `O:A->bool`] P2AJ_MB_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`s0:real`; `d:real`] P2AJ_SQ_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)] THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `k:A`; `sa2:real`; `sb1:real`; `r1:real`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p pow 2` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `d:real`)) (concl th) && can (find_term ((=) `O:A->bool`)) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `r1:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(gamma:real->A)(p pow 2)` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `O:A->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) ((gamma:real->A)(p pow 2))`; `SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) ((gamma:real->A)(s0 pow 2))`;
                 `SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k`] DIST_TRIANGLE) THEN
  ASM_REAL_ARITH_TAC);;

(* Near every time s0 > 0 the short pieces of the limit curve are good.     *)

let P2AJ_LOCAL_GOOD = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam s0.
     p2aj_lim V tt x nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam /\
     &0 < s0 /\ s0 pow 2 <= tau0
     ==> ?rr. &0 < rr /\
              !p p'. s0 - rr < p /\ p <= p' /\ p' < s0 + rr
                     ==> p < p' /\ p' pow 2 <= tau0
                         ==> p2aj_good V tt nb W A0 b tau0 gs sub gamma p p'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_lim]) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `gs:num->real->A`; `Lb:real`; `tau0:real`; `sub:num->num`;
                 `gamma:real->A`; `s0:real`] P2AJ_LOCAL_BOX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `k:A` (X_CHOOSE_THEN `sa:real`
    (X_CHOOSE_THEN `sb:real` (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd] o check (fun th ->
    not(is_forall(concl th)) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the s-range of the BVP data and the windows *)
  SUBGOAL_THEN `?sA sB. sa < sA /\ sA < s0 /\ s0 < sB /\ sB < sb` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`(sa + s0) / &2`; `(s0 + sb) / &2`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!s. sa < s /\ s < sb ==> (A0:num->real) j < tt - s pow 2 /\ tt - s pow 2 < (b:num->real) j) /\
    (!s. sa < s /\ s < sb ==> A0 j < tt - s pow 2 /\ tt - s pow 2 <= b j) /\
    (!s. sA <= s /\ s <= sB ==> b j - (b j - (a:num->real) j + eta / &2) <= tt - s pow 2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th) && can (find_term ((=) `eta:real`)) (concl th))) THEN
    ANTS_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?Eb. &0 < Eb /\ (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) <= Eb /\
         &2 * (&2 / lam * (Gm / &2 * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) + &4 * sB pow 2 * Rm * (sB - sA))) <= Eb`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) + abs(&2 * (&2 / lam * (Gm / &2 * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) + &4 * sB pow 2 * Rm * (sB - sA)))) + &1` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `(C:num->A->bool) j`; `(b:num->real) j - (a:num->real) j + eta / &2`;
                 `(Fs:num->A->bool) j`; `(R:num->A->real) j`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `tt:real`; `k:A`; `Eb:real`; `sA:real`; `sB:real`] P2AJ_BOX_BVP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `sA:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th) && can (find_term ((=) `eta:real`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SPEC `sB:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th) && can (find_term ((=) `eta:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `delta:real` (X_CHOOSE_THEN `rho:real`
      (X_CHOOSE_THEN `sol:real->real->real^N->real^N->real^1->real^N` ASSUME_TAC)))] THEN
  SUBGOAL_THEN `&0 < delta /\ &0 < rho` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bvpd")) (concl th))) THEN
    REWRITE_TAC[p2ak_bvpd] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`s0 - sA`; `sB - s0`; `r1:real`; `delta:real`; `(rho / &2) pow 2`; `r pow 2`;
                `(&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm))`] P2AJ_RR_CHOICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `rr:real` STRIP_ASSUME_TAC)] THEN
  (* a short piece near s0 *)
  EXISTS_TAC `rr:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `p':real`] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 < p /\ sA < p /\ sA <= p /\ p' < sB /\ p' <= sB /\ sa < p /\ p' < sb /\ &0 <= p /\
    p pow 2 <= tau0 /\ abs(p - s0) < r1 /\ p' - p <= delta /\
    (p' - p) * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) <= (rho / &2) pow 2 /\ (p' - p) * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) <= r pow 2 /\ &0 < sA`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(p' - p) * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) <= &2 * rr * ((&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * rr) * ((&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `p pow 2 <= p' pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x tau0 ((gs:num->real->A) ((sub:num->num) n)) /\
        p2a_L_length V tt (gs (sub n)) tau0 <= Lb /\
        (!tau. &0 <= tau /\ tau <= tau0
               ==> --(sqrt tau * Rm) <= p2a_L_integrand V tt (gs (sub n)) tau0 tau)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th) &&
      not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2AJ_MB_LINT_LOWER THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`; `a:num->real`;
                          `b:num->real`; `C:num->A->bool`; `eta:real`; `Fs:num->A->bool`;
                          `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `(sub:num->num) n`)) (concl th) &&
      can (find_term ((=) `C:num->A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. p <= s /\ s <= p'
        ==> (gamma:real->A)(s pow 2) IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2)) /\
            !O. open_in (p2a_vtop V (tt - s pow 2)) O /\ gamma(s pow 2) IN O
                ==> ?N. !n. N <= n ==> (gs:num->real->A) ((sub:num->num) n) (s pow 2) IN O`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p' pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(gamma:real->A)(p pow 2) IN FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) INTER (W:num->A->bool) j /\
    dist(SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) (gamma(p pow 2)),SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k) < (R:num->A->real) j k`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `r1:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. p <= s /\ s <= p' ==> (b:num->real) j - (b j - (a:num->real) j + eta / &2) <= tt - s pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sB:real`)) (concl th) && can (find_term ((=) `eta:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the piece limit in the box chart, then the good piece *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `(C:num->A->bool) j`; `(b:num->real) j - (a:num->real) j + eta / &2`;
                 `(Fs:num->A->bool) j`; `(R:num->A->real) j`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `tt:real`; `x:A`; `tau0:real`; `gs:num->real->A`; `Lb:real`;
                 `Rm:real`; `sub:num->num`; `gamma:real->A`; `k:A`; `p:real`; `p':real`;
                 `sa:real`; `sb:real`] P2AJ_BOX_PIECE_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `(C:num->A->bool) j`; `(b:num->real) j - (a:num->real) j + eta / &2`;
                 `(Fs:num->A->bool) j`; `(R:num->A->real) j`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `tt:real`; `x:A`; `tau0:real`;
                 `\n. (gs:num->real->A) ((sub:num->num) n)`; `Lb:real`; `Rm:real`;
                 `gamma:real->A`; `sA:real`; `sB:real`; `sa:real`; `sb:real`; `p:real`;
                 `p':real`; `k:A`; `N0:num`; `Eb:real`; `delta:real`; `rho:real`;
                 `sol:real->real->real^N->real^N->real^1->real^N`; `q:A`; `Lam:real`]
                P2AJ_GOOD_PIECE_MIN) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  REWRITE_TAC[p2aj_good] THEN
  MAP_EVERY EXISTS_TAC
   [`j:num`; `FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))`; `SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))`;
    `(sol:real->real->real^N->real^N->real^1->real^N) p p'
       (SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) ((gamma:real->A)(p pow 2))) (SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) (gamma(p' pow 2)))`] THEN
  ASM_REWRITE_TAC[PAIR] THEN
  CONJ_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sa:real`; `sb:real`] THEN ASM_REWRITE_TAC[]);;

(* Uniformly on [eps,sqrt tau0]: all short pieces of the limit are good.     *)

let P2AJ_MB_GOOD = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam eps.
     p2aj_lim V tt x nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam /\
     &0 < eps /\ eps <= sqrt tau0
     ==> ?h. &0 < h /\
             !p p'. eps <= p /\ p < p' /\ p' <= sqrt tau0 /\ p' - p <= h
                    ==> p2aj_good V tt nb W A0 b tau0 gs sub gamma p p'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_lim]) THEN
  MP_TAC(ISPECL [`\p p'. p < p' /\ p' pow 2 <= tau0
                         ==> p2aj_good (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt nb (W:num->A->bool) A0 b tau0 gs sub gamma p p'`;
                 `eps:real`; `sqrt tau0`] P2AJ_LOCAL_UNIFORM) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `s0:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                   `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                   `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                   `Rm:real`; `tau0:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`;
                   `gamma:real->A`; `Lam:real`; `s0:real`] P2AJ_LOCAL_GOOD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt tau0 pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `p':real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:real`; `p':real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt tau0 pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]]);;

(* MT Lemma 7.2(c) for the multi-box datum. *)

(* ------------------------------------------------------------------------- *)
(* MT Lemma 7.2(c) for p2a_admx minimizing sequences in the boxes: the     *)
(* L-integral of the limit over [eps^2,tau0], integrability on [0,tau0]    *)
(* and L-length at most the infimum, no corners, admissibility, minimality. *)
(* ------------------------------------------------------------------------- *)

(* The region and the time bounds of a box.                                  *)

let P2AJ_MB_REGION = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm j.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ j <= nb
     ==> p2a_svs V /\ p2a_region V (W j) (A0 j) (b j) /\ A0 j + eta <= a j /\ a j <= b j /\
         C j SUBSET W j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2ak_bxd] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ASM_SIMP_TAC[]);;

(* A strict window is a window.                                               *)

let P2AJ_WINDOW_WEAK = prove
 (`!tt A0 b' sa sb.
     (!s. sa < s /\ s < sb ==> A0 < tt - s pow 2 /\ tt - s pow 2 < b')
     ==> (!s. sa < s /\ s < sb ==> A0 < tt - s pow 2 /\ tt - s pow 2 <= b')`,
  MESON_TAC[REAL_LT_IMP_LE]);;

(* The L-integral of the limit over a good piece and its liminf bound.       *)

let P2AJ_GOOD_INT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm tau0 (gs:num->real->A) sub gamma p p'.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\
     p2aj_good V tt nb W A0 b tau0 gs sub gamma p p' /\
     &0 < p /\ p < p' /\ p' pow 2 <= tau0
     ==> p2a_L_integrand V tt gamma tau0 real_integrable_on real_interval[p pow 2,p' pow 2] /\
         !e. &0 < e
             ==> ?N. !n. N <= n
                     ==> real_integral (real_interval[p pow 2,p' pow 2])
                           (p2a_L_integrand V tt gamma tau0)
                         <= real_integral (real_interval[p pow 2,p' pow 2])
                              (p2a_L_integrand V tt (gs (sub n)) tau0) + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2aj_good] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aj_good")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (X_CHOOSE_THEN `Y:real^1->real^N` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `j:num`] P2AJ_MB_REGION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AJ_WINDOW_WEAK) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `tt:real`; `gamma:real->A`; `tau0:real`; `U:A->bool`; `phi:A->real^N`;
                 `Y:real^1->real^N`; `p:real`; `p':real`; `sa:real`; `sb:real`]
                P2AJ_GOOD_LINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[real_integrable_on]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  ASM_REWRITE_TAC[]);;

(* The L-integral of the limit over [eps^2,tau0].                            *)

let P2AJ_MB_EPS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam eps.
     p2aj_lim V tt x nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam /\
     &0 < eps /\ eps < sqrt tau0
     ==> p2a_L_integrand V tt gamma tau0 real_integrable_on real_interval[eps pow 2,tau0] /\
         real_integral (real_interval[eps pow 2,tau0]) (p2a_L_integrand V tt gamma tau0)
         <= Lam + sqrt tau0 * Rm * eps pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_lim]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `tau0:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`;
                 `gamma:real->A`; `Lam:real`; `eps:real`] P2AJ_MB_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < sqrt tau0 /\ sqrt tau0 pow 2 = tau0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eps pow 2 /\ eps pow 2 <= tau0` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt tau0 pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n tau. &0 <= tau /\ tau <= tau0
                        ==> --(sqrt tau * Rm) <=
                            p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) n) tau0 tau`
  (LABEL_TAC "LOW") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AJ_MB_LINT_LOWER THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`; `a:num->real`;
                          `b:num->real`; `C:num->A->bool`; `eta:real`; `Fs:num->A->bool`;
                          `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th) &&
      not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) tau0`;
                 `\n. p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) ((sub:num->num) n)) tau0`;
                 `eps:real`; `sqrt tau0`; `h:real`] P2AK_PARTITION_LIM) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN
      FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th) &&
        not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
      REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `tau0:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      REWRITE_TAC[REAL_LE_POW_2; REAL_LE_REFL];
      MAP_EVERY X_GEN_TAC [`p:real`; `p':real`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                     `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                     `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                     `Rm:real`; `tau0:real`; `gs:num->real->A`; `sub:num->num`;
                     `gamma:real->A`; `p:real`; `p':real`] P2AJ_GOOD_INT) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `h:real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt tau0 pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIM")) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AK_LE_ADD_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "LIM" (MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `e / &2` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Lam:real`)) (concl th) &&
    can (find_term ((=) `sub:num->num`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "real_lt")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N1:num`)) (concl th))) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N2:num`)) (concl th))) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) (N1 + N2)` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th) &&
    not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
  REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) ((sub:num->num) (N1 + N2))) tau0`;
                 `&0`; `tau0:real`; `eps pow 2`] REAL_INTEGRAL_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `--(sqrt tau0 * Rm) * (eps pow 2 - &0)
    <= real_integral (real_interval[&0,eps pow 2])
         (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) ((sub:num->num) (N1 + N2))) tau0)`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_CONST o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN MAP_EVERY EXISTS_TAC [`&0`; `tau0:real`] THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(sqrt tau * Rm)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      USE_THEN "LOW" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) ((sub:num->num) (N1 + N2))) tau0
               <= Lam + e / &2` THEN
  REWRITE_TAC[p2a_L_length] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  UNDISCH_TAC
   `real_integral (real_interval[eps pow 2,tau0]) (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) tau0)
    <= real_integral (real_interval[eps pow 2,tau0])
         (p2a_L_integrand V tt ((gs:num->real->A) ((sub:num->num) (N1 + N2))) tau0) + e / &2` THEN
  REAL_ARITH_TAC);;

(* Integrability on [0,tau0] and L-length at most the infimum.               *)

let P2AJ_MB_INT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam.
     p2aj_lim V tt x nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam
     ==> p2a_L_integrand V tt gamma tau0 real_integrable_on real_interval[&0,tau0] /\
         p2a_L_length V tt gamma tau0 <= Lam`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_lim]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  REWRITE_TAC[p2a_L_length] THEN
  MATCH_MP_TAC P2AJ_INT_FROM_EPS THEN EXISTS_TAC `sqrt tau0 * Rm` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(sqrt tau * Rm)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[SQRT_MONO_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC P2AJ_MB_LINT_LOWER THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`; `a:num->real`;
                          `b:num->real`; `C:num->A->bool`; `eta:real`; `Fs:num->A->bool`;
                          `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                   `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                   `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                   `Rm:real`; `gs:num->real->A`; `Lb:real`; `tau0:real`; `sub:num->num`;
                   `gamma:real->A`; `t:real`] P2AJ_LIM_STRICT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[REAL_LT_IMP_LE];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                   `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                   `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                   `Rm:real`; `tau0:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`;
                   `gamma:real->A`; `Lam:real`; `sqrt t`] P2AJ_MB_EPS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LT; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN SIMP_TAC[]]);;

(* The limit curve is C^1 in every chart of the slice atlases at every time *)
(* in (0,tau0] (no corners): around each time it is chart_inv of the chart *)
(* curve of a good piece, composed with the square root.                   *)

let P2AJ_MB_PC1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam.
     p2aj_lim V tt x nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam
     ==> p2a_pc1 V tt gamma (&0) tau0 {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_lim]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  REWRITE_TAC[p2a_pc1; FINITE_EMPTY; NOT_IN_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt tau0 /\ sqrt tau0 pow 2 = tau0 /\ &0 < sqrt s0 /\
                sqrt s0 <= sqrt tau0 /\ sqrt s0 pow 2 = s0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; SQRT_MONO_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `sg = sqrt s0` THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `tau0:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`;
                 `gamma:real->A`; `Lam:real`; `sg / &2`] P2AJ_MB_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GD"))) THEN
  ABBREV_TAC `p = max (sg / &2) (sg - h / &2)` THEN
  ABBREV_TAC `p' = min (sqrt tau0) (sg + h / &2)` THEN
  SUBGOAL_THEN `&0 < p /\ p < sg /\ sg <= p' /\ p < p' /\ p' <= sqrt tau0 /\ p' - p <= h /\
                sg / &2 <= p`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "p'"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "GD" (MP_TAC o SPECL [`p:real`; `p':real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2aj_good] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (X_CHOOSE_THEN `Y:real^1->real^N` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `sa:real` (X_CHOOSE_THEN `sb:real` STRIP_ASSUME_TAC))
        (CONJUNCTS_THEN2 (LABEL_TAC "Y") ASSUME_TAC)))))))) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `j:num`] P2AJ_MB_REGION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `m = min (h / &2) (sg / &2)` THEN
  SUBGOAL_THEN `&0 < m /\ &0 < m pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT THEN EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= tau0 /\ abs(tau - s0) <= m pow 2 / &2
          ==> p <= sqrt tau /\ sqrt tau <= p' /\ sqrt tau pow 2 = tau`
  (LABEL_TAC "IN") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(sqrt tau - sg) < m` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(abs(tau - s0))` THEN CONJ_TAC THENL
       [EXPAND_TAC "sg" THEN MATCH_MP_TAC REAL_ABS_LE_SQRT_POS THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt tau <= sqrt tau0 /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_MONO_LE; SQRT_POW_2]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["p"; "p'"] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= tau0 /\ abs(tau - s0) <= m pow 2 / &2
          ==> (gamma:real->A) tau =
              chart_inv (U INTER (W:num->A->bool) j,phi:A->real^N)
                        ((Y:real^1->real^N)(lift(sqrt tau)))`
  (LABEL_TAC "EQ") THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
    USE_THEN "IN" (MP_TAC o SPEC `tau:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "Y" (MP_TAC o SPEC `sqrt tau`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* the chart curve in tau is C^1 in every chart *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `(W:num->A->bool) j`; `(A0:num->real) j`;
                 `(b:num->real) j`; `U:A->bool`;
                 `phi:A->real^N`; `\t:real^1. (Y:real^1->real^N)(lift(sqrt(drop t)))`;
                 `\t:real^1. inv(&2 * sqrt(drop t)) %
                             vector_derivative (Y:real^1->real^N) (at (lift(sqrt(drop t))))`;
                 `p pow 2`; `p' pow 2`] P2A_CHART_CURVE_PC1) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= tau /\ p <= sqrt tau /\ sqrt tau <= p' /\ sqrt tau pow 2 = tau`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 <= tau` ASSUME_TAC THENL
         [MP_TAC(SPEC `p:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[SQRT_POW_2] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `sqrt tau` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < tau /\ p <= sqrt tau /\ sqrt tau <= p'` STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `p pow 2` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      USE_THEN "Y" (MP_TAC o SPEC `sqrt tau`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2A_SQRT_CURVE_DERIV THEN
      ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "CC") THEN
  SUBGOAL_THEN
   `!S. S SUBSET {s | s0 - m pow 2 / &2 <= drop s /\ drop s <= s0 + m pow 2 / &2 /\
                      &0 < drop s /\ drop s <= tau0 /\
                      p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - drop s) = p2a_vatlas V (tt - s0) /\
                      (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}
        ==> continuously_differentiable 1 S (\s. SND c (gamma(drop s)))`
  (LABEL_TAC "CD") THENL
   [X_GEN_TAC `S:real^1->bool` THEN DISCH_THEN(LABEL_TAC "SS") THEN
    SUBGOAL_THEN
     `!s. s IN S ==> &0 <= drop s /\ drop s <= tau0 /\ abs(drop s - s0) <= m pow 2 / &2 /\
                     p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - drop s) = p2a_vatlas V (tt - s0) /\
                     (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))`
    (LABEL_TAC "SS2") THENL
     [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      USE_THEN "SS" (MP_TAC o SPEC `s:real^1` o REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MFDM_CONTINUOUSLY_DIFFERENTIABLE_EQ THEN
    EXISTS_TAC `\s:real^1. SND (c:(A->bool)#(A->real^N))
                  (chart_inv (U INTER (W:num->A->bool) j,phi:A->real^N)
                             ((Y:real^1->real^N)(lift(sqrt(drop s)))))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN USE_THEN "EQ" MATCH_MP_TAC THEN
      USE_THEN "SS2" (MP_TAC o SPEC `s:real^1`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "CC" (MP_TAC o SPECL [`S:real^1->bool`; `c:(A->bool)#(A->real^N)`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    USE_THEN "SS2" (MP_TAC o SPEC `s:real^1`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "IN" (MP_TAC o SPEC `drop s`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "EQ" (MP_TAC o SPEC `drop s`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(drop s) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(drop s) pow 2` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[REAL_LE_REFL];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  EXISTS_TAC `m pow 2 / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN USE_THEN "CD" MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* MT Lemma 7.2(c) in the boxes: the limit of a minimizing sequence of      *)
(* p2a_admx curves is an admissible minimizer without corners ending at q.  *)

let P2AJ_MB_7_2_C = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam.
     p2aj_lim V tt x nb W A0 a b C eta Fs R r lam Gm Rm tau0 gs Lb q sub gamma Lam
     ==> p2a_min V tt x tau0 gamma /\ p2a_pc1 V tt gamma (&0) tau0 {} /\ gamma tau0 = q`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_lim]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  SUBGOAL_THEN `!t. hausdorff_space(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))` THEN SIMP_TAC[p2a_svs]; ALL_TAC] THEN
  (* the end point *)
  SUBGOAL_THEN `(gamma:real->A) tau0 = q` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AK_LIM_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau0)`;
                          `\n. (gs:num->real->A) ((sub:num->num) n) tau0`] THEN
    FIRST_ASSUM(MP_TAC o SPEC `tau0:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th) &&
        not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
      REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `tau0:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th) &&
        can (find_term ((=) `(gs:num->real->A) 0`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[] THEN X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN EXISTS_TAC `0` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* admissibility *)
  SUBGOAL_THEN `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x tau0 (gamma:real->A)` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_adm] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`t1:real`; `O:A->bool`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                     `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                     `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                     `Rm:real`; `gs:num->real->A`; `Lb:real`; `tau0:real`; `sub:num->num`;
                     `gamma:real->A`; `t1:real`; `O:A->bool`] P2AJ_MB_CONT) THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `{}:real->bool` THEN
      MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                     `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                     `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                     `Rm:real`; `tau0:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`;
                     `gamma:real->A`; `Lam:real`] P2AJ_MB_PC1) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                     `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                     `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                     `Rm:real`; `gs:num->real->A`; `Lb:real`; `tau0:real`; `sub:num->num`;
                     `gamma:real->A`; `tau:real`] P2AJ_LIM_STRICT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)] THEN
      MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                     `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                     `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                     `Rm:real`; `j:num`] P2AJ_MB_REGION) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; STRIP_TAC] THEN
      REWRITE_TAC[p2a_smooth] THEN
      MAP_EVERY EXISTS_TAC [`(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(C:num->A->bool) j SUBSET (W:num->A->bool) j` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                     `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                     `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                     `Rm:real`; `tau0:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`;
                     `gamma:real->A`; `Lam:real`] P2AJ_MB_INT) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2a_min] THEN CONJ_TAC THENL
   [X_GEN_TAC `gamma':real->A` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Lam:real` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                     `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                     `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                     `Rm:real`; `tau0:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`;
                     `gamma:real->A`; `Lam:real`] P2AJ_MB_INT) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Lam:real`)) (concl th) && can (find_term ((=) `q:A`)) (concl th))) THEN
      ASM_SIMP_TAC[P2AX_ADM_IMP]];
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                   `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                   `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                   `Rm:real`; `tau0:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`;
                   `gamma:real->A`; `Lam:real`] P2AJ_MB_PC1) THEN
    ASM_REWRITE_TAC[]]);;

