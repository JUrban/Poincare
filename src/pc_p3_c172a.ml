(* ========================================================================= *)
(* Unit pc_p3_c172a: MT Lemma 17.2, part A (the first bad                    *)
(* time).  Bad times: some point at that time with R >= rp^-2 and no strong *)
(* canonical neighbourhood.  The infimum ts of the bad times lies in        *)
(* [T, horizon) when the truncation at T is canonical; the truncation at ts *)
(* is canonical; and ts itself is bad as soon as strong canonical           *)
(* neighbourhoods at good points of ts persist on a box N x [ts, ts + d)    *)
(* (the openness property, MT pp. 396-401, proved in later units): on the   *)
(* compact stage finitely many boxes (or boxes where R < r'^-2, by joint    *)
(* continuity of R) cover, so no bad time lies just after ts.               *)
(*                                                                         *)
(* Bad times, the canonical assumption and its truncations,                 *)
(* boxes where R stays below a bound.                                        *)
(* ========================================================================= *)

needs "src/pc_p3_c17trunc.ml";;
needs "src/pc_rfa_scalar.ml";;
needs "src/pc_apx_event.ml";;

prioritize_real();;
type_invention_error := true;;

let p3h_bad = new_definition
 `p3h_bad (hs:(A)rfs_history) (C:real) (eps:real) (rp:real->real) (t:real) <=>
    ?x. &0 <= t /\ x IN topspace(rfs_top_at hs t) /\
        inv(rp t pow 2) <= rfs_vscalar (rfs_view hs) t x /\
        ~p3_canon_at (rfs_view hs) C eps x t`;;

let P3H_CANON_ASSUMPTION_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps rp.
     rfs_canonical_assumption V C eps rp <=>
     !t x. &0 <= t /\ x IN topspace(rfs_vtop V t) /\
           inv(rp t pow 2) <= rfs_vscalar V t x
           ==> p3_canon_at V C eps x t`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_canonical_assumption; rfs_vtop; rfs_vscalar;
              p3_canon_at]);;

let P3H_CANON_BAD = prove
 (`!(hs:(A)rfs_history) C eps rp.
     rfs_canonical_assumption (rfs_view hs) C eps rp <=> !t. ~p3h_bad hs C eps rp t`,
  REWRITE_TAC[P3H_CANON_ASSUMPTION_ALT; p3h_bad] THEN
  REWRITE_TAC[rfs_view; rfs_vtop] THEN MESON_TAC[]);;

let P3H_TRUNC_CANON_BAD = prove
 (`!(hs:(A)rfs_history) C eps rp tau.
     rfs_canonical_assumption (rfs_trunc (rfs_view hs) tau) C eps rp <=>
     !t. t < tau ==> ~p3h_bad hs C eps rp t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P3H_CANON_ASSUMPTION_ALT; p3h_bad] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`]) THEN
    ASM_SIMP_TAC[P3E_VIEW_TRUNC_AT] THEN REWRITE_TAC[p3_canon_at] THEN
    ASM_SIMP_TAC[P3E_STRONG_CANONICAL_TRUNC] THEN
    UNDISCH_TAC `~p3_canon_at (rfs_view (hs:(A)rfs_history)) C eps x t` THEN
    REWRITE_TAC[p3_canon_at; rfs_view; rfs_vtop] THEN
    UNDISCH_TAC `(x:A) IN topspace(rfs_top_at hs t)` THEN REWRITE_TAC[rfs_view; rfs_vtop] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t < tau` THENL
   [ALL_TAC;
    UNDISCH_TAC `(x:A) IN topspace(rfs_vtop (rfs_trunc (rfs_view hs) tau) t)` THEN
    REWRITE_TAC[rfs_view; rfs_trunc; rfs_vtop] THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  UNDISCH_TAC `(x:A) IN topspace(rfs_vtop (rfs_trunc (rfs_view hs) tau) t)` THEN
  UNDISCH_TAC `inv(rp t pow 2) <= rfs_vscalar (rfs_trunc (rfs_view (hs:(A)rfs_history)) tau) t x` THEN
  ASM_SIMP_TAC[P3E_VIEW_TRUNC_AT] THEN REWRITE_TAC[p3_canon_at] THEN
  ASM_SIMP_TAC[P3E_STRONG_CANONICAL_TRUNC] THEN REWRITE_TAC[rfs_view; rfs_vtop] THEN
  MESON_TAC[]);;

let P3H_BAD_LIVE = prove
 (`!(hs:(A)rfs_history) C eps rp t.
     p3h_bad hs C eps rp t ==> &0 <= t /\ t < rfs_horizon hs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3h_bad; rfs_top_at; rfs_live; rfs_horizon] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]);;

(* Joint continuity of R on a slab gives boxes N x [ts, ts + d) where R stays *)
(* below a strict bound.                                                    *)

let P3H_SCALAR_BOX = prove
 (`!(hs:(A)rfs_history) k ts x c.
     rfs_history_ok hs /\ k <= hs_count hs /\
     hs_time hs k <= ts /\ ts < hs_time hs (k + 1) /\ x IN topspace(hs_top hs k) /\
     mfd_scalar (hs_atlas hs k) (hs_metric hs k ts) x < c
     ==> ?N d. open_in (hs_top hs k) N /\ x IN N /\ &0 < d /\
               !s y. ts <= s /\ s < ts + d /\ s < hs_time hs (k + 1) /\ y IN N
                     ==> mfd_scalar (hs_atlas hs k) (hs_metric hs k s) y < c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `top = hs_top (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `atlas = hs_atlas (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `g = hs_metric (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `b = hs_time (hs:(A)rfs_history) (k + 1)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `ts:real`;
                 `b:real`; `g:real->A->real^3^3`] RFA_MFD_SCALAR_CONTINUOUS_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `hs_time (hs:(A)rfs_history) k`; `b:real`; `g:real->A->real^3^3`;
                     `t:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC RFA_RICCI_FLOW_FROM_EXT_AT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `hs_time (hs:(A)rfs_history) k`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_map; SUBTOPOLOGY_TOPSPACE] THEN
  DISCH_THEN(MP_TAC o SPEC `{r:real | r < c}` o CONJUNCT2) THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_LT] THEN
  REWRITE_TAC[OPEN_IN_PROD_TOPOLOGY_ALT] THEN
  DISCH_THEN(MP_TAC o SPECL [`ts:real`; `x:A`]) THEN
  REWRITE_TAC[IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real->bool` (X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_SUBTOPOLOGY] o check (fun th ->
    can (find_term (fun t -> t = `u:real->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open_in euclideanreal (w:real->bool)` THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; real_open] THEN
  DISCH_THEN(MP_TAC o SPEC `ts:real`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`v:A->bool`; `e:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> t = `(u:real->bool) CROSS (v:A->bool)`)) (concl th))) THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `y:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u:real->bool) = w INTER {t | ts <= t /\ t < b}` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* No bad times just after a good time ts (compactness of the               *)
(* stage), and the first bad time.                                           *)
(* ========================================================================= *)

let P3H_GOOD_BOX = prove
 (`!(hs:(A)rfs_history) C eps rp r' ts k.
     rfs_history_ok hs /\ k <= hs_count hs /\
     hs_time hs k <= ts /\ ts < hs_time hs (k + 1) /\ &0 <= ts /\
     (!t. ts <= t /\ t < hs_time hs (k + 1) ==> rp t = r') /\
     (!x. x IN topspace(hs_top hs k) /\
          inv(r' pow 2) <= mfd_scalar (hs_atlas hs k) (hs_metric hs k ts) x
          ==> ?N d. open_in (hs_top hs k) N /\ x IN N /\ &0 < d /\
                    !s y. ts <= s /\ s < ts + d /\ s < hs_time hs (k + 1) /\ y IN N /\
                          inv(r' pow 2) <= mfd_scalar (hs_atlas hs k) (hs_metric hs k s) y
                          ==> p3_canon_at (rfs_view hs) C eps y s)
     ==> ?d. &0 < d /\ !t. ts <= t /\ t < ts + d ==> ~p3h_bad hs C eps rp t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN topspace(hs_top hs k)
        ==> ?N d. open_in (hs_top (hs:(A)rfs_history) k) N /\ x IN N /\ &0 < d /\
                  !s y. ts <= s /\ s < ts + d /\ s < hs_time hs (k + 1) /\ y IN N /\
                        inv(r' pow 2) <= mfd_scalar (hs_atlas hs k) (hs_metric hs k s) y
                        ==> p3_canon_at (rfs_view hs) C eps y s`
  MP_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `inv(r' pow 2) <= mfd_scalar (hs_atlas hs k)
                                     (hs_metric (hs:(A)rfs_history) k ts) x` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_canon_at")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar (hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k ts) x <
                  inv(r' pow 2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`; `x:A`; `inv(r' pow 2)`]
                  P3H_SCALAR_BOX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`N:A->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:A`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `N:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A->A->bool` (X_CHOOSE_TAC `d:A->real`)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `compact_space (hs_top (hs:(A)rfs_history) k)` THEN
  REWRITE_TAC[compact_space; compact_in] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (N:A->A->bool) (topspace(hs_top (hs:(A)rfs_history) k))` o
             CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> (a /\ b) /\ c`] THEN
  REWRITE_TAC[FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:A->bool` (X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `dd = inf ((hs_time (hs:(A)rfs_history) (k + 1) - ts) INSERT IMAGE (d:A->real) Fs)` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= hs_time (hs:(A)rfs_history) (k + 1) - ts /\
                (!x. x IN Fs ==> dd <= (d:A->real) x)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN
    MP_TAC(ISPEC `(hs_time (hs:(A)rfs_history) (k + 1) - ts) INSERT IMAGE (d:A->real) Fs`
                 INF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY; FORALL_IN_INSERT;
                 FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      is_const t && fst(dest_const t) = "INSERT")) (concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "IN")) THEN
    REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x:A) IN topspace(hs_top (hs:(A)rfs_history) k)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `dd:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[p3h_bad; NOT_EXISTS_THM] THEN
  X_GEN_TAC `y:A` THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `t:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[rfs_view; rfs_vscalar] THEN
  SUBGOAL_THEN `(rp:real->real) t = r'` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?x:A. x IN Fs /\ (y:A) IN (N:A->A->bool) x` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(hs_top (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `N:A->A->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_canon_at")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `y:A`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[rfs_view] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `ts + dd` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> ts + a <= ts + b`) THEN ASM_SIMP_TAC[]);;

(* Part A: the first bad time, given the openness property OPEN at good     *)
(* points of times whose truncation is canonical.                           *)

let P3H_FIRST_BAD_TIME = prove
 (`!(hs:(A)rfs_history) C eps rp r' T0.
     rfs_history_ok hs /\ &0 <= T0 /\
     rfs_canonical_assumption (rfs_trunc (rfs_view hs) T0) C eps rp /\
     ~rfs_canonical_assumption (rfs_view hs) C eps rp /\
     (!t. T0 <= t /\ t < rfs_horizon hs ==> rp t = r') /\
     (!ts x. T0 <= ts /\ ts < rfs_horizon hs /\
             rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps rp /\
             x IN topspace(rfs_top_at hs ts) /\
             inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
             p3_canon_at (rfs_view hs) C eps x ts
             ==> ?N d. open_in (rfs_top_at hs ts) N /\ x IN N /\ &0 < d /\
                       !s y. ts <= s /\ s < ts + d /\ y IN N /\
                             y IN topspace(rfs_top_at hs s) /\
                             inv(r' pow 2) <= rfs_vscalar (rfs_view hs) s y
                             ==> p3_canon_at (rfs_view hs) C eps y s)
     ==> ?ts x. T0 <= ts /\ ts < rfs_horizon hs /\
                rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps rp /\
                x IN topspace(rfs_top_at hs ts) /\
                inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
                ~p3_canon_at (rfs_view hs) C eps x ts`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "const") (LABEL_TAC "open")))))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P3H_TRUNC_CANON_BAD] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_trunc")) (concl th))) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[P3H_CANON_BAD] o check (is_neg o concl)) THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN DISCH_THEN(X_CHOOSE_TAC `t0:real`) THEN
  ABBREV_TAC `B = {t | p3h_bad (hs:(A)rfs_history) C eps rp t}` THEN
  SUBGOAL_THEN `~(B:real->bool = {}) /\ (!t. t IN B ==> T0 <= t)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[REAL_NOT_LT]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `B:real->bool` INF) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `ts = inf (B:real->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `T0 <= ts /\ ts < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `t0:real` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "B" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      ASM_MESON_TAC[P3H_BAD_LIVE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_canonical_assumption (rfs_trunc (rfs_view (hs:(A)rfs_history)) ts)
                  C eps rp` ASSUME_TAC THENL
   [REWRITE_TAC[P3H_TRUNC_CANON_BAD] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `ts <= t:real` MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `B:real->bool`)) (concl th) &&
        can (find_term (fun t -> t = `ts:real`)) (concl th) &&
        not (can (find_term (fun t -> is_var t && fst(dest_var t) = "b")) (concl th)))) THEN
      EXPAND_TAC "B" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `p3h_bad (hs:(A)rfs_history) C eps rp ts` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p3h_bad]) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`ts:real`; `x:A`] THEN
    REMOVE_THEN "const" (MP_TAC o SPEC `ts:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) ts` THEN STRIP_TAC THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k + 1) <= rfs_horizon hs` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_horizon] THEN MATCH_MP_TAC APX_HS_TIME_LE THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ts /\
                (!t. ts <= t /\ t < hs_time (hs:(A)rfs_history) (k + 1) ==> (rp:real->real) t = r')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "const" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `rp:real->real`; `r':real`;
                 `ts:real`; `k:num`] P3H_GOOD_BOX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "open" (MP_TAC o SPECL [`ts:real`; `x:A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[rfs_view; rfs_vscalar] THEN
      MP_TAC(ASSUME `~p3h_bad (hs:(A)rfs_history) C eps rp ts`) THEN
      REWRITE_TAC[p3h_bad; NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
      SUBGOAL_THEN `(rp:real->real) ts = r'` SUBST1_TAC THENL
       [USE_THEN "const" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[rfs_view; rfs_vscalar];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`N:A->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `N:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[rfs_view; rfs_vscalar] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `N:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `ts + d0` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `B:real->bool`)) (concl th) &&
    can (find_term (fun t -> is_var t && fst(dest_var t) = "b")) (concl th))) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  X_GEN_TAC `t:real` THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `d0:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `B:real->bool`)) (concl th) &&
    can (find_term (fun t -> t = `ts:real`)) (concl th) &&
    not (can (find_term (fun t -> is_var t && fst(dest_var t) = "b")) (concl th)))) THEN
  EXPAND_TAC "B" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `~(t:real = ts)` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; REAL_ARITH_TAC]);;

