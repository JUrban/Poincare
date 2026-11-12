(* ========================================================================= *)
(* pc_wan_ptime: time derivatives of whole-space weak solutions through the  *)
(* equation. No new estimates: commutation of weak derivatives, the          *)
(* time-differentiated weak equation, and an induction in an anisotropic     *)
(* class (all spatial orders, m time derivatives).                           *)
(*   - the classes wan_hxa and wan_ht, commutation of weak derivatives;      *)
(*   - the time derivative of a weak solution;                               *)
(*   - the time bootstrap.                                                   *)
(* ========================================================================= *)

needs "src/pc_wan_pstep.ml";;

prioritize_real();;
type_invention_error := true;;

let wan_hxa = new_definition
 `wan_hxa (u:real^(N,1)finite_sum->real^1) <=> !s. wan_hd (1..dimindex(:N)) s u`;;

let wan_ht = define
 `(wan_ht 0 (u:real^(N,1)finite_sum->real^1) <=> wan_hxa u) /\
  (wan_ht (SUC m) u <=>
     wan_hxa u /\
     ?w. wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1) u w /\ wan_ht m w)`;;

(* ------------------------------------------------------------------------- *)
(* The class of all spatial orders.                                          *)
(* ------------------------------------------------------------------------- *)

let WAN_HXA_LSPACE = prove
 (`!u:real^(N,1)finite_sum->real^1.
     wan_hxa u ==> u IN lspace (:real^(N,1)finite_sum) (&2)`,
  MESON_TAC[wan_hxa; WAN_HD_LSPACE]);;

let WAN_HXA_LLOC = prove
 (`!u:real^(N,1)finite_sum->real^1. wan_hxa u ==> wan_lloc (:real^(N,1)finite_sum) u`,
  MESON_TAC[WAN_HXA_LSPACE; WAN_L2_LLOC]);;

let WAN_HXA_ZERO = prove
 (`wan_hxa (\z:real^(N,1)finite_sum. vec 0:real^1)`,
  REWRITE_TAC[wan_hxa; WAN_HD_ZERO]);;

let WAN_HXA_ADD = prove
 (`!u u':real^(N,1)finite_sum->real^1.
     wan_hxa u /\ wan_hxa u' ==> wan_hxa (\x. u x + u' x)`,
  SIMP_TAC[wan_hxa; WAN_HD_ADD]);;

let WAN_HXA_SUB = prove
 (`!u u':real^(N,1)finite_sum->real^1.
     wan_hxa u /\ wan_hxa u' ==> wan_hxa (\x. u x - u' x)`,
  SIMP_TAC[wan_hxa; WAN_HD_SUB]);;

let WAN_HXA_CMUL = prove
 (`!(u:real^(N,1)finite_sum->real^1) c. wan_hxa u ==> wan_hxa (\x. c % u x)`,
  SIMP_TAC[wan_hxa; WAN_HD_CMUL]);;

let WAN_HXA_MUL = prove
 (`!(m:real^(N,1)finite_sum->real) (u:real^(N,1)finite_sum->real^1).
     wan_cc m /\ wan_hxa u ==> wan_hxa (\x. m x % u x)`,
  SIMP_TAC[wan_hxa; WAN_HD_MUL]);;

let WAN_HXA_VSUM = prove
 (`!(u:A->real^(N,1)finite_sum->real^1) t.
     FINITE t /\ (!i. i IN t ==> wan_hxa (u i))
     ==> wan_hxa (\x. vsum t (\i. u i x))`,
  REWRITE_TAC[wan_hxa] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_HD_VSUM THEN
  ASM_SIMP_TAC[]);;

let WAN_HXA_SPIKE = prove
 (`!(u:real^(N,1)finite_sum->real^1) u' t.
     negligible t /\ (!x. ~(x IN t) ==> u' x = u x) /\ wan_hxa u ==> wan_hxa u'`,
  REWRITE_TAC[wan_hxa] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_HD_SPIKE THEN
  MAP_EVERY EXISTS_TAC [`u:real^(N,1)finite_sum->real^1`; `t:real^(N,1)finite_sum->bool`] THEN
  ASM_REWRITE_TAC[]);;

let WAN_HXA_DERIV = prove
 (`!(u:real^(N,1)finite_sum->real^1) w k.
     wan_hxa u /\ 1 <= k /\ k <= dimindex(:N) /\
     wan_wpd (:real^(N,1)finite_sum) k u w
     ==> wan_hxa w`,
  REWRITE_TAC[wan_hxa] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_HD_WPD THEN
  MAP_EVERY EXISTS_TAC [`u:real^(N,1)finite_sum->real^1`; `k:num`] THEN
  ASM_REWRITE_TAC[IN_NUMSEG]);;

let WAN_HXA_HAS_DERIV = prove
 (`!(u:real^(N,1)finite_sum->real^1) k.
     wan_hxa u /\ 1 <= k /\ k <= dimindex(:N)
     ==> ?w. wan_wpd (:real^(N,1)finite_sum) k u w /\ wan_hxa w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `SUC 0` o REWRITE_RULE[wan_hxa]) THEN
  REWRITE_TAC[wan_hd; IN_NUMSEG] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^(N,1)finite_sum->real^1` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_HXA_DERIV THEN
  MAP_EVERY EXISTS_TAC [`u:real^(N,1)finite_sum->real^1`; `k:num`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Commutation of weak derivatives.                                          *)
(* ------------------------------------------------------------------------- *)

let WAN_DPART_SYM = prove
 (`!(phi:real^M->real) k l x.
     wan_test (:real^M) phi /\ 1 <= k /\ k <= dimindex(:M) /\ 1 <= l /\ l <= dimindex(:M)
     ==> wan_dpart l (wan_dpart k phi) x = wan_dpart k (wan_dpart l phi) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WAN_DROP_PD_LIFT] THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX] THEN MATCH_MP_TAC WAN_PD_SYM THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[wan_test]);;

let WAN_VEC_CHAIN4 = prove
 (`!a c b e d:real^N. b = --c /\ e = --b /\ d = --a /\ d = e ==> a = --c`,
  VECTOR_ARITH_TAC);;

let WAN_WPD_COMMUTE = prove
 (`!(u:real^M->real^K) uk ul ukl k l.
     1 <= k /\ k <= dimindex(:M) /\ 1 <= l /\ l <= dimindex(:M) /\
     wan_wpd (:real^M) k u uk /\ wan_wpd (:real^M) l u ul /\
     wan_wpd (:real^M) l uk ukl
     ==> wan_wpd (:real^M) k ul ukl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_wpd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `phi:real^M->real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `wan_test (:real^M) (wan_dpart k phi) /\ wan_test (:real^M) (wan_dpart l phi)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_TEST_DPART_TEST]; ALL_TAC] THEN
  MATCH_MP_TAC WAN_VEC_CHAIN4 THEN
  EXISTS_TAC `integral (:real^M) (\x. wan_dpart l phi x % (uk:real^M->real^K) x)` THEN
  EXISTS_TAC `integral (:real^M)
                (\x. wan_dpart k (wan_dpart l phi) x % (u:real^M->real^K) x)` THEN
  EXISTS_TAC `integral (:real^M)
                (\x. wan_dpart l (wan_dpart k phi) x % (u:real^M->real^K) x)` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      free_in `ukl:real^M->real^K` (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      free_in `uk:real^M->real^K` (concl th) && is_forall(concl th) &&
      free_in `u:real^M->real^K` (concl th))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      free_in `ul:real^M->real^K` (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC WAN_DPART_SYM THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The anisotropic class: all spatial orders and m time derivatives.        *)
(* ------------------------------------------------------------------------- *)

let WAN_TIME_INDEX = prove
 (`1 <= dimindex(:N) + 1 /\ dimindex(:N) + 1 <= dimindex(:(N,1)finite_sum)`,
  REWRITE_TAC[TEXT_DIMINDEX_SPACETIME] THEN ARITH_TAC);;

let WAN_SPACE_INDEX = prove
 (`!k. 1 <= k /\ k <= dimindex(:N) ==> 1 <= k /\ k <= dimindex(:(N,1)finite_sum)`,
  REWRITE_TAC[TEXT_DIMINDEX_SPACETIME] THEN ARITH_TAC);;

let WAN_HT_HXA = prove
 (`!m (u:real^(N,1)finite_sum->real^1). wan_ht m u ==> wan_hxa u`,
  INDUCT_TAC THEN SIMP_TAC[wan_ht]);;

let WAN_HT_MONO = prove
 (`!m (u:real^(N,1)finite_sum->real^1). wan_ht (SUC m) u ==> wan_ht m u`,
  INDUCT_TAC THENL [SIMP_TAC[wan_ht]; ALL_TAC] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[wan_ht] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `w:real^(N,1)finite_sum->real^1` THEN ASM_SIMP_TAC[]);;

let WAN_HT_ZERO = prove
 (`!m. wan_ht m (\z:real^(N,1)finite_sum. vec 0:real^1)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[wan_ht; WAN_HXA_ZERO] THEN
  EXISTS_TAC `\z:real^(N,1)finite_sum. vec 0:real^1` THEN
  ASM_REWRITE_TAC[WAN_WPD_ZERO]);;

let WAN_HT_ADD = prove
 (`!m (u:real^(N,1)finite_sum->real^1) u'.
     wan_ht m u /\ wan_ht m u' ==> wan_ht m (\x. u x + u' x)`,
  INDUCT_TAC THENL [SIMP_TAC[wan_ht; WAN_HXA_ADD]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wan_ht] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w':real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC))) THEN
  ASM_SIMP_TAC[WAN_HXA_ADD] THEN EXISTS_TAC `\x. (w:real^(N,1)finite_sum->real^1) x + w' x` THEN
  ASM_SIMP_TAC[WAN_WPD_ADD]);;

let WAN_HT_CMUL = prove
 (`!m (u:real^(N,1)finite_sum->real^1) c. wan_ht m u ==> wan_ht m (\x. c % u x)`,
  INDUCT_TAC THENL [SIMP_TAC[wan_ht; WAN_HXA_CMUL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wan_ht] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[WAN_HXA_CMUL] THEN EXISTS_TAC `\x. c % (w:real^(N,1)finite_sum->real^1) x` THEN
  ASM_SIMP_TAC[WAN_WPD_CMUL]);;

let WAN_HT_SUB = prove
 (`!m (u:real^(N,1)finite_sum->real^1) u'.
     wan_ht m u /\ wan_ht m u' ==> wan_ht m (\x. u x - u' x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_SUB] THEN
  MP_TAC(ISPECL [`m:num`; `u:real^(N,1)finite_sum->real^1`;
                 `\x. --(&1) % (u':real^(N,1)finite_sum->real^1) x`] WAN_HT_ADD) THEN
  ASM_SIMP_TAC[WAN_HT_CMUL; VECTOR_MUL_LNEG; VECTOR_MUL_LID]);;

let WAN_HT_VSUM = prove
 (`!m (u:A->real^(N,1)finite_sum->real^1) t.
     FINITE t /\ (!i. i IN t ==> wan_ht m (u i))
     ==> wan_ht m (\x. vsum t (\i. u i x))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; WAN_HT_ZERO; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `(u:A->real^(N,1)finite_sum->real^1) a`;
                 `\x. vsum s (\i. (u:A->real^(N,1)finite_sum->real^1) i x)`] WAN_HT_ADD) THEN
  ASM_SIMP_TAC[]);;

let WAN_HT_MUL = prove
 (`!m (c:real^(N,1)finite_sum->real) (u:real^(N,1)finite_sum->real^1).
     wan_cc c /\ wan_ht m u ==> wan_ht m (\x. c x % u x)`,
  INDUCT_TAC THENL [SIMP_TAC[wan_ht; WAN_HXA_MUL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_ht m (u:real^(N,1)finite_sum->real^1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_HT_MONO]; ALL_TAC] THEN
  UNDISCH_TAC `wan_ht (SUC m) (u:real^(N,1)finite_sum->real^1)` THEN
  ONCE_REWRITE_TAC[wan_ht] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[WAN_HXA_MUL] THEN
  EXISTS_TAC `\x. wan_dpart (dimindex(:N) + 1) (c:real^(N,1)finite_sum->real) x %
                  (u:real^(N,1)finite_sum->real^1) x + c x % w x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_WPD_MUL_SMOOTH THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    ASM_MESON_TAC[wan_cc];
    MATCH_MP_TAC WAN_HT_ADD THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[WAN_CC_DPART; ETA_AX]]);;

let WAN_HT_SPIKE = prove
 (`!m (u:real^(N,1)finite_sum->real^1) u' t.
     negligible t /\ (!x. ~(x IN t) ==> u' x = u x) /\ wan_ht m u ==> wan_ht m u'`,
  INDUCT_TAC THEN REWRITE_TAC[wan_ht] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC WAN_HXA_SPIKE THEN
    MAP_EVERY EXISTS_TAC [`u:real^(N,1)finite_sum->real^1`; `t:real^(N,1)finite_sum->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC WAN_HXA_SPIKE THEN
    MAP_EVERY EXISTS_TAC [`u:real^(N,1)finite_sum->real^1`; `t:real^(N,1)finite_sum->bool`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `w:real^(N,1)finite_sum->real^1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_WPD_SPIKE THEN
    MAP_EVERY EXISTS_TAC [`u:real^(N,1)finite_sum->real^1`; `w:real^(N,1)finite_sum->real^1`;
                          `t:real^(N,1)finite_sum->bool`] THEN
    ASM_SIMP_TAC[]]);;

let WAN_HT_WPD_T = prove
 (`!m (u:real^(N,1)finite_sum->real^1) w.
     wan_ht (SUC m) u /\ wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1) u w
     ==> wan_ht m w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_ht] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w0:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  MATCH_MP_TAC WAN_HT_SPIKE THEN
  MAP_EVERY EXISTS_TAC
   [`w0:real^(N,1)finite_sum->real^1`;
    `{x:real^(N,1)finite_sum | ~((w0:real^(N,1)finite_sum->real^1) x = w x)}`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`(:real^(N,1)finite_sum)`; `dimindex(:N) + 1`;
                 `u:real^(N,1)finite_sum->real^1`; `w0:real^(N,1)finite_sum->real^1`;
                 `w:real^(N,1)finite_sum->real^1`] WAN_WPD_UNIQUE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN MESON_TAC[]);;

let WAN_HT_DERIV_X = prove
 (`!m (u:real^(N,1)finite_sum->real^1) w k.
     wan_ht m u /\ 1 <= k /\ k <= dimindex(:N) /\
     wan_wpd (:real^(N,1)finite_sum) k u w
     ==> wan_ht m w`,
  INDUCT_TAC THENL
   [REWRITE_TAC[wan_ht] THEN MESON_TAC[WAN_HXA_DERIV]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wan_ht] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ut:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_HXA_DERIV THEN
    MAP_EVERY EXISTS_TAC [`u:real^(N,1)finite_sum->real^1`; `k:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ut:real^(N,1)finite_sum->real^1`; `k:num`] WAN_HXA_HAS_DERIV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[WAN_HT_HXA]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `utk:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `utk:real^(N,1)finite_sum->real^1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_WPD_COMMUTE THEN
    MAP_EVERY EXISTS_TAC [`u:real^(N,1)finite_sum->real^1`; `ut:real^(N,1)finite_sum->real^1`;
                          `k:num`] THEN
    ASM_SIMP_TAC[WAN_TIME_INDEX; WAN_SPACE_INDEX];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    MAP_EVERY EXISTS_TAC [`ut:real^(N,1)finite_sum->real^1`; `k:num`] THEN
    ASM_REWRITE_TAC[]]);;

let WAN_HT_ALL_HD = prove
 (`!s (u:real^(N,1)finite_sum->real^1).
     (!m. wan_ht m u) ==> wan_hd (1..dimindex(:(N,1)finite_sum)) s u`,
  INDUCT_TAC THENL
   [REWRITE_TAC[wan_hd] THEN MESON_TAC[WAN_HT_HXA; WAN_HXA_LSPACE]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wan_hd] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[WAN_HT_HXA; WAN_HXA_LSPACE]; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `k <= dimindex(:N) + 1` ASSUME_TAC THENL
   [ASM_MESON_TAC[TEXT_DIMINDEX_SPACETIME]; ALL_TAC] THEN
  ASM_CASES_TAC `k <= dimindex(:N)` THENL
   [MP_TAC(ISPECL [`u:real^(N,1)finite_sum->real^1`; `k:num`] WAN_HXA_HAS_DERIV) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[WAN_HT_HXA]; ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `w:real^(N,1)finite_sum->real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o check
      (fun th -> not(free_in `u:real^(N,1)finite_sum->real^1` (concl th)))) THEN
    GEN_TAC THEN MATCH_MP_TAC WAN_HT_DERIV_X THEN
    MAP_EVERY EXISTS_TAC [`u:real^(N,1)finite_sum->real^1`; `k:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k = dimindex(:N) + 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `SUC 0`) THEN REWRITE_TAC[wan_ht] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  EXISTS_TAC `w:real^(N,1)finite_sum->real^1` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o check
    (fun th -> not(free_in `u:real^(N,1)finite_sum->real^1` (concl th)))) THEN
  X_GEN_TAC `m:num` THEN MATCH_MP_TAC WAN_HT_WPD_T THEN
  EXISTS_TAC `u:real^(N,1)finite_sum->real^1` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The time derivative of a weak solution exists through                    *)
(* the equation, and solves the time-differentiated weak equation.          *)
(* ========================================================================= *)

let WAN_WPD_VSUM = prove
 (`!(u:A->real^M->real^K) v k t.
     FINITE t /\ (!i. i IN t ==> wan_wpd (:real^M) k (u i) (v i))
     ==> wan_wpd (:real^M) k (\x. vsum t (\i. u i x)) (\x. vsum t (\i. v i x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; WAN_WPD_ZERO; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `k:num`; `(u:A->real^M->real^K) a`; `(v:A->real^M->real^K) a`;
                 `\x. vsum s (\i. (u:A->real^M->real^K) i x)`;
                 `\x. vsum s (\i. (v:A->real^M->real^K) i x)`] WAN_WPD_ADD) THEN
  ASM_SIMP_TAC[]);;

let WAN_GWEAK_TDER = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
    (c:real^(N,1)finite_sum->real) (f:real^(N,1)finite_sum->real^1)
    (g:num->real^(N,1)finite_sum->real^1) (W:real^(N,1)finite_sum->real^1) KW dH.
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> (\z. lift(b z$i)) continuous_on (:real^(N,1)finite_sum)) /\
     (\z. lift(c z)) continuous_on (:real^(N,1)finite_sum) /\
     wan_lloc (:real^(N,1)finite_sum) W /\ wan_lloc (:real^(N,1)finite_sum) f /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_lloc (:real^(N,1)finite_sum) (KW j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> wan_wpd (:real^(N,1)finite_sum) i
                (\z. vsum(1..dimindex(:N)) (\j. a z$i$j % KW j z) + g i z) (dH i)) /\
     wan_gweak a b c f g W KW
     ==> wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1) W
           (\z. vsum(1..dimindex(:N)) (\i. dH i z) +
                (vsum(1..dimindex(:N)) (\i. b z$i % KW i z) + c z % W z + f z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `wan_lloc (:real^(N,1)finite_sum)
      (\z. vsum(1..dimindex(:N))
             (\i. (b:real^(N,1)finite_sum->real^N) z$i %
                  (KW:num->real^(N,1)finite_sum->real^1) i z) +
           (c:real^(N,1)finite_sum->real) z % (W:real^(N,1)finite_sum->real^1) z +
           (f:real^(N,1)finite_sum->real^1) z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_LLOC_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC WAN_LLOC_CONT_MUL THEN
      ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC WAN_LLOC_ADD THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC WAN_LLOC_CONT_MUL THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_lloc (:real^(N,1)finite_sum)
              (\z. vsum(1..dimindex(:N))
                     (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j %
                          (KW:num->real^(N,1)finite_sum->real^1) j z) +
                   (g:num->real^(N,1)finite_sum->real^1) i z) /\
            wan_lloc (:real^(N,1)finite_sum)
              ((dH:num->real^(N,1)finite_sum->real^1) i)`
  (LABEL_TAC "hl") THENL [ASM_MESON_TAC[wan_wpd]; ALL_TAC] THEN
  REWRITE_TAC[wan_wpd] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_LLOC_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!u:real^(N,1)finite_sum->real^1.
      wan_lloc (:real^(N,1)finite_sum) u
      ==> (\z. phi z % u z) integrable_on (:real^(N,1)finite_sum) /\
          (!i. (\z. wan_dpart i phi z % u z) integrable_on (:real^(N,1)finite_sum))`
  (LABEL_TAC "pair") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(:real^(N,1)finite_sum)`; `phi:real^(N,1)finite_sum->real`;
                   `u:real^(N,1)finite_sum->real^1`] WAN_TEST_PAIRING) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  UNDISCH_TAC `wan_gweak (a:real^(N,1)finite_sum->real^N^N) b c f g W KW` THEN
  REWRITE_TAC[wan_gweak] THEN DISCH_THEN(MP_TAC o SPEC `phi:real^(N,1)finite_sum->real`) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `R = \z. vsum(1..dimindex(:N))
              (\i. (b:real^(N,1)finite_sum->real^N) z$i %
                   (KW:num->real^(N,1)finite_sum->real^1) i z) +
            (c:real^(N,1)finite_sum->real) z % (W:real^(N,1)finite_sum->real^1) z +
            (f:real^(N,1)finite_sum->real^1) z` THEN
  ABBREV_TAC
   `H = \i z. vsum(1..dimindex(:N))
                (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j %
                     (KW:num->real^(N,1)finite_sum->real^1) j z) +
              (g:num->real^(N,1)finite_sum->real^1) i z` THEN
  SUBGOAL_THEN
   `(!z. vsum(1..dimindex(:N))
           (\i. (b:real^(N,1)finite_sum->real^N) z$i %
                (KW:num->real^(N,1)finite_sum->real^1) i z) +
         (c:real^(N,1)finite_sum->real) z % (W:real^(N,1)finite_sum->real^1) z +
         (f:real^(N,1)finite_sum->real^1) z = (R:real^(N,1)finite_sum->real^1) z) /\
    (!i z. vsum(1..dimindex(:N))
             (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j % KW j z) +
           (g:num->real^(N,1)finite_sum->real^1) i z =
           (H:num->real^(N,1)finite_sum->real^1) i z)`
  (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MAP_EVERY EXPAND_TAC ["R"; "H"] THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^(N,1)finite_sum) (R:real^(N,1)finite_sum->real^1)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `R:real^(N,1)finite_sum->real^1` (concl th) &&
      is_comb(concl th) && fst(dest_const(rator(rator(concl th)))) = "wan_lloc")) THEN
    REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\z. wan_dpart i phi z % (H:num->real^(N,1)finite_sum->real^1) i z)
              integrable_on (:real^(N,1)finite_sum) /\
            (\z. phi z % (dH:num->real^(N,1)finite_sum->real^1) i z)
              integrable_on (:real^(N,1)finite_sum) /\
            integral (:real^(N,1)finite_sum) (\z. wan_dpart i phi z % H i z) =
            --(integral (:real^(N,1)finite_sum) (\z. phi z % dH i z))`
  (LABEL_TAC "ih") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "hl" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `1 <= i /\ i <= dimindex(:N)`))) THEN
    STRIP_TAC THEN USE_THEN "pair" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `wan_lloc (:real^(N,1)finite_sum) ((H:num->real^(N,1)finite_sum->real^1) i)`))) THEN
    USE_THEN "pair" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `wan_lloc (:real^(N,1)finite_sum) ((dH:num->real^(N,1)finite_sum->real^1) i)`))) THEN
    SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(MP (SPEC `i:num` (ASSUME
      `!i. 1 <= i /\ i <= dimindex(:N)
           ==> wan_wpd (:real^(N,1)finite_sum) i ((H:num->real^(N,1)finite_sum->real^1) i)
                 ((dH:num->real^(N,1)finite_sum->real^1) i)`))
      (ASSUME `1 <= i /\ i <= dimindex(:N)`)) THEN
    REWRITE_TAC[wan_wpd] THEN DISCH_THEN(MP_TAC o SPEC `phi:real^(N,1)finite_sum->real` o
      CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. wan_dpart (dimindex(:N) + 1) phi z % (W:real^(N,1)finite_sum->real^1) z)
      integrable_on (:real^(N,1)finite_sum) /\
    (\z. phi z % (R:real^(N,1)finite_sum->real^1) z) integrable_on (:real^(N,1)finite_sum) /\
    (\z. vsum(1..dimindex(:N))
           (\i. wan_dpart i phi z % (H:num->real^(N,1)finite_sum->real^1) i z))
      integrable_on (:real^(N,1)finite_sum) /\
    (\z. vsum(1..dimindex(:N))
           (\i. phi z % (dH:num->real^(N,1)finite_sum->real^1) i z))
      integrable_on (:real^(N,1)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "pair" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `wan_lloc (:real^(N,1)finite_sum) (W:real^(N,1)finite_sum->real^1)`))) THEN
      SIMP_TAC[];
      USE_THEN "pair" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `wan_lloc (:real^(N,1)finite_sum) (R:real^(N,1)finite_sum->real^1)`))) THEN
      SIMP_TAC[];
      MP_TAC(ISPECL [`\i z. wan_dpart i phi z % (H:num->real^(N,1)finite_sum->real^1) i z`;
                     `(:real^(N,1)finite_sum)`; `1..dimindex(:N)`] INTEGRABLE_VSUM) THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "ih" (fun th -> SIMP_TAC[th]);
      MP_TAC(ISPECL [`\i z. phi z % (dH:num->real^(N,1)finite_sum->real^1) i z`;
                     `(:real^(N,1)finite_sum)`; `1..dimindex(:N)`] INTEGRABLE_VSUM) THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "ih" (fun th -> SIMP_TAC[th])];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. wan_dpart (dimindex(:N) + 1) phi z % (W:real^(N,1)finite_sum->real^1) z -
         vsum(1..dimindex(:N))
           (\i. wan_dpart i phi z % (H:num->real^(N,1)finite_sum->real^1) i z)`;
    `\z. phi z % (R:real^(N,1)finite_sum->real^1) z`; `(:real^(N,1)finite_sum)`]
   INTEGRAL_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`\z. wan_dpart (dimindex(:N) + 1) phi z % (W:real^(N,1)finite_sum->real^1) z`;
    `\z. vsum(1..dimindex(:N))
           (\i. wan_dpart i phi z % (H:num->real^(N,1)finite_sum->real^1) i z)`;
    `(:real^(N,1)finite_sum)`] INTEGRAL_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\i z. wan_dpart i phi z % (H:num->real^(N,1)finite_sum->real^1) i z`;
                 `(:real^(N,1)finite_sum)`; `1..dimindex(:N)`] INTEGRAL_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  ANTS_TAC THENL [USE_THEN "ih" (fun th -> SIMP_TAC[th]); ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. integral (:real^(N,1)finite_sum)
             (\z. wan_dpart i phi z % (H:num->real^(N,1)finite_sum->real^1) i z)) =
    --vsum(1..dimindex(:N))
        (\i. integral (:real^(N,1)finite_sum)
               (\z. phi z % (dH:num->real^(N,1)finite_sum->real^1) i z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VSUM_NEG] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN USE_THEN "ih" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; GSYM VSUM_LMUL] THEN
  MP_TAC(ISPECL
   [`\z. vsum(1..dimindex(:N))
           (\i. phi z % (dH:num->real^(N,1)finite_sum->real^1) i z)`;
    `\z. phi z % (R:real^(N,1)finite_sum->real^1) z`; `(:real^(N,1)finite_sum)`]
   INTEGRAL_ADD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\i z. phi z % (dH:num->real^(N,1)finite_sum->real^1) i z`;
                 `(:real^(N,1)finite_sum)`; `1..dimindex(:N)`] INTEGRAL_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  ANTS_TAC THENL [USE_THEN "ih" (fun th -> SIMP_TAC[th]); ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC(VECTOR_ARITH `(a:real^N) - --d + c = vec 0 ==> a = --(d + c)`));;

let WAN_CC_SMOOTH = prove
 (`!m:real^M->real. wan_cc m ==> smooth_map_on (:real^M) (\x. lift(m x))`,
  SIMP_TAC[wan_cc]);;

let WAN_WPD_LINCOMB = prove
 (`!(m:num->real^M->real) (u:num->real^M->real^K) ut h ht k n.
     (!j. 1 <= j /\ j <= n
          ==> smooth_map_on (:real^M) (\x. lift(m j x)) /\
              wan_wpd (:real^M) k (u j) (ut j)) /\
     wan_wpd (:real^M) k h ht
     ==> wan_wpd (:real^M) k (\x. vsum(1..n) (\j. m j x % u j x) + h x)
           (\x. vsum(1..n) (\j. wan_dpart k (m j) x % u j x + m j x % ut j x) + ht x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `k:num`;
                 `\x. vsum(1..n) (\j. (m:num->real^M->real) j x % (u:num->real^M->real^K) j x)`;
                 `\x. vsum(1..n) (\j. wan_dpart k ((m:num->real^M->real) j) x %
                                      (u:num->real^M->real^K) j x + m j x % ut j x)`;
                 `h:real^M->real^K`; `ht:real^M->real^K`] WAN_WPD_ADD) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\j x. (m:num->real^M->real) j x % (u:num->real^M->real^K) j x`;
                 `\j x. wan_dpart k ((m:num->real^M->real) j) x %
                        (u:num->real^M->real^K) j x + m j x % ut j x`;
                 `k:num`; `1..n`] WAN_WPD_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_MUL_SMOOTH THEN
  ASM_SIMP_TAC[OPEN_UNIV; ETA_AX]);;

let WAN_TEST_SPLIT3 = prove
 (`!(phi:real^M->real) (v:real^M->real^K) H R t n.
     wan_test (:real^M) phi /\ wan_lloc (:real^M) v /\ wan_lloc (:real^M) R /\
     (!i. 1 <= i /\ i <= n ==> wan_lloc (:real^M) (H i))
     ==> integral (:real^M)
           (\z. wan_dpart t phi z % v z - vsum(1..n) (\i. wan_dpart i phi z % H i z) +
                phi z % R z) =
         integral (:real^M) (\z. wan_dpart t phi z % v z) -
         vsum(1..n) (\i. integral (:real^M) (\z. wan_dpart i phi z % H i z)) +
         integral (:real^M) (\z. phi z % R z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!u:real^M->real^K.
      wan_lloc (:real^M) u
      ==> (\z. phi z % u z) integrable_on (:real^M) /\
          (!i. (\z. wan_dpart i phi z % u z) integrable_on (:real^M))`
  (LABEL_TAC "pair") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(:real^M)`; `phi:real^M->real`; `u:real^M->real^K`] WAN_TEST_PAIRING) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. wan_dpart t phi z % (v:real^M->real^K) z) integrable_on (:real^M) /\
    (\z. phi z % (R:real^M->real^K) z) integrable_on (:real^M) /\
    (!i. 1 <= i /\ i <= n
         ==> (\z. wan_dpart i phi z % (H:num->real^M->real^K) i z) integrable_on (:real^M)) /\
    (\z. vsum(1..n) (\i. wan_dpart i phi z % (H:num->real^M->real^K) i z))
      integrable_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "pair" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `wan_lloc (:real^M) (v:real^M->real^K)`))) THEN SIMP_TAC[];
      USE_THEN "pair" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `wan_lloc (:real^M) (R:real^M->real^K)`))) THEN SIMP_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "pair" MP_TAC THEN ASM_SIMP_TAC[ETA_AX];
      MP_TAC(ISPECL [`\i z. wan_dpart i phi z % (H:num->real^M->real^K) i z`;
                     `(:real^M)`; `1..n`] INTEGRABLE_VSUM) THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN USE_THEN "pair" MP_TAC THEN ASM_SIMP_TAC[ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. wan_dpart t phi z % (v:real^M->real^K) z -
         vsum(1..n) (\i. wan_dpart i phi z % (H:num->real^M->real^K) i z)`;
    `\z. phi z % (R:real^M->real^K) z`; `(:real^M)`] INTEGRAL_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`\z. wan_dpart t phi z % (v:real^M->real^K) z`;
    `\z. vsum(1..n) (\i. wan_dpart i phi z % (H:num->real^M->real^K) i z)`;
    `(:real^M)`] INTEGRAL_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\i z. wan_dpart i phi z % (H:num->real^M->real^K) i z`;
                 `(:real^M)`; `1..n`] INTEGRAL_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ASM_SIMP_TAC[]);;

let WAN_WPD_LLOC = prove
 (`!(s:real^M->bool) k (u:real^M->real^K) v.
     wan_wpd s k u v ==> wan_lloc s u /\ wan_lloc s v`,
  SIMP_TAC[wan_wpd]);;

let WAN_LLOC_TAC =
  REPEAT((MATCH_MP_TAC WAN_LLOC_ADD THEN CONJ_TAC) ORELSE
         (MATCH_MP_TAC WAN_LLOC_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
          REPEAT STRIP_TAC THEN REWRITE_TAC[]) ORELSE
         (USE_THEN "cm" MATCH_MP_TAC THEN CONJ_TAC)) THEN
  ASM_SIMP_TAC[WAN_CC_DPART; ETA_AX];;

let WAN_GWEAK_TDIFF = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
    (c:real^(N,1)finite_sum->real) (f:real^(N,1)finite_sum->real^1)
    (g:num->real^(N,1)finite_sum->real^1) (W:real^(N,1)finite_sum->real^1) KW Wt KWt ft gt.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> wan_cc (\z. a z$i$j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_cc (\z. b z$i)) /\ wan_cc c /\
     wan_gweak a b c f g W KW /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_wpd (:real^(N,1)finite_sum) j W (KW j)) /\
     wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1) W Wt /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_wpd (:real^(N,1)finite_sum) j Wt (KWt j)) /\
     wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1) f ft /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1) (g i) (gt i))
     ==> wan_gweak a b c
           (\z. ft z +
                vsum(1..dimindex(:N))
                  (\i. wan_dpart (dimindex(:N) + 1) (\y. b y$i) z % KW i z) +
                wan_dpart (dimindex(:N) + 1) c z % W z)
           (\i z. gt i z +
                  vsum(1..dimindex(:N))
                    (\j. wan_dpart (dimindex(:N) + 1) (\y. a y$i$j) z % KW j z))
           Wt KWt`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1)
              ((KW:num->real^(N,1)finite_sum->real^1) j)
              ((KWt:num->real^(N,1)finite_sum->real^1) j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_COMMUTE THEN
    MAP_EVERY EXISTS_TAC [`W:real^(N,1)finite_sum->real^1`; `Wt:real^(N,1)finite_sum->real^1`;
                          `j:num`] THEN
    ASM_SIMP_TAC[WAN_TIME_INDEX; WAN_SPACE_INDEX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1)
              (\z. vsum(1..dimindex(:N))
                     (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j %
                          (KW:num->real^(N,1)finite_sum->real^1) j z) +
                   (g:num->real^(N,1)finite_sum->real^1) i z)
              (\z. vsum(1..dimindex(:N))
                     (\j. wan_dpart (dimindex(:N) + 1) (\z. a z$i$j) z % KW j z +
                          a z$i$j % (KWt:num->real^(N,1)finite_sum->real^1) j z) +
                   (gt:num->real^(N,1)finite_sum->real^1) i z)`
  (LABEL_TAC "Ht") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\j z. (a:real^(N,1)finite_sum->real^N^N) z$i$j`;
                   `KW:num->real^(N,1)finite_sum->real^1`;
                   `KWt:num->real^(N,1)finite_sum->real^1`;
                   `(g:num->real^(N,1)finite_sum->real^1) i`;
                   `(gt:num->real^(N,1)finite_sum->real^1) i`;
                   `dimindex(:N) + 1`; `dimindex(:N)`] WAN_WPD_LINCOMB) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[WAN_CC_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1)
      (\z. vsum(1..dimindex(:N))
             (\i. (b:real^(N,1)finite_sum->real^N) z$i %
                  (KW:num->real^(N,1)finite_sum->real^1) i z) +
           (c:real^(N,1)finite_sum->real) z % (W:real^(N,1)finite_sum->real^1) z +
           (f:real^(N,1)finite_sum->real^1) z)
      (\z. vsum(1..dimindex(:N))
             (\i. wan_dpart (dimindex(:N) + 1) (\z. b z$i) z % KW i z +
                  b z$i % (KWt:num->real^(N,1)finite_sum->real^1) i z) +
           ((wan_dpart (dimindex(:N) + 1) c z % W z +
             c z % (Wt:real^(N,1)finite_sum->real^1) z) +
            (ft:real^(N,1)finite_sum->real^1) z))`
  (LABEL_TAC "Rt") THENL
   [MP_TAC(ISPECL [`\i z. (b:real^(N,1)finite_sum->real^N) z$i`;
                   `KW:num->real^(N,1)finite_sum->real^1`;
                   `KWt:num->real^(N,1)finite_sum->real^1`;
                   `\z. (c:real^(N,1)finite_sum->real) z % (W:real^(N,1)finite_sum->real^1) z +
                        (f:real^(N,1)finite_sum->real^1) z`;
                   `\z. (wan_dpart (dimindex(:N) + 1) (c:real^(N,1)finite_sum->real) z %
                         (W:real^(N,1)finite_sum->real^1) z +
                         c z % (Wt:real^(N,1)finite_sum->real^1) z) +
                        (ft:real^(N,1)finite_sum->real^1) z`;
                   `dimindex(:N) + 1`; `dimindex(:N)`] WAN_WPD_LINCOMB) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[WAN_CC_SMOOTH] THEN
    MP_TAC(ISPECL [`(:real^(N,1)finite_sum)`; `dimindex(:N) + 1`;
                   `\z. (c:real^(N,1)finite_sum->real) z % (W:real^(N,1)finite_sum->real^1) z`;
                   `\z. wan_dpart (dimindex(:N) + 1) (c:real^(N,1)finite_sum->real) z %
                        (W:real^(N,1)finite_sum->real^1) z +
                        c z % (Wt:real^(N,1)finite_sum->real^1) z`;
                   `f:real^(N,1)finite_sum->real^1`; `ft:real^(N,1)finite_sum->real^1`]
                  WAN_WPD_ADD) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_WPD_MUL_SMOOTH THEN ASM_SIMP_TAC[OPEN_UNIV; WAN_CC_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_lloc (:real^(N,1)finite_sum) (W:real^(N,1)finite_sum->real^1) /\
    wan_lloc (:real^(N,1)finite_sum) (Wt:real^(N,1)finite_sum->real^1) /\
    wan_lloc (:real^(N,1)finite_sum) (f:real^(N,1)finite_sum->real^1) /\
    wan_lloc (:real^(N,1)finite_sum) (ft:real^(N,1)finite_sum->real^1) /\
    (!j. 1 <= j /\ j <= dimindex(:N)
         ==> wan_lloc (:real^(N,1)finite_sum) ((KW:num->real^(N,1)finite_sum->real^1) j) /\
             wan_lloc (:real^(N,1)finite_sum) ((KWt:num->real^(N,1)finite_sum->real^1) j)) /\
    (!i. 1 <= i /\ i <= dimindex(:N)
         ==> wan_lloc (:real^(N,1)finite_sum) ((g:num->real^(N,1)finite_sum->real^1) i) /\
             wan_lloc (:real^(N,1)finite_sum) ((gt:num->real^(N,1)finite_sum->real^1) i))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(MATCH_MP WAN_WPD_LLOC (ASSUME
        `wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1) (W:real^(N,1)finite_sum->real^1) Wt`)) THEN
      SIMP_TAC[];
      MP_TAC(MATCH_MP WAN_WPD_LLOC (ASSUME
        `wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1) (W:real^(N,1)finite_sum->real^1) Wt`)) THEN
      SIMP_TAC[];
      MP_TAC(MATCH_MP WAN_WPD_LLOC (ASSUME
        `wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1) (f:real^(N,1)finite_sum->real^1) ft`)) THEN
      SIMP_TAC[];
      MP_TAC(MATCH_MP WAN_WPD_LLOC (ASSUME
        `wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1) (f:real^(N,1)finite_sum->real^1) ft`)) THEN
      SIMP_TAC[];
      GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
       [MP_TAC(MATCH_MP WAN_WPD_LLOC (MP (SPEC `j:num` (ASSUME
          `!j. 1 <= j /\ j <= dimindex(:N)
               ==> wan_wpd (:real^(N,1)finite_sum) j (W:real^(N,1)finite_sum->real^1)
                     ((KW:num->real^(N,1)finite_sum->real^1) j)`))
          (ASSUME `1 <= j /\ j <= dimindex(:N)`))) THEN SIMP_TAC[];
        MP_TAC(MATCH_MP WAN_WPD_LLOC (MP (SPEC `j:num` (ASSUME
          `!j. 1 <= j /\ j <= dimindex(:N)
               ==> wan_wpd (:real^(N,1)finite_sum) j (Wt:real^(N,1)finite_sum->real^1)
                     ((KWt:num->real^(N,1)finite_sum->real^1) j)`))
          (ASSUME `1 <= j /\ j <= dimindex(:N)`))) THEN SIMP_TAC[]];
      GEN_TAC THEN DISCH_TAC THEN
      MP_TAC(MATCH_MP WAN_WPD_LLOC (MP (SPEC `i:num` (ASSUME
        `!i. 1 <= i /\ i <= dimindex(:N)
             ==> wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1)
                   ((g:num->real^(N,1)finite_sum->real^1) i)
                   ((gt:num->real^(N,1)finite_sum->real^1) i)`))
        (ASSUME `1 <= i /\ i <= dimindex(:N)`))) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(m:real^(N,1)finite_sum->real) (u:real^(N,1)finite_sum->real^1).
      wan_cc m /\ wan_lloc (:real^(N,1)finite_sum) u
      ==> wan_lloc (:real^(N,1)finite_sum) (\z. m z % u z)`
  (LABEL_TAC "cm") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LLOC_CONT_MUL THEN
    ASM_SIMP_TAC[WAN_CC_CONTINUOUS];
    ALL_TAC] THEN
  REWRITE_TAC[wan_gweak] THEN X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `wan_test (:real^(N,1)finite_sum) (wan_dpart (dimindex(:N) + 1) phi) /\
                (!i. wan_test (:real^(N,1)finite_sum) (wan_dpart i phi))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_TEST_DPART_TEST]; ALL_TAC] THEN
  UNDISCH_TAC `wan_gweak (a:real^(N,1)finite_sum->real^N^N) b c f g W KW` THEN
  REWRITE_TAC[wan_gweak] THEN
  DISCH_THEN(MP_TAC o SPEC `wan_dpart (dimindex(:N) + 1) (phi:real^(N,1)finite_sum->real)`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`wan_dpart (dimindex(:N) + 1) (phi:real^(N,1)finite_sum->real)`;
    `W:real^(N,1)finite_sum->real^1`;
    `\i z. vsum(1..dimindex(:N))
             (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j %
                  (KW:num->real^(N,1)finite_sum->real^1) j z) +
           (g:num->real^(N,1)finite_sum->real^1) i z`;
    `\z. vsum(1..dimindex(:N))
           (\i. (b:real^(N,1)finite_sum->real^N) z$i %
                (KW:num->real^(N,1)finite_sum->real^1) i z) +
         (c:real^(N,1)finite_sum->real) z % (W:real^(N,1)finite_sum->real^1) z +
         (f:real^(N,1)finite_sum->real^1) z`;
    `dimindex(:N) + 1`; `dimindex(:N)`] WAN_TEST_SPLIT3) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN WAN_LLOC_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL
   [`phi:real^(N,1)finite_sum->real`; `Wt:real^(N,1)finite_sum->real^1`;
    `\i z. vsum(1..dimindex(:N))
             (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j %
                  (KWt:num->real^(N,1)finite_sum->real^1) j z) +
           ((gt:num->real^(N,1)finite_sum->real^1) i z +
            vsum(1..dimindex(:N))
              (\j. wan_dpart (dimindex(:N) + 1) (\y. a y$i$j) z %
                   (KW:num->real^(N,1)finite_sum->real^1) j z))`;
    `\z. vsum(1..dimindex(:N))
           (\i. (b:real^(N,1)finite_sum->real^N) z$i %
                (KWt:num->real^(N,1)finite_sum->real^1) i z) +
         (c:real^(N,1)finite_sum->real) z % (Wt:real^(N,1)finite_sum->real^1) z +
         ((ft:real^(N,1)finite_sum->real^1) z +
          vsum(1..dimindex(:N))
            (\i. wan_dpart (dimindex(:N) + 1) (\y. b y$i) z %
                 (KW:num->real^(N,1)finite_sum->real^1) i z) +
          wan_dpart (dimindex(:N) + 1) c z % (W:real^(N,1)finite_sum->real^1) z)`;
    `dimindex(:N) + 1`; `dimindex(:N)`] WAN_TEST_SPLIT3) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN WAN_LLOC_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^(N,1)finite_sum)
      (\z. wan_dpart (dimindex(:N) + 1) (wan_dpart (dimindex(:N) + 1) phi) z %
           (W:real^(N,1)finite_sum->real^1) z) =
    --(integral (:real^(N,1)finite_sum)
         (\z. wan_dpart (dimindex(:N) + 1) phi z % (Wt:real^(N,1)finite_sum->real^1) z))`
  SUBST1_TAC THENL
   [MP_TAC(ASSUME `wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1)
                     (W:real^(N,1)finite_sum->real^1) Wt`) THEN
    REWRITE_TAC[wan_wpd] THEN
    DISCH_THEN(MP_TAC o SPEC `wan_dpart (dimindex(:N) + 1) (phi:real^(N,1)finite_sum->real)` o
      CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^(N,1)finite_sum)
      (\z. wan_dpart (dimindex(:N) + 1) phi z %
           (vsum(1..dimindex(:N))
              (\i. (b:real^(N,1)finite_sum->real^N) z$i %
                   (KW:num->real^(N,1)finite_sum->real^1) i z) +
            (c:real^(N,1)finite_sum->real) z % (W:real^(N,1)finite_sum->real^1) z +
            (f:real^(N,1)finite_sum->real^1) z)) =
    --(integral (:real^(N,1)finite_sum)
         (\z. phi z %
              (vsum(1..dimindex(:N)) (\i. b z$i % (KWt:num->real^(N,1)finite_sum->real^1) i z) +
               c z % (Wt:real^(N,1)finite_sum->real^1) z +
               ((ft:real^(N,1)finite_sum->real^1) z +
                vsum(1..dimindex(:N))
                  (\i. wan_dpart (dimindex(:N) + 1) (\y. b y$i) z % KW i z) +
                wan_dpart (dimindex(:N) + 1) c z % W z))))`
  SUBST1_TAC THENL
   [USE_THEN "Rt" MP_TAC THEN REWRITE_TAC[wan_wpd] THEN
    DISCH_THEN(MP_TAC o SPEC `phi:real^(N,1)finite_sum->real` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[VSUM_ADD_NUMSEG] THEN
    MATCH_ACCEPT_TAC(VECTOR_ARITH
     `((p:real^N) + q) + ((r + s) + t) = q + s + (t + p + r)`);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. integral (:real^(N,1)finite_sum)
             (\z. wan_dpart i (wan_dpart (dimindex(:N) + 1) phi) z %
                  (vsum(1..dimindex(:N))
                     (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j %
                          (KW:num->real^(N,1)finite_sum->real^1) j z) +
                   (g:num->real^(N,1)finite_sum->real^1) i z))) =
    --vsum(1..dimindex(:N))
        (\i. integral (:real^(N,1)finite_sum)
               (\z. wan_dpart i phi z %
                    (vsum(1..dimindex(:N))
                       (\j. a z$i$j % (KWt:num->real^(N,1)finite_sum->real^1) j z) +
                     ((gt:num->real^(N,1)finite_sum->real^1) i z +
                      vsum(1..dimindex(:N))
                        (\j. wan_dpart (dimindex(:N) + 1) (\y. a y$i$j) z % KW j z)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VSUM_NEG] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!z. wan_dpart i (wan_dpart (dimindex(:N) + 1) phi) z =
          wan_dpart (dimindex(:N) + 1) (wan_dpart i phi) (z:real^(N,1)finite_sum)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC WAN_DPART_SYM THEN
      ASM_SIMP_TAC[WAN_TIME_INDEX; WAN_SPACE_INDEX];
      ALL_TAC] THEN
    USE_THEN "Ht" (fun th -> MP_TAC(MP (SPEC `i:num` th)
      (CONJ (ASSUME `1 <= i`) (ASSUME `i <= dimindex(:N)`)))) THEN
    REWRITE_TAC[wan_wpd] THEN
    DISCH_THEN(MP_TAC o SPEC `wan_dpart i (phi:real^(N,1)finite_sum->real)` o
      CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[VSUM_ADD_NUMSEG] THEN
    MATCH_ACCEPT_TAC(VECTOR_ARITH `((p:real^N) + q) + r = q + (r + p)`);
    ALL_TAC] THEN
  MATCH_ACCEPT_TAC(VECTOR_ARITH
   `--(a:real^N) - --s + --c = vec 0 ==> a - s + c = vec 0`));;

(* ========================================================================= *)
(* The time bootstrap.  Data with m time derivatives (each                  *)
(* of all spatial orders) give a solution with m + 1 time derivatives; data *)
(* of all orders give a solution in every isotropic class.                   *)
(* ========================================================================= *)

let WAN_HXA_TAC =
  REPEAT((MATCH_MP_TAC WAN_HXA_ADD THEN CONJ_TAC) ORELSE
         (MATCH_MP_TAC WAN_HXA_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
          REPEAT STRIP_TAC THEN REWRITE_TAC[]) ORELSE
         (MATCH_MP_TAC WAN_HXA_MUL THEN CONJ_TAC)) THEN
  ASM_SIMP_TAC[WAN_CC_DPART; ETA_AX];;

let WAN_HT_TAC =
  REPEAT((MATCH_MP_TAC WAN_HT_ADD THEN CONJ_TAC) ORELSE
         (MATCH_MP_TAC WAN_HT_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
          REPEAT STRIP_TAC THEN REWRITE_TAC[]) ORELSE
         (MATCH_MP_TAC WAN_HT_MUL THEN CONJ_TAC)) THEN
  ASM_SIMP_TAC[WAN_CC_DPART; ETA_AX];;

let WAN_TIME_BOOT = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
    (c:real^(N,1)finite_sum->real).
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> wan_cc (\z. a z$i$j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_cc (\z. b z$i)) /\ wan_cc c
     ==> !m (f:real^(N,1)finite_sum->real^1) (g:num->real^(N,1)finite_sum->real^1)
           (W:real^(N,1)finite_sum->real^1) KW.
           wan_gweak a b c f g W KW /\
           (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_wpd (:real^(N,1)finite_sum) j W (KW j)) /\
           wan_hxa W /\ wan_ht m f /\
           (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_ht m (g i))
           ==> wan_ht (SUC m) W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!j. 1 <= j /\ j <= dimindex(:N) ==> wan_hxa ((KW:num->real^(N,1)finite_sum->real^1) j)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_HXA_DERIV THEN
      MAP_EVERY EXISTS_TAC [`W:real^(N,1)finite_sum->real^1`; `j:num`] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. 1 <= i /\ i <= dimindex(:N)
          ==> ?dH. wan_wpd (:real^(N,1)finite_sum) i
                     (\z. vsum(1..dimindex(:N))
                            (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j %
                                 (KW:num->real^(N,1)finite_sum->real^1) j z) +
                          (g:num->real^(N,1)finite_sum->real^1) i z) dH /\
                   wan_hxa dH`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_HXA_HAS_DERIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WAN_HXA_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC WAN_HXA_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC WAN_HXA_MUL THEN
        ASM_SIMP_TAC[ETA_AX];
        REWRITE_TAC[ETA_AX] THEN
        MP_TAC(MP (SPEC `i:num` (ASSUME
          `!i. 1 <= i /\ i <= dimindex(:N)
               ==> wan_ht 0 ((g:num->real^(N,1)finite_sum->real^1) i)`))
          (CONJ (ASSUME `1 <= i`) (ASSUME `i <= dimindex(:N)`))) THEN
        REWRITE_TAC[wan_ht]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `dH:num->real^(N,1)finite_sum->real^1` o
      REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wan_ht]) THEN
    MP_TAC(ISPECL [`a:real^(N,1)finite_sum->real^N^N`; `b:real^(N,1)finite_sum->real^N`;
                   `c:real^(N,1)finite_sum->real`; `f:real^(N,1)finite_sum->real^1`;
                   `g:num->real^(N,1)finite_sum->real^1`; `W:real^(N,1)finite_sum->real^1`;
                   `KW:num->real^(N,1)finite_sum->real^1`;
                   `dH:num->real^(N,1)finite_sum->real^1`] WAN_GWEAK_TDER) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[WAN_CC_CONTINUOUS; WAN_HXA_LLOC; ETA_AX];
      DISCH_TAC] THEN
    REWRITE_TAC[wan_ht] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC
     `\z. vsum(1..dimindex(:N)) (\i. (dH:num->real^(N,1)finite_sum->real^1) i z) +
          (vsum(1..dimindex(:N))
             (\i. (b:real^(N,1)finite_sum->real^N) z$i %
                  (KW:num->real^(N,1)finite_sum->real^1) i z) +
           (c:real^(N,1)finite_sum->real) z % (W:real^(N,1)finite_sum->real^1) z +
           (f:real^(N,1)finite_sum->real^1) z)` THEN
    ASM_REWRITE_TAC[] THEN WAN_HXA_TAC;
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_ht (SUC m) (W:real^(N,1)finite_sum->real^1)` ASSUME_TAC THENL
   [USE_THEN "IH" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`f:real^(N,1)finite_sum->real^1`; `g:num->real^(N,1)finite_sum->real^1`;
                          `KW:num->real^(N,1)finite_sum->real^1`] THEN
    ASM_SIMP_TAC[WAN_HT_MONO];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[wan_ht] (ASSUME `wan_ht (SUC m) (W:real^(N,1)finite_sum->real^1)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `Wt:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?KWt. !j. 1 <= j /\ j <= dimindex(:N)
              ==> wan_wpd (:real^(N,1)finite_sum) j (Wt:real^(N,1)finite_sum->real^1)
                    (KWt j) /\
                  wan_hxa (KWt j)`
  (X_CHOOSE_TAC `KWt:num->real^(N,1)finite_sum->real^1`) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC WAN_HXA_HAS_DERIV THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC WAN_HT_HXA THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[wan_ht] (ASSUME `wan_ht (SUC m) (f:real^(N,1)finite_sum->real^1)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `ft:real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `?gt. !i. 1 <= i /\ i <= dimindex(:N)
             ==> wan_wpd (:real^(N,1)finite_sum) (dimindex(:N) + 1)
                   ((g:num->real^(N,1)finite_sum->real^1) i) (gt i) /\
                 wan_ht m (gt i)`
  (X_CHOOSE_TAC `gt:num->real^(N,1)finite_sum->real^1`) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(MP (SPEC `i:num` (ASSUME
      `!i. 1 <= i /\ i <= dimindex(:N)
           ==> wan_ht (SUC m) ((g:num->real^(N,1)finite_sum->real^1) i)`))
      (CONJ (ASSUME `1 <= i`) (ASSUME `i <= dimindex(:N)`))) THEN
    REWRITE_TAC[wan_ht] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> wan_ht (SUC m) ((KW:num->real^(N,1)finite_sum->real^1) j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_HT_DERIV_X THEN
    MAP_EVERY EXISTS_TAC [`W:real^(N,1)finite_sum->real^1`; `j:num`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [CONJUNCT2 wan_ht] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `Wt:real^(N,1)finite_sum->real^1` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "IH" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\z. (ft:real^(N,1)finite_sum->real^1) z +
         vsum(1..dimindex(:N))
           (\i. wan_dpart (dimindex(:N) + 1) (\y. (b:real^(N,1)finite_sum->real^N) y$i) z %
                (KW:num->real^(N,1)finite_sum->real^1) i z) +
         wan_dpart (dimindex(:N) + 1) (c:real^(N,1)finite_sum->real) z %
         (W:real^(N,1)finite_sum->real^1) z`;
    `\i z. (gt:num->real^(N,1)finite_sum->real^1) i z +
           vsum(1..dimindex(:N))
             (\j. wan_dpart (dimindex(:N) + 1)
                    (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j) z %
                  (KW:num->real^(N,1)finite_sum->real^1) j z)`;
    `KWt:num->real^(N,1)finite_sum->real^1`] THEN
  ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_GWEAK_TDIFF THEN
    MAP_EVERY EXISTS_TAC [`f:real^(N,1)finite_sum->real^1`;
                          `g:num->real^(N,1)finite_sum->real^1`] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC WAN_HT_HXA THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[];
    WAN_HT_TAC THEN ASM_SIMP_TAC[WAN_HT_MONO];
    REPEAT STRIP_TAC THEN WAN_HT_TAC THEN ASM_SIMP_TAC[WAN_HT_MONO]]);;

let WAN_TIME_ALL = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
    (c:real^(N,1)finite_sum->real) (f:real^(N,1)finite_sum->real^1)
    (g:num->real^(N,1)finite_sum->real^1) (W:real^(N,1)finite_sum->real^1) KW.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> wan_cc (\z. a z$i$j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_cc (\z. b z$i)) /\ wan_cc c /\
     wan_gweak a b c f g W KW /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_wpd (:real^(N,1)finite_sum) j W (KW j)) /\
     wan_hxa W /\ (!m. wan_ht m f) /\
     (!m i. 1 <= i /\ i <= dimindex(:N) ==> wan_ht m (g i))
     ==> (!m. wan_ht m W) /\ (!s. wan_hd (1..dimindex(:(N,1)finite_sum)) s W)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m. wan_ht m (W:real^(N,1)finite_sum->real^1)` ASSUME_TAC THENL
   [INDUCT_TAC THENL [ASM_REWRITE_TAC[wan_ht]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^(N,1)finite_sum->real^N^N`; `b:real^(N,1)finite_sum->real^N`;
                   `c:real^(N,1)finite_sum->real`] WAN_TIME_BOOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`f:real^(N,1)finite_sum->real^1`; `g:num->real^(N,1)finite_sum->real^1`;
                          `KW:num->real^(N,1)finite_sum->real^1`] THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[WAN_HT_ALL_HD]]);;

