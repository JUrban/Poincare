(* ========================================================================= *)
(* pc_p2a_l314: MT Lemma 3.14, under nonnegative Ricci curvature distances   *)
(* do not increase along a Ricci flow.  For a fixed vector w at a point z,   *)
(* d/ds g(s)(w,w) = -2 Ric(w,w) <= 0 (RFA_QFORM_DERIV), so the speed         *)
(* and the length of every C^1 curve do not increase in time; the distance   *)
(* is the infimum of the lengths over the same class of curves at both times *)
(* (the infimum of the empty set at both times for points that are not       *)
(* joinable).                                                                *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;
needs "src/pc_rfa_shi.ml";;

prioritize_real();;
type_invention_error := true;;

(* The quadratic form of the metric at a point does not increase.           *)

let P2AR_QFORM_DECR = prove
 (`!top atlas a b (g:real->A->real^N^N) t1 t2 z w.
        ricci_flow_on (top,atlas) a b g /\
        (!t. a < t /\ t < b ==> &0 <= mfd_ricci atlas (g t) z w w) /\
        a < t1 /\ t1 <= t2 /\ t2 < b /\ z IN topspace top
        ==> w dot (g t2 z ** w) <= w dot (g t1 z ** w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. --(w dot ((g:real->A->real^N^N) s z ** w))`;
                 `\s. &2 * mfd_ricci atlas ((g:real->A->real^N^N) s) z w w`;
                 `real_interval[t1,t2]`; `t1:real`; `t2:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL; REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`; `g:real->A->real^N^N`; `s:real`; `z:A`;
                     `w:real^N`] RFA_QFORM_DERIV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP HAS_REAL_DERIVATIVE_NEG) THEN
      MATCH_MP_TAC(MESON[]
       `(x:real) = y
        ==> (f has_real_derivative x) (net:(real)net)
            ==> (f has_real_derivative y) net`) THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* Speeds and lengths of a fixed C^1 curve do not increase.                 *)

let P2AR_SPEED_DECR = prove
 (`!top atlas a b (g:real->A->real^N^N) t1 t2 (gamma:real->A) c d s.
        ricci_flow_on (top,atlas) a b g /\
        (!t z v. a < t /\ t < b /\ z IN topspace top
                 ==> &0 <= mfd_ricci atlas (g t) z v v) /\
        a < t1 /\ t1 <= t2 /\ t2 < b /\
        mfd_c1_curve (top,atlas) gamma c d /\ s IN real_interval[c,d]
        ==> mfd_speed atlas (g t2) gamma c d s <= mfd_speed atlas (g t1) gamma c d s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_speed] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC P2AR_QFORM_DECR THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) s IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `c:real`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let P2AR_LENGTH_DECR = prove
 (`!top atlas a b (g:real->A->real^N^N) t1 t2 (gamma:real->A) c d.
        ricci_flow_on (top,atlas) a b g /\
        (!t z v. a < t /\ t < b /\ z IN topspace top
                 ==> &0 <= mfd_ricci atlas (g t) z v v) /\
        a < t1 /\ t1 <= t2 /\ t2 < b /\
        mfd_c1_curve (top,atlas) gamma c d
        ==> mfd_length atlas (g t2) gamma c d <= mfd_length atlas (g t1) gamma c d`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2AR_SPEED_DECR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem (the statement P2_LEMMA_3_14_STATEMENT of pc_p3_iface).  *)
(* ------------------------------------------------------------------------- *)

let P2AR_LEMMA_3_14 = prove
 (`!u:A->bool. P2_LEMMA_3_14_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2_LEMMA_3_14_STATEMENT; mfd_dist] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `t1:real`; `t2:real`; `x:A`; `y:A`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  ASM_CASES_TAC
   `?gamma:real->A.
       mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) gamma (&0) (&1) /\
       gamma(&0) = x /\ gamma(&1) = y`
  THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `!t. {mfd_length atlas ((g:real->A->real^3^3) t) gamma (&0) (&1) | gamma |
           mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
           gamma(&0) = x /\ gamma(&1) = y} = {}`
     (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
    GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `gamma0:real->A` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length atlas ((g:real->A->real^3^3) t2) gam (&0) (&1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
     [EXISTS_TAC `&0` THEN X_GEN_TAC `l':real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `gamma':real->A` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_LENGTH_POS_LE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `gam:real->A` THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC P2AR_LENGTH_DECR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[]]);;

