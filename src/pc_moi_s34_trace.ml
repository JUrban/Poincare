(* ========================================================================= *)
(* pc_moi_s34_trace: Moise Sec 34, Lemma 11, p.244.  Main theorem TRACE :  *)
(* |- MOI_S34_TRACE (pc_moi_s34_stmt.ml), with 28.8 in the used form       *)
(* (MOISE_288_STATEMENT) as antecedent.  Route: a three-sector map from the *)
(* face torus to the circle; along a trace component J the lift moves by   *)
(* the same third at every rim crossing (Lemma 10 and the crossing         *)
(* property), so its winding is m/3 for m rim points on J; 28.8 and the    *)
(* core loop of winding 1 give m = 3.                                      *)
(* ========================================================================= *)

needs "src/pc_moi_s34_l910.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Equal steps along a finite set of reals.                                  *)
(* ------------------------------------------------------------------------- *)

let moi_s4t_gap = new_definition
 `moi_s4t_gap (r:real->bool) a b <=>
    a IN r /\ b IN r /\ a < b /\ !x. x IN r ==> ~(a < x /\ x < b)`;;

let MOI_S4T_GAP_PAIR = prove
 (`!a b u v. a < b ==> (moi_s4t_gap {a,b} u v <=> u = a /\ v = b)`,
  REWRITE_TAC[moi_s4t_gap; IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
    REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_LT_REFL]]);;

let MOI_S4T_SUP_INF_PAIR = prove
 (`!a b. a < b ==> sup {a,b} = b /\ inf {a,b} = a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC[SUP_INSERT_FINITE; INF_INSERT_FINITE; FINITE_SING; NOT_INSERT_EMPTY;
           SUP_SING; INF_SING] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S4T_STEPS_INDUCT = prove
 (`!n (r:real->bool) (f:real->complex) d.
     r HAS_SIZE (n + 2) /\
     (!a b. moi_s4t_gap r a b ==> f b - f a = d \/ f b - f a = --d) /\
     (!a b c. moi_s4t_gap r a b /\ moi_s4t_gap r b c ==> f c - f b = f b - f a)
     ==> ?e. (e = d \/ e = --d) /\
             (!a b. moi_s4t_gap r a b ==> f b - f a = e) /\
             f (sup r) - f (inf r) = Cx(&(n + 1)) * e`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:real` (X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC))
      STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `?a b. a < b /\ {x:real,y} = {a,b}`
     (X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THENL
     [ASM_CASES_TAC `x:real < y` THENL
       [MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN ASM_REWRITE_TAC[];
        MAP_EVERY EXISTS_TAC [`y:real`; `x:real`] THEN CONJ_TAC THENL
         [UNDISCH_TAC `~(x:real = y)` THEN UNDISCH_TAC `~(x:real < y)` THEN REAL_ARITH_TAC;
          SET_TAC[]]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S4T_GAP_PAIR; MOI_S4T_SUP_INF_PAIR] THEN
    EXISTS_TAC `(f:real->complex) b - f a` THEN
    REWRITE_TAC[COMPLEX_MUL_LID] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_SIMP_TAC[MOI_S4T_GAP_PAIR];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (r:real->bool) /\ CARD r = n + 3` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(r:real->bool) HAS_SIZE (SUC n + 2)` THEN
    SIMP_TAC[HAS_SIZE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `r:real->bool` SUP_FINITE) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `CARD ({}:real->bool) = n + 3` THEN REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = sup (r:real->bool)` THEN STRIP_TAC THEN
  ABBREV_TAC `r' = (r:real->bool) DELETE m` THEN
  SUBGOAL_THEN `(r':real->bool) HAS_SIZE (n + 2) /\ FINITE r' /\ r' SUBSET r /\
                ~(m IN r')` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r'" THEN REWRITE_TAC[HAS_SIZE; DELETE_SUBSET; IN_DELETE] THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. moi_s4t_gap r' a b ==> moi_s4t_gap r a b` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4t_gap] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]; ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN ASM_CASES_TAC `x:real = m` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(b:real) <= m` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; REAL_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "r'" THEN ASM_REWRITE_TAC[IN_DELETE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r':real->bool`; `f:real->complex`; `d:complex`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:complex` (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~((r':real->bool) = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `({}:real->bool) HAS_SIZE (n + 2)` THEN
    REWRITE_TAC[HAS_SIZE; CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `r':real->bool` SUP_FINITE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sup (r':real->bool) < m` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= m /\ ~(x = m) ==> x < m`) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `m:real`)) (concl th))) THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4t_gap r (sup (r':real->bool)) m` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4t_gap] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN ASM_CASES_TAC `x:real = m` THENL
     [ASM_REWRITE_TAC[REAL_LT_REFL];
      SUBGOAL_THEN `(x:real) <= sup r'` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `sup (r':real->bool)`)) (concl th))) THEN
        EXPAND_TAC "r'" THEN ASM_REWRITE_TAC[IN_DELETE];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?p. moi_s4t_gap r' p (sup (r':real->bool))` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~((r' DELETE sup (r':real->bool)) = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `CARD (r' DELETE sup (r':real->bool)) = n + 1` MP_TAC THENL
       [ASM_SIMP_TAC[CARD_DELETE] THEN
        UNDISCH_TAC `(r':real->bool) HAS_SIZE (n + 2)` THEN SIMP_TAC[HAS_SIZE] THEN ARITH_TAC;
        ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPEC `r' DELETE sup (r':real->bool)` SUP_FINITE) THEN
    ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN STRIP_TAC THEN
    EXISTS_TAC `sup (r' DELETE sup (r':real->bool))` THEN
    REWRITE_TAC[moi_s4t_gap] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= m /\ ~(x = m) ==> x < m`) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN ASM_CASES_TAC `x = sup (r':real->bool)` THENL
       [ASM_REWRITE_TAC[REAL_LT_REFL];
        SUBGOAL_THEN `x <= sup (r' DELETE sup (r':real->bool))` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->complex) m - f (sup r') = e` ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS `(f:real->complex) (sup r') - f p` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `e:complex` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `b:real = m` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `a = sup (r':real->bool)` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `moi_s4t_gap r a m` THEN REWRITE_TAC[moi_s4t_gap] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(a:real) IN r'` ASSUME_TAC THENL
       [EXPAND_TAC "r'" THEN REWRITE_TAC[IN_DELETE] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `a:real < m` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `a <= sup (r':real->bool)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `sup (r':real->bool)` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `a:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `sup (r':real->bool) < m` THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `moi_s4t_gap r a b` THEN REWRITE_TAC[moi_s4t_gap] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(b:real) <= m` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "r'" THEN ASM_REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
       [UNDISCH_TAC `a:real < b` THEN UNDISCH_TAC `(b:real) <= m` THEN REAL_ARITH_TAC;
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inf (r:real->bool) = inf r'` SUBST1_TAC THENL
   [MP_TAC(ISPEC `r:real->bool` INF_FINITE) THEN MP_TAC(ISPEC `r':real->bool` INF_FINITE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((r:real->bool) = {})` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `inf (r':real->bool)`)) (concl th))) THEN
      EXPAND_TAC "r'" THEN ASM_REWRITE_TAC[IN_DELETE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `inf (r:real->bool) <= sup r'` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        UNDISCH_TAC `sup (r':real->bool) < m` THEN UNDISCH_TAC `inf (r:real->bool) = m` THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; GSYM REAL_OF_NUM_SUC; CX_ADD] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `!b. a - b = e /\ b - c = k * e ==> a - c = (k + Cx(&1)) * e`) THEN
  EXISTS_TAC `(f:real->complex) (sup r')` THEN ASM_REWRITE_TAC[]);;

let MOI_S4T_STEPS = prove
 (`!(r:real->bool) (f:real->complex) d a b.
     FINITE r /\ a IN r /\ b IN r /\ a < b /\ (!x. x IN r ==> a <= x /\ x <= b) /\
     (!x y. moi_s4t_gap r x y ==> f y - f x = d \/ f y - f x = --d) /\
     (!x y z. moi_s4t_gap r x y /\ moi_s4t_gap r y z ==> f z - f y = f y - f x)
     ==> f b - f a = Cx(&(CARD r - 1)) * d \/
         f b - f a = --(Cx(&(CARD r - 1)) * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 <= CARD(r:real->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `{a:real,b} SUBSET r` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN MP_TAC(ISPECL [`{a:real,b}`; `r:real->bool`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    COND_CASES_TAC THENL
     [UNDISCH_TAC `a:real < b` THEN ASM_REWRITE_TAC[REAL_LT_REFL]; ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`CARD(r:real->bool) - 2`; `r:real->bool`; `f:real->complex`; `d:complex`]
    MOI_S4T_STEPS_INDUCT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE] THEN UNDISCH_TAC `2 <= CARD(r:real->bool)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sup (r:real->bool) = b /\ inf r = a` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MP_TAC(ISPEC `r:real->bool` SUP_FINITE) THEN MP_TAC(ISPEC `r:real->bool` INF_FINITE) THEN
    SUBGOAL_THEN `~((r:real->bool) = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(r:real->bool) - 2 + 1 = CARD r - 1` SUBST1_TAC THENL
   [UNDISCH_TAC `2 <= CARD(r:real->bool)` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:complex` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RNEG]);;

(* ------------------------------------------------------------------------- *)
(* Continuous logarithms and the three-sector map of a chain of three        *)
(* closed sets.                                                              *)
(* ------------------------------------------------------------------------- *)

(* Two continuous logarithms of one map on a connected set differ by a      *)
(* constant.                                                                 *)
let MOI_S4T_LOG_INCR = prove
 (`!(q:real^N->complex) p s a b.
     connected s /\ a IN s /\ b IN s /\ q continuous_on s /\ p continuous_on s /\
     (!t. t IN s ==> cexp(q t) = cexp(p t))
     ==> q b - q a = p b - p a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN s ==> ?n. integer n /\
                  ((q:real^N->complex) t - p t) * inv(Cx(&2 * pi) * ii) = Cx n`
  (LABEL_TAC "int") THENL
   [X_GEN_TAC `t:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N` o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[CEXP_EQ] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `n:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC PI_NZ THEN MP_TAC II_NZ THEN REWRITE_TAC[CX_MUL] THEN
    REWRITE_TAC[GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t:real^N. ((q:real^N->complex) t - p t) * inv(Cx(&2 * pi) * ii)`;
                 `s:real^N->bool`] CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_RMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      USE_THEN "int" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN s`))) THEN
      USE_THEN "int" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN s`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `n1:real` STRIP_ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `n2:real` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~(((q:real^N->complex) y - p y) * inv(Cx(&2 * pi) * ii) =
                     (q x - p x) * inv(Cx(&2 * pi) * ii))` THEN
      ASM_REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX; CX_INJ] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
      ASM_SIMP_TAC[INTEGER_SUB; REAL_SUB_0]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:complex` (fun th ->
    MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC PI_NZ THEN MP_TAC II_NZ THEN REWRITE_TAC[CX_MUL] THEN
  REWRITE_TAC[GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD);;

let MOI_S4T_NORM_SECTOR = prove
 (`!a b c. norm(cexp(Cx a * ii * (Cx b + Cx c))) = &1`,
  REWRITE_TAC[NORM_CEXP; GSYM CX_ADD; RE_MUL_CX; RE_MUL_II; IM_CX; REAL_NEG_0;
              REAL_MUL_RZERO; REAL_EXP_0]);;

let MOI_S4T_SECTOR_EQ = prove
 (`!a b c d e n.
     a * (b + c) = a * (d + e) + &2 * n * pi
     ==> Cx a * ii * (Cx b + Cx c) = Cx a * ii * (Cx d + Cx e) + Cx(&2 * n * pi) * ii`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `Cx a * ii * (Cx b + Cx c) = ii * Cx(a * (b + c)) /\
                Cx a * ii * (Cx d + Cx e) + Cx(&2 * n * pi) * ii =
                ii * Cx(a * (d + e) + &2 * n * pi)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[CX_MUL; CX_ADD] THEN CONV_TAC COMPLEX_RING; ASM_REWRITE_TAC[]]);;

let MOI_S4T_CONTINUOUS_SECTOR = prove
 (`!(p:real^N->real^1) s k.
     p continuous_on s
     ==> (\x. cexp(Cx(&2 * pi / &3) * ii * (Cx k + Cx(drop(p x))))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. cexp(Cx(&2 * pi / &3) * ii * (Cx k + Cx(drop((p:real^N->real^1) x))))) =
                cexp o (\x. Cx(&2 * pi / &3) * ii * (Cx k + Cx(drop(p x))))`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN ASM_REWRITE_TAC[]);;

(* The three-sector map: on c_k it is cexp(2 pi i (k + p_k)/3), p_k = 0 on *)
(* the meet with the previous set and 1 on the meet with the next one.     *)
let MOI_S4T_SECTOR_MAP = prove
 (`!(c1:real^N->bool) c2 c3.
     closed c1 /\ closed c2 /\ closed c3 /\ c1 INTER c2 INTER c3 = {}
     ==> ?phi p1 p2 p3.
           phi continuous_on (c1 UNION c2 UNION c3) /\
           IMAGE phi (c1 UNION c2 UNION c3) SUBSET sphere(vec 0,&1) /\
           p1 continuous_on (:real^N) /\ p2 continuous_on (:real^N) /\
           p3 continuous_on (:real^N) /\
           (!x. x IN c1
                ==> phi x = cexp(Cx(&2 * pi / &3) * ii * (Cx(&0) + Cx(drop(p1 x))))) /\
           (!x. x IN c2
                ==> phi x = cexp(Cx(&2 * pi / &3) * ii * (Cx(&1) + Cx(drop(p2 x))))) /\
           (!x. x IN c3
                ==> phi x = cexp(Cx(&2 * pi / &3) * ii * (Cx(&2) + Cx(drop(p3 x))))) /\
           (!x. x IN c1 INTER c3 ==> p1 x = vec 0) /\
           (!x. x IN c1 INTER c2 ==> p1 x = vec 1) /\
           (!x. x IN c1 INTER c2 ==> p2 x = vec 0) /\
           (!x. x IN c2 INTER c3 ==> p2 x = vec 1) /\
           (!x. x IN c2 INTER c3 ==> p3 x = vec 0) /\
           (!x. x IN c1 INTER c3 ==> p3 x = vec 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c1 INTER c3:real^N->bool`; `c1 INTER c2:real^N->bool`;
                 `vec 0:real^1`; `vec 1:real^1`] URYSOHN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_INTER] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `p1:real^N->real^1` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`c1 INTER c2:real^N->bool`; `c2 INTER c3:real^N->bool`;
                 `vec 0:real^1`; `vec 1:real^1`] URYSOHN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_INTER] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `p2:real^N->real^1` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`c2 INTER c3:real^N->bool`; `c1 INTER c3:real^N->bool`;
                 `vec 0:real^1`; `vec 1:real^1`] URYSOHN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_INTER] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `p3:real^N->real^1` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `e1 = \x. cexp(Cx(&2 * pi / &3) * ii *
                           (Cx(&0) + Cx(drop((p1:real^N->real^1) x))))` THEN
  ABBREV_TAC `e2 = \x. cexp(Cx(&2 * pi / &3) * ii *
                           (Cx(&1) + Cx(drop((p2:real^N->real^1) x))))` THEN
  ABBREV_TAC `e3 = \x. cexp(Cx(&2 * pi / &3) * ii *
                           (Cx(&2) + Cx(drop((p3:real^N->real^1) x))))` THEN
  SUBGOAL_THEN `(!x. x IN c1 INTER c2 ==> (e1:real^N->complex) x = e2 x) /\
                (!x. x IN c2 INTER c3 ==> (e2:real^N->complex) x = e3 x) /\
                (!x. x IN c1 INTER c3 ==> (e1:real^N->complex) x = e3 x)`
  (CONJUNCTS_THEN2 (LABEL_TAC "a12") (CONJUNCTS_THEN2 (LABEL_TAC "a23") (LABEL_TAC "a13")))
  THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "e2"; "e3"] THEN REPEAT CONJ_TAC THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[DROP_VEC] THEN
    REWRITE_TAC[CEXP_EQ] THENL
     [EXISTS_TAC `&0`; EXISTS_TAC `&0`; EXISTS_TAC `-- &1`] THEN
    (CONJ_TAC THENL
      [SIMP_TAC[INTEGER_CLOSED]; MATCH_MP_TAC MOI_S4T_SECTOR_EQ THEN REAL_ARITH_TAC]);
    ALL_TAC] THEN
  EXISTS_TAC `\x:real^N. if x IN c1 then (e1:real^N->complex) x
                         else if x IN c2 then (e2:real^N->complex) x else e3 x` THEN
  MAP_EVERY EXISTS_TAC [`p1:real^N->real^1`; `p2:real^N->real^1`; `p3:real^N->real^1`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN c1 UNION c2 UNION c3
                    ==> (x IN c1 ==> (if x IN c1 then (e1:real^N->complex) x
                                      else if x IN c2 then e2 x else e3 x) = e1 x) /\
                        (x IN c2 ==> (if x IN c1 then (e1:real^N->complex) x
                                      else if x IN c2 then e2 x else e3 x) = e2 x) /\
                        (x IN c3 ==> (if x IN c1 then (e1:real^N->complex) x
                                      else if x IN c2 then e2 x else e3 x) = e3 x)`
  (LABEL_TAC "val") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_CASES_TAC `(x:real^N) IN c1` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "a12" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
      ASM_CASES_TAC `(x:real^N) IN c1` THEN ASM_REWRITE_TAC[] THENL
       [USE_THEN "a13" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
        ASM_CASES_TAC `(x:real^N) IN c2` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "a23" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_CASES THEN ASM_SIMP_TAC[CLOSED_UNION] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "e1" THEN MATCH_MP_TAC MOI_S4T_CONTINUOUS_SECTOR THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      MATCH_MP_TAC CONTINUOUS_ON_CASES THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [EXPAND_TAC "e2" THEN MATCH_MP_TAC MOI_S4T_CONTINUOUS_SECTOR THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
        EXPAND_TAC "e3" THEN MATCH_MP_TAC MOI_S4T_CONTINUOUS_SECTOR THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
        USE_THEN "a23" MATCH_MP_TAC THEN ASM SET_TAC[]];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [USE_THEN "a12" MATCH_MP_TAC THEN ASM SET_TAC[];
        USE_THEN "a13" MATCH_MP_TAC THEN ASM SET_TAC[]]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["e1"; "e2"; "e3"] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[MOI_S4T_NORM_SECTOR];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "e1" THEN REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "val" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "e2" THEN REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "val" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "e3" THEN REWRITE_TAC[]]);;

(* Winding number of a loop with a continuous logarithm along it. *)
let MOI_S4T_WINDING_LOG = prove
 (`!(p:real^1->complex) r.
     path p /\ ~(Cx(&0) IN path_image p) /\ r continuous_on interval[vec 0,vec 1] /\
     (!t. t IN interval[vec 0,vec 1] ==> p t = cexp(r t))
     ==> Cx(&2) * Cx pi * ii * winding_number(p,Cx(&0)) = r(vec 1) - r(vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^1->complex`; `Cx(&0)`] WINDING_NUMBER_AS_CONTINUOUS_LOGARITHM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[COMPLEX_ADD_LID]] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->complex` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "winding_number")) (concl th))) THEN
  REWRITE_TAC[pathstart; pathfinish] THEN MATCH_MP_TAC MOI_S4T_LOG_INCR THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  REWRITE_TAC[CONNECTED_INTERVAL; ENDS_IN_UNIT_INTERVAL] THEN
  ASM_REWRITE_TAC[GSYM path] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  ASM_MESON_TAC[]);;

(* One sector piece of a path: its winding is the change of p_k over 3.  *)
let MOI_S4T_SECTOR_PIECE = prove
 (`!(c:real^N->bool) (phi:real^N->complex) (pk:real^N->real^1) k g.
     path g /\ path_image g SUBSET c /\ pk continuous_on (:real^N) /\
     (!x. x IN c ==> phi x = cexp(Cx(&2 * pi / &3) * ii * (Cx k + Cx(drop(pk x))))) /\
     path (phi o g) /\ ~(Cx(&0) IN path_image (phi o g))
     ==> Cx(&2) * Cx pi * ii * winding_number(phi o g,Cx(&0)) =
         Cx(&2 * pi / &3) * ii *
         (Cx(drop(pk(pathfinish g))) - Cx(drop(pk(pathstart g))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(phi:real^N->complex) o (g:real^1->real^N)`;
                 `\t. Cx(&2 * pi / &3) * ii * (Cx k + Cx(drop((pk:real^N->real^1)
                        ((g:real^1->real^N) t))))`] MOI_S4T_WINDING_LOG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
      SUBGOAL_THEN `(\t. (pk:real^N->real^1) ((g:real^1->real^N) t)) = pk o g`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THENL [ASM_MESON_TAC[path]; ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `path_image (g:real^1->real^N) SUBSET c` THEN
      REWRITE_TAC[path_image] THEN ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pathstart; pathfinish] THEN
    CONV_TAC COMPLEX_RING]);;

(* The core loop through c1, c2, c3 has winding 1 under the sector map.  *)
let MOI_S4T_CORE_WINDING = prove
 (`!(c1:real^N->bool) c2 c3 (phi:real^N->complex) p1 p2 p3.
     path_connected c1 /\ path_connected c2 /\ path_connected c3 /\
     ~(c1 INTER c2 = {}) /\ ~(c2 INTER c3 = {}) /\ ~(c1 INTER c3 = {}) /\
     phi continuous_on (c1 UNION c2 UNION c3) /\
     IMAGE phi (c1 UNION c2 UNION c3) SUBSET sphere(vec 0,&1) /\
     p1 continuous_on (:real^N) /\ p2 continuous_on (:real^N) /\
     p3 continuous_on (:real^N) /\
     (!x. x IN c1 ==> phi x = cexp(Cx(&2 * pi / &3) * ii * (Cx(&0) + Cx(drop(p1 x))))) /\
     (!x. x IN c2 ==> phi x = cexp(Cx(&2 * pi / &3) * ii * (Cx(&1) + Cx(drop(p2 x))))) /\
     (!x. x IN c3 ==> phi x = cexp(Cx(&2 * pi / &3) * ii * (Cx(&2) + Cx(drop(p3 x))))) /\
     (!x. x IN c1 INTER c3 ==> p1 x = vec 0) /\ (!x. x IN c1 INTER c2 ==> p1 x = vec 1) /\
     (!x. x IN c1 INTER c2 ==> p2 x = vec 0) /\ (!x. x IN c2 INTER c3 ==> p2 x = vec 1) /\
     (!x. x IN c2 INTER c3 ==> p3 x = vec 0) /\ (!x. x IN c1 INTER c3 ==> p3 x = vec 1)
     ==> ?g. path g /\ path_image g SUBSET c1 UNION c2 UNION c3 /\
             pathfinish g = pathstart g /\
             winding_number(phi o g,Cx(&0)) = Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (t,x) -> FIRST_X_ASSUM(X_CHOOSE_TAC x o
      REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o check (fun th -> concl th = t)))
   [`~((c1:real^N->bool) INTER c2 = {})`, `x12:real^N`;
    `~((c2:real^N->bool) INTER c3 = {})`, `x23:real^N`;
    `~((c1:real^N->bool) INTER c3 = {})`, `x13:real^N`] THEN
  MP_TAC(ISPECL [`c1:real^N->bool`] path_connected) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x13:real^N`; `x12:real^N`]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c2:real^N->bool`] path_connected) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x12:real^N`; `x23:real^N`]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c3:real^N->bool`] path_connected) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x23:real^N`; `x13:real^N`]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g3:real^1->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(g1:real^1->real^N) ++ g2 ++ g3` THEN
  ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* each piece of phi o g is a path in the circle *)
  SUBGOAL_THEN
   `!g:real^1->real^N. path g /\ path_image g SUBSET c1 UNION c2 UNION c3
        ==> path ((phi:real^N->complex) o g) /\ ~(Cx(&0) IN path_image (phi o g))`
  (LABEL_TAC "pc") THENL
   [GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `Cx(&0) IN sphere(vec 0,&1)` MP_TAC THENL
       [ASM SET_TAC[];
        REWRITE_TAC[IN_SPHERE_0; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx(&2) * Cx pi * ii * winding_number((phi:real^N->complex) o g1,Cx(&0)) =
    Cx(&2 * pi / &3) * ii * (Cx(&1) - Cx(&0)) /\
    Cx(&2) * Cx pi * ii * winding_number((phi:real^N->complex) o g2,Cx(&0)) =
    Cx(&2 * pi / &3) * ii * (Cx(&1) - Cx(&0)) /\
    Cx(&2) * Cx pi * ii * winding_number((phi:real^N->complex) o g3,Cx(&0)) =
    Cx(&2 * pi / &3) * ii * (Cx(&1) - Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`c1:real^N->bool`; `phi:real^N->complex`; `p1:real^N->real^1`;
                     `&0`; `g1:real^1->real^N`] MOI_S4T_SECTOR_PIECE);
      MP_TAC(ISPECL [`c2:real^N->bool`; `phi:real^N->complex`; `p2:real^N->real^1`;
                     `&1`; `g2:real^1->real^N`] MOI_S4T_SECTOR_PIECE);
      MP_TAC(ISPECL [`c3:real^N->bool`; `phi:real^N->complex`; `p3:real^N->real^1`;
                     `&2`; `g3:real^1->real^N`] MOI_S4T_SECTOR_PIECE)] THEN
    (ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN USE_THEN "pc" MATCH_MP_TAC THEN ASM SET_TAC[];
       DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
       ASM_SIMP_TAC[IN_INTER; DROP_VEC]]);
    ALL_TAC] THEN
  REWRITE_TAC[PATH_COMPOSE_JOIN] THEN
  MAP_EVERY (fun g -> USE_THEN "pc" (MP_TAC o SPEC g) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC])
   [`g1:real^1->real^N`; `g2:real^1->real^N`; `g3:real^1->real^N`] THEN
  ASM_SIMP_TAC[WINDING_NUMBER_JOIN; PATH_JOIN; PATH_IMAGE_JOIN; IN_UNION; PATHSTART_JOIN;
               PATHFINISH_JOIN; PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `!a. ~(Cx(&2) * Cx pi * ii = Cx(&0)) /\
        Cx(&2) * Cx pi * ii * w1 = a /\ Cx(&2) * Cx pi * ii * w2 = a /\
        Cx(&2) * Cx pi * ii * w3 = a /\ Cx(&3) * a = Cx(&2) * Cx pi * ii
        ==> w1 + w2 + w3 = Cx(&1)`) THEN
  EXISTS_TAC `Cx(&2 * pi / &3) * ii * (Cx(&1) - Cx(&0))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; II_NZ; PI_NZ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_MUL_RID; CX_MUL; CX_DIV] THEN
    CONV_TAC COMPLEX_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* H_1 of the circle and of a simple closed curve; the 28.8 dichotomy turned *)
(* into a statement about winding numbers of a map to the circle.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S4T_CIRCLE_CLASS_ZPOW = prove
 (`!h:real^1->complex.
     path h /\ pathfinish h = pathstart h /\ path_image h SUBSET sphere(vec 0,&1)
     ==> ?m. winding_number(h,Cx(&0)) = Cx(real_of_int m) /\
             homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
               (frag_of (path_simplex (h o lift))) =
             group_zpow (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
               (homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
                  (frag_of (path_simplex (circlepath(vec 0,&1) o lift)))) m`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FH1_CIRCLE_CLASS_POW) THEN
  REWRITE_TAC[COMPLEX_VEC_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (DISJ_CASES_THEN STRIP_ASSUME_TAC)) THENL
   [EXISTS_TAC `&n:int` THEN ASM_REWRITE_TAC[int_of_num_th; GROUP_ZPOW_POW];
    EXISTS_TAC `-- &n:int` THEN
    ASM_REWRITE_TAC[int_neg_th; int_of_num_th; GROUP_ZPOW_POW; CX_NEG]]);;

let MOI_S4T_CIRCLE_H1_ZPOW = prove
 (`!z. z IN group_carrier
              (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
       ==> ?m. z = group_zpow
                    (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
                    (homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
                       (frag_of (path_simplex (circlepath(vec 0,&1) o lift)))) m`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^2,&1)`; `Cx(&1)`; `z:((num->real)->complex)frag->bool`]
    MOI_FH1_H1_LOOP_REPRESENTATIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_2; LE_REFL];
      REWRITE_TAC[IN_SPHERE_0; COMPLEX_NORM_CX; REAL_ABS_NUM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `h:real^1->complex` MOI_S4T_CIRCLE_CLASS_ZPOW) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* H_1 of the image of a simple closed path is generated by its loop. *)
let MOI_S4T_SIMPLE_LOOP_GENERATES = prove
 (`!l:real^1->real^N.
     simple_path l /\ pathfinish l = pathstart l
     ==> !z. z IN group_carrier(homology_group(&1,subtopology euclidean (path_image l)))
             ==> ?m. z = group_zpow
                           (homology_group(&1,subtopology euclidean (path_image l)))
                           (homologous_rel (1,subtopology euclidean (path_image l),{})
                              (frag_of (path_simplex (l o lift)))) m`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:real^1->real^N`; `vec 0:real^2`; `&1`]
    HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE) THEN
  ASM_REWRITE_TAC[REAL_LT_01; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->complex` (X_CHOOSE_TAC `k':complex->real^N`)) THEN
  ABBREV_TAC `j = path_image (l:real^1->real^N)` THEN
  SUBGOAL_THEN `path (l:real^1->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `path_in (subtopology euclidean j) ((l:real^1->real^N) o lift) /\
                (l o lift) (&0) = (l o lift) (&1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM; SUBSET_REFL] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pathfinish (l:real^1->real^N) = pathstart l` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean j,
                  subtopology euclidean (sphere(vec 0:real^2,&1))) (k:real^N->complex)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; SUBSET_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `group_isomorphism
      (homology_group(&1,subtopology euclidean j),
       homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
      (hom_induced (&1) (subtopology euclidean (j:real^N->bool),{})
                        (subtopology euclidean (sphere(vec 0:real^2,&1)),{})
                        (k:real^N->complex))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_MAP_HOMOLOGY_GROUP_ISOMORPHISM THEN
    REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY] THEN
    EXISTS_TAC `k':complex->real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the image of the loop class *)
  MP_TAC(ISPECL [`subtopology euclidean (j:real^N->bool)`;
                 `subtopology euclidean (sphere(vec 0:real^2,&1))`;
                 `k:real^N->complex`; `(l:real^1->real^N) o lift`]
    MOI_FH1_HOM_INDUCED_LOOP) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_ASSOC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `winding_number((k:real^N->complex) o l,Cx(&0)) = Cx(&1) \/
                winding_number((k:real^N->complex) o l,Cx(&0)) = --Cx(&1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(k:real^N->complex) o (l:real^1->real^N)`
      SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN ASM_REWRITE_TAC[INSIDE_SPHERE] THEN
    DISCH_THEN(DISJ_CASES_THEN (MP_TAC o SPEC `Cx(&0)`)) THEN
    REWRITE_TAC[CENTRE_IN_BALL; GSYM COMPLEX_VEC_0; REAL_LT_01] THEN
    REWRITE_TAC[COMPLEX_VEC_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(k:real^N->complex) o (l:real^1->real^N)` MOI_S4T_CIRCLE_CLASS_ZPOW) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:int` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `e * e = &1:int` ASSUME_TAC THENL
   [SUBGOAL_THEN `e = &1:int \/ e = -- &1` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[int_eq; int_of_num_th; int_neg_th] THEN
      UNDISCH_TAC `winding_number((k:real^N->complex) o l,Cx(&0)) = Cx(&1) \/
                   winding_number((k:real^N->complex) o l,Cx(&0)) = --Cx(&1)` THEN
      ASM_REWRITE_TAC[GSYM CX_NEG; CX_INJ];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `z:((num->real)->real^N)frag->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `homologous_rel (1,subtopology euclidean (j:real^N->bool),{})
                  (frag_of (path_simplex ((l:real^1->real^N) o lift))) IN
                group_carrier(homology_group(&1,subtopology euclidean j))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FH1_LOOP_CLASS_IN_CARRIER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a. hom_induced (&1) (subtopology euclidean (j:real^N->bool),{})
          (subtopology euclidean (sphere(vec 0:real^2,&1)),{}) (k:real^N->complex) z =
        group_zpow (homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
          (homologous_rel (1,subtopology euclidean (sphere(vec 0:real^2,&1)),{})
             (frag_of (path_simplex (circlepath(vec 0,&1) o lift)))) a`
  (X_CHOOSE_TAC `a:int`) THENL
   [MATCH_MP_TAC MOI_S4T_CIRCLE_H1_ZPOW THEN
    UNDISCH_TAC `group_homomorphism
      (homology_group(&1,subtopology euclidean j),
       homology_group(&1,subtopology euclidean (sphere(vec 0:real^2,&1))))
      (hom_induced (&1) (subtopology euclidean (j:real^N->bool),{})
          (subtopology euclidean (sphere(vec 0:real^2,&1)),{}) (k:real^N->complex))` THEN
    REWRITE_TAC[GROUP_HOMOMORPHISM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `e * a:int` THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [group_monomorphism] o
    check (fun th -> moi_s4l_has "group_monomorphism" th)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[GROUP_ZPOW] THEN
  FIRST_ASSUM((fun th -> ASM_SIMP_TAC[MATCH_MP GROUP_HOMOMORPHISM_ZPOW th]) o
    check (fun th -> moi_s4l_has "group_homomorphism" th)) THEN
  MP_TAC MOI_FH1_CIRCLE_GENERATOR_ORDER THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM GROUP_ZPOW_MUL; INT_MUL_ASSOC; INT_MUL_LID]);;

(* If a simple closed curve carries H_1(s), every loop of s winds under phi *)
(* by a multiple of its winding; a loop of winding 1 forces winding +-1.   *)
let MOI_S4T_CARRIES_UNIT = prove
 (`!(s:real^N->bool) (phi:real^N->complex) l g.
     simple_path l /\ pathfinish l = pathstart l /\
     carries_h1 (path_image l) s /\ path_image l SUBSET s /\
     phi continuous_on s /\ IMAGE phi s SUBSET sphere(vec 0,&1) /\
     path g /\ path_image g SUBSET s /\ pathfinish g = pathstart g /\
     winding_number(phi o g,Cx(&0)) = Cx(&1)
     ==> winding_number(phi o l,Cx(&0)) = Cx(&1) \/
         winding_number(phi o l,Cx(&0)) = --Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `j = path_image (l:real^1->real^N)` THEN
  SUBGOAL_THEN `path (l:real^1->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `path_in (subtopology euclidean j) ((l:real^1->real^N) o lift) /\
                (l o lift) (&0) = (l o lift) (&1) /\
                path_in (subtopology euclidean s) ((g:real^1->real^N) o lift) /\
                (g o lift) (&0) = (g o lift) (&1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM; SUBSET_REFL] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pathfinish (l:real^1->real^N) = pathstart l` THEN
    UNDISCH_TAC `pathfinish (g:real^1->real^N) = pathstart g` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean s,subtopology euclidean (sphere(vec 0:real^2,&1)))
       (phi:real^N->complex) /\
    continuous_map (subtopology euclidean j,subtopology euclidean s) (\x:real^N. x) /\
    continuous_map (subtopology euclidean j,subtopology euclidean (sphere(vec 0:real^2,&1)))
       (phi:real^N->complex)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; CONTINUOUS_ON_ID; IMAGE_ID; o_DEF; ETA_AX] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; IMAGE_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  (* the class of g comes from j *)
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`; `(g:real^1->real^N) o lift`]
    MOI_FH1_LOOP_CLASS_IN_CARRIER) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `carries_h1 (j:real^N->bool) s` THEN
  REWRITE_TAC[carries_h1; group_image] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:((num->real)->real^N)frag->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `l:real^1->real^N` MOI_S4T_SIMPLE_LOOP_GENERATES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:((num->real)->real^N)frag->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:int`) THEN
  (* push forward by phi *)
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                 `subtopology euclidean (sphere(vec 0:real^2,&1))`;
                 `phi:real^N->complex`; `(g:real^1->real^N) o lift`]
    MOI_FH1_HOM_INDUCED_LOOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[o_ASSOC]] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq(concl th) && moi_s4l_has "hom_induced" th && moi_s4l_has "frag_of" th)) THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (j:real^N->bool)`;
                 `subtopology euclidean (s:real^N->bool)`;
                 `subtopology euclidean (sphere(vec 0:real^2,&1))`;
                 `\x:real^N. x`; `phi:real^N->complex`] HOM_INDUCED_COMPOSE_EMPTY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `z:((num->real)->real^N)frag->bool`) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(phi:real^N->complex) o (\x:real^N. x) = phi` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `z:((num->real)->real^N)frag->bool`)) THEN
  MP_TAC(ISPECL [`subtopology euclidean (j:real^N->bool)`; `(l:real^1->real^N) o lift`]
    MOI_FH1_LOOP_CLASS_IN_CARRIER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP GROUP_HOMOMORPHISM_ZPOW (ISPECL
    [`&1:int`; `subtopology euclidean (j:real^N->bool)`;
     `subtopology euclidean (sphere(vec 0:real^2,&1))`; `phi:real^N->complex`]
    GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY)) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM((fun th' -> REWRITE_TAC[MATCH_MP th th']) o
    check (fun th'' -> moi_s4l_has "group_carrier" th'' && moi_s4l_has "frag_of" th''))) THEN
  MP_TAC(ISPECL [`subtopology euclidean (j:real^N->bool)`;
                 `subtopology euclidean (sphere(vec 0:real^2,&1))`;
                 `phi:real^N->complex`; `(l:real^1->real^N) o lift`]
    MOI_FH1_HOM_INDUCED_LOOP) THEN
  ASM_REWRITE_TAC[o_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
  (* integer powers of the generator *)
  SUBGOAL_THEN `path ((phi:real^N->complex) o (l:real^1->real^N)) /\
                path ((phi:real^N->complex) o (g:real^1->real^N))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(phi:real^N->complex) o (l:real^1->real^N)` MOI_S4T_CIRCLE_CLASS_ZPOW) THEN
  MP_TAC(ISPEC `(phi:real^N->complex) o (g:real^1->real^N)` MOI_S4T_CIRCLE_CLASS_ZPOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `v:int` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `w:int` (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC))] THEN
  MP_TAC MOI_FH1_CIRCLE_GENERATOR_ORDER THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM GROUP_ZPOW_MUL; GROUP_ZPOW_EQ_ALT;
               INTEGER_RULE `!x:int. &0 divides x <=> x = &0`] THEN
  SUBGOAL_THEN `v = &1:int` SUBST1_TAC THENL
   [REWRITE_TAC[int_eq; int_of_num_th] THEN
    UNDISCH_TAC `winding_number((phi:real^N->complex) o g,Cx(&0)) = Cx(real_of_int v)` THEN
    ASM_REWRITE_TAC[CX_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INT_ARITH `&1 - x:int = &0 <=> x = &1`; INT_MUL_EQ_1] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[int_of_num_th; int_neg_th; CX_NEG]);;

(* A loop in a contractible set has winding 0 under any map to C - {0}. *)
let MOI_S4T_CONTRACTIBLE_WINDING = prove
 (`!(d:real^N->bool) (phi:real^N->complex) l.
     contractible d /\ phi continuous_on d /\ (!x. x IN d ==> ~(phi x = Cx(&0))) /\
     path l /\ path_image l SUBSET d /\ pathfinish l = pathstart l
     ==> winding_number(phi o l,Cx(&0)) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^N->complex`; `d:real^N->bool`]
    CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q:real^N->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(phi:real^N->complex) o (l:real^1->real^N)`;
                 `(q:real^N->complex) o (l:real^1->real^N)`] MOI_S4T_WINDING_LOG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ASM_MESON_TAC[path];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `d:real^N->bool` THEN
        ASM_REWRITE_TAC[GSYM path_image]];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `path_image (l:real^1->real^N) SUBSET d` THEN
      REWRITE_TAC[path_image] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `pathfinish (l:real^1->real^N) = pathstart l` THEN
  REWRITE_TAC[pathstart; pathfinish; o_THM] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_ENTIRE; CX_INJ; II_NZ; PI_NZ] THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ]);;

let MOI_S4T_CELL_CONTRACTIBLE = prove
 (`!n (d:real^N->bool) b. pl_cell_with_boundary n d b ==> contractible d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(k:real^N->bool) homeomorphic (d:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP HOMEOMORPHIC_CONTRACTIBLE_EQ) THEN
  MATCH_MP_TAC CONVEX_IMP_CONTRACTIBLE THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]);;

(* ------------------------------------------------------------------------- *)
(* A face triangle s with vertices v1 v2 v3: its balls, disks and rims.      *)
(* ------------------------------------------------------------------------- *)

let moi_s4t_tri = new_definition
 `moi_s4t_tri (tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 <=>
    moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
    moi_s34_fbinv tt kk h f1 car cb /\ s IN moi_s34_simp kk (&2) /\
    ~(v1 = v2) /\ ~(v1 = v3) /\ ~(v2 = v3) /\
    {x | x IN s /\ {x} IN kk} = {v1,v2,v3} /\
    segment[v1,v2] IN kk /\ segment[v1,v3] IN kk /\ segment[v2,v3] IN kk`;;

let MOI_S4T_TRI_EXISTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ s IN moi_s34_simp kk (&2)
     ==> ?v1 v2 v3. moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_S4L_TRI_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` (X_CHOOSE_THEN `c:real^N`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `s:real^N->bool`)) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `c:real^N`] THEN
  ASM_REWRITE_TAC[moi_s4t_tri]);;

let MOI_S4T_TRI_BALLS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3
     ==> {v1} IN kk /\ {v2} IN kk /\ {v3} IN kk /\
         compact(IMAGE f1 (moi_s34_vb tt kk v1)) /\
         compact(IMAGE f1 (moi_s34_vb tt kk v2)) /\
         compact(IMAGE f1 (moi_s34_vb tt kk v3)) /\
         path_connected(IMAGE f1 (moi_s34_vb tt kk v1)) /\
         path_connected(IMAGE f1 (moi_s34_vb tt kk v2)) /\
         path_connected(IMAGE f1 (moi_s34_vb tt kk v3)) /\
         IMAGE f1 (moi_s34_vb tt kk v1) INTER IMAGE f1 (moi_s34_vb tt kk v2) =
         IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2) /\
         IMAGE f1 (moi_s34_vb tt kk v1) INTER IMAGE f1 (moi_s34_vb tt kk v3) =
         IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3) /\
         IMAGE f1 (moi_s34_vb tt kk v2) INTER IMAGE f1 (moi_s34_vb tt kk v3) =
         IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3) /\
         ~(IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2) = {}) /\
         ~(IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3) = {}) /\
         ~(IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3) = {}) /\
         IMAGE f1 (moi_s34_vb tt kk v1) INTER IMAGE f1 (moi_s34_vb tt kk v2) INTER
         IMAGE f1 (moi_s34_vb tt kk v3) = {} /\
         compact(IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_bd tt kk)) /\
         compact(IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk)) /\
         compact(IMAGE f1 (moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk)) /\
         IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_bd tt kk) SUBSET
         IMAGE f1 (moi_s34_vb tt kk v1) /\
         IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk) SUBSET
         IMAGE f1 (moi_s34_vb tt kk v2) /\
         IMAGE f1 (moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk) SUBSET
         IMAGE f1 (moi_s34_vb tt kk v3) /\
         IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_bd tt kk) INTER
         IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk) =
         IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_bd tt kk) INTER
         IMAGE f1 (moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk) =
         IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk) INTER
         IMAGE f1 (moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk) =
         IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk)
         SUBSET moi_s34_rims tt kk f1 /\
         IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk)
         SUBSET moi_s34_rims tt kk f1 /\
         IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk)
         SUBSET moi_s34_rims tt kk f1 /\
         IMAGE f1 (moi_s34_ft tt kk s) =
         IMAGE f1 (moi_s34_vb tt kk v1) UNION IMAGE f1 (moi_s34_vb tt kk v2) UNION
         IMAGE f1 (moi_s34_vb tt kk v3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4t_tri] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v1:real^N} IN kk /\ {v2} IN kk /\ {v3} IN kk` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN s /\ {x} IN kk} = {v1:real^N,v2,v3}` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE o check (fun th ->
    concl th = `moi_s34_tube (tt:(real^N->bool)->bool) kk`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY (fun v -> MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; v] MOI_S4L_AV_BASIC) THEN
                 ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
   [`v1:real^N`; `v2:real^N`; `v3:real^N`] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `v1:real^N`; `v2:real^N`; `v3:real^N`] MOI_S4L_FACE_TORUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_s34_vb tt kk (v1:real^N) SUBSET moi_s34_nb tt kk /\
                moi_s34_vb tt kk v2 SUBSET moi_s34_nb tt kk /\
                moi_s34_vb tt kk v3 SUBSET moi_s34_nb tt kk`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "img" o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
    moi_s4l_has "moi_s34_nb" th)) THEN
  SUBGOAL_THEN
   `!x y. x SUBSET moi_s34_nb tt kk /\ y SUBSET moi_s34_nb tt kk
          ==> IMAGE (f1:real^N->real^3) (x INTER y) = IMAGE f1 x INTER IMAGE f1 y /\
              x INTER y SUBSET moi_s34_nb tt kk`
  (LABEL_TAC "img2") THENL
   [REPEAT STRIP_TAC THENL [USE_THEN "img" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY (fun (x,y) -> USE_THEN "img2" (MP_TAC o SPECL [x;y]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
   [`moi_s34_vb tt kk (v1:real^N)`, `moi_s34_vb tt kk (v2:real^N)`;
    `moi_s34_vb tt kk (v1:real^N)`, `moi_s34_vb tt kk (v3:real^N)`;
    `moi_s34_vb tt kk (v2:real^N)`, `moi_s34_vb tt kk (v3:real^N)`;
    `moi_s34_vb tt kk (v1:real^N)`, `moi_s34_bd (tt:(real^N->bool)->bool) kk`;
    `moi_s34_vb tt kk (v2:real^N)`, `moi_s34_bd (tt:(real^N->bool)->bool) kk`;
    `moi_s34_vb tt kk (v3:real^N)`, `moi_s34_bd (tt:(real^N->bool)->bool) kk`] THEN
  MAP_EVERY (fun (x,y) -> USE_THEN "img2" (MP_TAC o SPECL [x;y]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
   [`moi_s34_vb tt kk (v1:real^N)`,
    `moi_s34_vb tt kk (v2:real^N) INTER moi_s34_bd (tt:(real^N->bool)->bool) kk`;
    `moi_s34_vb tt kk (v1:real^N)`,
    `moi_s34_vb tt kk (v3:real^N) INTER moi_s34_bd (tt:(real^N->bool)->bool) kk`;
    `moi_s34_vb tt kk (v2:real^N)`,
    `moi_s34_vb tt kk (v3:real^N) INTER moi_s34_bd (tt:(real^N->bool)->bool) kk`] THEN
  SUBGOAL_THEN `~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2) = {})`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO (ASSUME
     `pl_cell_with_boundary 2 (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2))
        (IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk))`)) THEN
    MESON_TAC[SET_RULE `!d b:real^3->bool. ~(d DIFF b = {}) ==> ~(d = {})`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3) = {})`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO (ASSUME
     `pl_cell_with_boundary 2 (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3))
        (IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk))`)) THEN
    MESON_TAC[SET_RULE `!d b:real^3->bool. ~(d DIFF b = {}) ==> ~(d = {})`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3) = {})`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO (ASSUME
     `pl_cell_with_boundary 2 (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3))
        (IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk))`)) THEN
    MESON_TAC[SET_RULE `!d b:real^3->bool. ~(d DIFF b = {}) ==> ~(d = {})`];
    ALL_TAC] THEN
  MAP_EVERY (fun (x,y) -> MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `f1:real^N->real^3`; x; y] MOI_S4L_RIM_IN_RIMS) THEN
                 ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SEGMENT_SYM]; DISCH_TAC])
   [`v1:real^N`, `v2:real^N`; `v1:real^N`, `v3:real^N`; `v2:real^N`, `v3:real^N`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v1:real^N`; `v2:real^N`; `v3:real^N`] o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 3 &&
    moi_s4l_has "moi_s34_vb" th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC MOI_S4L_PL_BALL_PATH_CONNECTED THEN EXISTS_TAC `3` THEN
         FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
         ASM_REWRITE_TAC[] THEN NO_TAC;
         ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_S4T_TRI_TRACE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3
     ==> moi_s34_fb1 tt kk h f1 car s (cb s) /\
         moi_s34_trace tt kk f1 (cb s) =
         frontier (cb s) INTER
         (IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_bd tt kk) UNION
          IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk) UNION
          IMAGE f1 (moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk)) /\
         compact (moi_s34_trace tt kk f1 (cb s)) /\
         FINITE (components (moi_s34_trace tt kk f1 (cb s))) /\
         (!k. k IN components (moi_s34_trace tt kk f1 (cb s)) ==> pl_sphere 1 k) /\
         FINITE (moi_s34_trace tt kk f1 (cb s) INTER moi_s34_rims tt kk f1) /\
         moi_s34_trace tt kk f1 (cb s) INTER moi_s34_rims tt kk f1 SUBSET
         IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk) UNION
         IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk) UNION
         IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk) /\
         pl_solid_torus (IMAGE f1 (moi_s34_ft tt kk s)) /\
         moi_s34_trace tt kk f1 (cb s) SUBSET frontier (IMAGE f1 (moi_s34_ft tt kk s)) /\
         carries_h1 (moi_s34_trace tt kk f1 (cb s)) (IMAGE f1 (moi_s34_ft tt kk s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_BALLS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4t_tri]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `(cb:(real^N->bool)->real^3->bool) s`;
                 `v1:real^N`; `v2:real^N`; `v3:real^N`] MOI_S4L_TRACE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s34_fb1] o
    check (moi_s4l_has "moi_s34_fb1")) THEN
  SUBGOAL_THEN `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)
                SUBSET IMAGE f1 (moi_s34_ft tt kk s)` ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
      is_eq(concl th) && lhs(concl th) =
      `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`)) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
      is_eq(concl th) && lhs(concl th) =
      `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`)) THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_bd tt kk) SUBSET
       IMAGE f1 (moi_s34_vb tt kk v1)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk) SUBSET
       IMAGE f1 (moi_s34_vb tt kk v2)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk) SUBSET
       IMAGE f1 (moi_s34_vb tt kk v3)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_bd tt kk)`, `A1:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk)`, `A2:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk)`, `A3:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1)`, `C1:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2)`, `C2:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v3)`, `C3:real^3->bool`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s)`, `S:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `frontier ((cb:(real^N->bool)->real^3->bool) s) INTER
                moi_s34_rims tt kk (f1:real^N->real^3)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s34_trace] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)` THEN
    REWRITE_TAC[moi_s34_rims; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `r:real^3->bool`)) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) /\
                  x IN IMAGE f1 (moi_s34_vb tt kk w)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                     ((moi_s34_vb tt kk u INTER moi_s34_vb tt kk w) INTER moi_s34_bd tt kk)` THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN (cb:(real^N->bool)->real^3->bool) s` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^N) IN s /\ (w:real^N) IN s` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1 && moi_s4l_has "DISJOINT" th &&
        moi_s4l_has "moi_s34_vb" th)) THENL
       [DISCH_THEN(MP_TAC o SPEC `u:real^N`); DISCH_THEN(MP_TAC o SPEC `w:real^N`)] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `((u:real^N) = v1 \/ u = v2 \/ u = v3) /\ (w = v1 \/ w = v2 \/ w = v3)`
    MP_TAC THENL
     [UNDISCH_TAC `{x | x IN s /\ {x} IN kk} = {v1:real^N,v2,v3}` THEN
      MAP_EVERY UNDISCH_TAC [`(u:real^N) IN s`; `(w:real^N) IN s`; `{u:real^N} IN kk`;
                             `{w:real^N} IN kk`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~(u:real^N = w)` THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   ((moi_s34_vb tt kk u INTER moi_s34_vb tt kk w) INTER moi_s34_bd tt kk)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> moi_s4l_has "IMAGE" th)) THEN
    ASM_REWRITE_TAC[IN_UNION; INTER_ACI] THEN TRY(MESON_TAC[]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o funpow 9 CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[frontier; SUBSET; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN ASM SET_TAC[];
      DISCH_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE o check (fun th ->
      concl th = `moi_s34_tube (tt:(real^N->bool)->bool) kk`)) THEN
    SUBGOAL_THEN `moi_s34_ft tt kk (s:real^N->bool) SUBSET moi_s34_nb tt kk` ASSUME_TAC THENL
     [REWRITE_TAC[moi_s34_ft; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`;
                   `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`] SUBSET_INTERIOR) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[IMAGE_SUBSET]; DISCH_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4L_FRAME_F1 o check (moi_s4l_has "moi_s34_frame")) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM SET_TAC[];
    UNDISCH_TAC `carries_h1 (moi_s34_trace tt kk (f1:real^N->real^3)
                   ((cb:(real^N->bool)->real^3->bool) s) INTER IMAGE f1 (moi_s34_ft tt kk s))
                 (IMAGE f1 (moi_s34_ft tt kk s))` THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The three-sector map of a face torus, in vertex-indexed form, and its     *)
(* core loop of winding 1.                                                   *)
(* ------------------------------------------------------------------------- *)

let moi_s4t_refl_neg th =
  is_neg(concl th) && (let t = dest_neg(concl th) in is_eq t && lhs t = rhs t);;

let moi_s4t_vcases vs =
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  REPEAT(FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
    is_disj(concl th) && exists (fun v -> vfree_in v (concl th)) vs))) THEN
  TRY(FIRST_X_ASSUM(fun th ->
    if moi_s4t_refl_neg th then MP_TAC th THEN REWRITE_TAC[] else NO_TAC));;

let MOI_S4T_TRI_SECTOR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3
     ==> ?(phi:real^3->complex) (pp:real^N->real^3->real^1) kc sg.
           phi continuous_on IMAGE f1 (moi_s34_ft tt kk s) /\
           IMAGE phi (IMAGE f1 (moi_s34_ft tt kk s)) SUBSET sphere(vec 0,&1) /\
           (!u. pp u continuous_on (:real^3)) /\
           (!u x. u IN {v1,v2,v3} /\ x IN IMAGE f1 (moi_s34_vb tt kk u)
                  ==> phi x = cexp(Cx(&2 * pi / &3) * ii *
                                   (Cx(kc u) + Cx(drop(pp u x))))) /\
           (!u w x. u IN {v1,v2,v3} /\ w IN {v1,v2,v3} /\ ~(u = w) /\
                    x IN IMAGE f1 (moi_s34_vb tt kk u) /\ x IN IMAGE f1 (moi_s34_vb tt kk w)
                    ==> drop(pp u x) = sg u w) /\
           (!u w. u IN {v1,v2,v3} /\ w IN {v1,v2,v3} /\ ~(u = w)
                  ==> sg u w + sg w u = &1) /\
           (!u w1 w2. u IN {v1,v2,v3} /\ w1 IN {v1,v2,v3} /\ w2 IN {v1,v2,v3} /\
                      ~(u = w1) /\ ~(u = w2) /\ ~(w1 = w2)
                      ==> sg u w1 + sg u w2 = &1) /\
           (!u w. sg u w = &0 \/ sg u w = &1) /\
           (?g. path g /\ path_image g SUBSET IMAGE f1 (moi_s34_ft tt kk s) /\
                pathfinish g = pathstart g /\ winding_number(phi o g,Cx(&0)) = Cx(&1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_BALLS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4t_tri]) THEN
  MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v3)`] MOI_S4T_SECTOR_MAP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->complex` (X_CHOOSE_THEN `p1:real^3->real^1`
    (X_CHOOSE_THEN `p2:real^3->real^1` (X_CHOOSE_THEN `p3:real^3->real^1`
      STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `phi:real^3->complex` THEN
  EXISTS_TAC `\u:real^N. if u = v1 then (p1:real^3->real^1)
                         else if u = v2 then p2 else p3` THEN
  EXISTS_TAC `\u:real^N. if u = v1 then &0 else if u = v2 then &1 else &2` THEN
  EXISTS_TAC `\u w:real^N. if (u = v1 /\ w = v2) \/ (u = v2 /\ w = v3) \/
                              (u = v3 /\ w = v1) then &1 else &0` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(v2:real^N = v1) /\ ~(v3:real^N = v1) /\ ~(v3:real^N = v2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
    moi_s4t_vcases [`u:real^N`] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
    moi_s4t_vcases [`u:real^N`; `w:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[IN_INTER; DROP_VEC];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
    moi_s4t_vcases [`u:real^N`; `w:real^N`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
    moi_s4t_vcases [`u:real^N`; `w1:real^N`; `w2:real^N`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4T_CORE_WINDING THEN
    MAP_EVERY EXISTS_TAC [`p1:real^3->real^1`; `p2:real^3->real^1`; `p3:real^3->real^1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_S4L_PL_BALL_PATH_CONNECTED]]);;

(* ------------------------------------------------------------------------- *)
(* A trace component J as a loop: its rim points, rim times and gaps.        *)
(* ------------------------------------------------------------------------- *)

(* A connected part of the trace missing the rims lies in one A_u. *)
let MOI_S4T_CONNECTED_ONE_A = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 k.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     connected k /\ k SUBSET moi_s34_trace tt kk f1 (cb s) /\
     k INTER moi_s34_rims tt kk f1 = {}
     ==> ?u. u IN {v1,v2,v3} /\
             k SUBSET IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_BALLS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_TRACE) THEN
  ABBREV_TAC `a1 = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `a2 = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2 INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `a3 = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk)` THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET a1 UNION a2 UNION a3 /\
                k INTER a1 INTER a2 = {} /\ k INTER a1 INTER a3 = {} /\
                k INTER a2 INTER a3 = {}` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(k:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
         ((cb:(real^N->bool)->real^3->bool) s)`;
      `(k:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) = {}`;
      `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s) =
       frontier (cb s) INTER (a1 UNION a2 UNION a3)`;
      `(a1:real^3->bool) INTER a2 =
       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2 INTER
                                  moi_s34_bd tt kk)`;
      `(a1:real^3->bool) INTER a3 =
       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3 INTER
                                  moi_s34_bd tt kk)`;
      `(a2:real^3->bool) INTER a3 =
       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3 INTER
                                  moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2 INTER
                                  moi_s34_bd tt kk) SUBSET moi_s34_rims tt kk f1`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3 INTER
                                  moi_s34_bd tt kk) SUBSET moi_s34_rims tt kk f1`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3 INTER
                                  moi_s34_bd tt kk) SUBSET moi_s34_rims tt kk f1`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`,
      `TT:real^3->bool`;
      `moi_s34_rims tt kk (f1:real^N->real^3)`, `RR:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2 INTER
                                  moi_s34_bd tt kk)`, `R12:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3 INTER
                                  moi_s34_bd tt kk)`, `R13:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3 INTER
                                  moi_s34_bd tt kk)`, `R23:real^3->bool`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s)`, `S:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(a1:real^3->bool) /\ closed(a2:real^3->bool) /\ closed(a3:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a1"; "a2"; "a3"] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `a1:real^3->bool`; `a2 UNION a3:real^3->bool`]
    MOI_S4L_CONNECTED_TWO_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_IN_CLOSED_INTER; CLOSED_UNION] THEN ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `v1:real^N` THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `a2:real^3->bool`; `a3:real^3->bool`]
    MOI_S4L_CONNECTED_TWO_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_IN_CLOSED_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `v2:real^N` THEN ASM_REWRITE_TAC[IN_INSERT];
    EXISTS_TAC `v3:real^N` THEN ASM_REWRITE_TAC[IN_INSERT]]);;

let MOI_S4T_CARD_GE2 = prove
 (`!s:A->bool. FINITE s /\ ~(s = {}) /\ ~(?a. s = {a}) ==> 2 <= CARD s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n = 0) /\ ~(n = 1)`] THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(s:A->bool) HAS_SIZE 1` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN ASM_MESON_TAC[]);;

(* The rim points of a trace component: finitely many, at least two. *)
let MOI_S4T_COMP_RIMS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     (!s v j. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
              j IN components (moi_s34_trace tt kk f1 (cb s))
              ==> ~(j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))) /\
     j IN components (moi_s34_trace tt kk f1 (cb s))
     ==> FINITE (j INTER moi_s34_rims tt kk f1) /\
         2 <= CARD (j INTER moi_s34_rims tt kk f1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_BALLS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_TRACE) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `moi_s34_trace tt kk (f1:real^N->real^3)
                       ((cb:(real^N->bool)->real^3->bool) s)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4t_tri]) THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s) /\ connected j` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN
      EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3)
                    ((cb:(real^N->bool)->real^3->bool) s)` THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE ((j:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)
                INTER moi_s34_rims tt kk f1` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4T_CARD_GE2 THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                   `j:real^3->bool`] MOI_S4T_CONNECTED_ONE_A) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `u:real^N`; `j:real^3->bool`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
      is_disj(concl th) && vfree_in `u:real^N` (concl th))) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `r:real^3`) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`; `j:real^3->bool`; `r:real^3`]
      MOI_S4L_TRACE_RIMS_NOT_SING) THEN
    ASM_REWRITE_TAC[]]);;

(* The component as a simple closed PL loop starting at a rim point. *)
let MOI_S4T_COMP_LOOP = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     ~(j INTER moi_s34_rims tt kk f1 = {})
     ==> ?l. simple_path l /\ pathfinish l = pathstart l /\
             pl_map_on (interval[vec 0,vec 1]) l /\ path_image l = j /\
             pathstart l IN moi_s34_rims tt kk f1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_TRACE) THEN
  MP_TAC(ISPEC `j:real^3->bool` MOI_S4O_CIRCLE_LOOP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:real^1->real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `p:real^3` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> is_neg(concl th) && moi_s4l_has "moi_s34_rims" th)) THEN
  SUBGOAL_THEN `?a. a IN interval[vec 0,vec 1] /\ (l0:real^1->real^3) a = p`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN j INTER moi_s34_rims tt kk (f1:real^N->real^3)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
    REWRITE_TAC[path_image; IN_INTER; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= drop a /\ drop a <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(a:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC];
    ALL_TAC] THEN
  EXISTS_TAC `shiftpath a (l0:real^1->real^3)` THEN
  ASM_SIMP_TAC[SIMPLE_PATH_SHIFTPATH; MOI_PL2_PL_SHIFTPATH; PATHSTART_SHIFTPATH;
               PATHFINISH_SHIFTPATH; PATH_IMAGE_SHIFTPATH] THEN
  ASM SET_TAC[]);;

(* Rim times of a simple closed loop through a finite set. *)
let MOI_S4T_TIMES = prove
 (`!(l:real^1->real^N) p.
     simple_path l /\ pathfinish l = pathstart l /\ pathstart l IN p /\
     FINITE p /\ p SUBSET path_image l
     ==> FINITE {t | &0 <= t /\ t <= &1 /\ l(lift t) IN p} /\
         &0 IN {t | &0 <= t /\ t <= &1 /\ l(lift t) IN p} /\
         &1 IN {t | &0 <= t /\ t <= &1 /\ l(lift t) IN p} /\
         CARD {t | &0 <= t /\ t <= &1 /\ l(lift t) IN p} = CARD p + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(l:real^1->real^N)(lift(&0)) IN p /\ l(lift(&1)) IN p` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_NUM] THEN
    UNDISCH_TAC `pathfinish (l:real^1->real^N) = pathstart l` THEN
    UNDISCH_TAC `pathstart (l:real^1->real^N) IN p` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. (&0 <= x /\ x < &1) /\ (&0 <= y /\ y < &1) /\
          (l:real^1->real^N) (lift x) = l (lift y) ==> x = y`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `simple_path (l:real^1->real^N)` THEN REWRITE_TAC[simple_path] THEN
    DISCH_THEN(MP_TAC o SPECL [`lift x`; `lift y`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; GSYM LIFT_NUM; LIFT_EQ] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `{t | &0 <= t /\ t <= &1 /\ (l:real^1->real^N)(lift t) IN p} =
                &1 INSERT {t | t IN {t | &0 <= t /\ t < &1} /\ (l o lift) t IN p}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; o_THM] THEN X_GEN_TAC `t:real` THEN
    ASM_CASES_TAC `t = &1` THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
    ASM_REWRITE_TAC[REAL_LT_LE; CONJ_ACI];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {t | t IN {t | &0 <= t /\ t < &1} /\
                            ((l:real^1->real^N) o lift) t IN p}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ_GENERAL THEN ASM_REWRITE_TAC[o_THM; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((l:real^1->real^N) o lift)
                  {t | t IN {t | &0 <= t /\ t < &1} /\ (l o lift) t IN p} = p`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; o_THM] THEN X_GEN_TAC `x:real^N` THEN
    EQ_TAC THENL [MESON_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN path_image l` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[path_image; IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `drop u = &1` THENL
     [EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN
      UNDISCH_TAC `pathfinish (l:real^1->real^N) = pathstart l` THEN
      REWRITE_TAC[pathstart; pathfinish; GSYM LIFT_NUM] THEN
      SUBGOAL_THEN `u = lift(&1)` SUBST_ALL_TAC THENL
       [ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `drop u` THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {t | t IN {t | &0 <= t /\ t < &1} /\
                          ((l:real^1->real^N) o lift) t IN p} = CARD p`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; IN_INSERT; IN_ELIM_THM; o_THM] THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LT_REFL; REAL_LT_01; REAL_LE_REFL; ADD1; LIFT_NUM]);;

(* Facts about an ordered pair of distinct vertices of the triangle. *)
let MOI_S4T_TRI_PAIR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 u w.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     u IN {v1,v2,v3} /\ w IN {v1,v2,v3} /\ ~(u = w)
     ==> {u} IN kk /\ {w} IN kk /\ segment[u,w] IN kk /\
         IMAGE f1 (moi_s34_vb tt kk u) INTER IMAGE f1 (moi_s34_vb tt kk w) =
         IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w) /\
         IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) INTER
         IMAGE f1 (moi_s34_vb tt kk w) =
         IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
         SUBSET moi_s34_rims tt kk f1 /\
         (!x. x IN {v1,v2,v3} /\ ~(x = u) /\ ~(x = w)
              ==> IMAGE f1 (moi_s34_vb tt kk u) INTER IMAGE f1 (moi_s34_vb tt kk w) INTER
                  IMAGE f1 (moi_s34_vb tt kk x) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4t_tri]) THEN
  SUBGOAL_THEN `{v1:real^N} IN kk /\ {v2} IN kk /\ {v3} IN kk` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN s /\ {x} IN kk} = {v1:real^N,v2,v3}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN kk /\ {w} IN kk /\ segment[u,w] IN kk` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(u:real^N = w)` THEN
    UNDISCH_TAC `(w:real^N) IN {v1,v2,v3}` THEN UNDISCH_TAC `(u:real^N) IN {v1,v2,v3}` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT(DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SEGMENT_SYM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE o check (fun th ->
    concl th = `moi_s34_tube (tt:(real^N->bool)->bool) kk`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `moi_s34_vb tt kk (u:real^N) SUBSET moi_s34_nb tt kk /\
                moi_s34_vb tt kk (w:real^N) SUBSET moi_s34_nb tt kk`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      moi_s4l_has "moi_s34_nb" th)) THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`moi_s34_vb tt kk (u:real^N) INTER moi_s34_bd tt kk`;
                   `moi_s34_vb tt kk (w:real^N)`] (ASSUME
     `!a b. a SUBSET moi_s34_nb tt kk /\ b SUBSET moi_s34_nb tt kk
            ==> IMAGE (f1:real^N->real^3) (a INTER b) = IMAGE f1 a INTER IMAGE f1 b`)) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN SET_TAC[];
    MATCH_MP_TAC MOI_S4L_RIM_IN_RIMS THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 3 &&
      moi_s4l_has "moi_s34_vb" th)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN {v1,v2,v3}` THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* A trace-rim point in one vertex ball lies in exactly one other one. *)
let MOI_S4T_TRI_RIMPT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 p u.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     p IN moi_s34_trace tt kk f1 (cb s) /\ p IN moi_s34_rims tt kk f1 /\
     u IN {v1,v2,v3} /\ p IN IMAGE f1 (moi_s34_vb tt kk u)
     ==> ?w. w IN {v1,v2,v3} /\ ~(w = u) /\ p IN IMAGE f1 (moi_s34_vb tt kk w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_BALLS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_TRACE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4t_tri]) THEN
  SUBGOAL_THEN
   `?a b. a IN {v1,v2,v3} /\ b IN {v1,v2,v3} /\ ~(a = b) /\
          (p:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a) /\
          p IN IMAGE f1 (moi_s34_vb tt kk b)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(p:real^3) IN
      IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2 INTER
                                 moi_s34_bd tt kk) UNION
      IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk) UNION
      IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3 INTER moi_s34_bd tt kk)`
    MP_TAC THENL
     [UNDISCH_TAC `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)
                   INTER moi_s34_rims tt kk f1 SUBSET
                   IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v2 INTER
                             moi_s34_bd tt kk) UNION
                   IMAGE f1 (moi_s34_vb tt kk v1 INTER moi_s34_vb tt kk v3 INTER
                             moi_s34_bd tt kk) UNION
                   IMAGE f1 (moi_s34_vb tt kk v2 INTER moi_s34_vb tt kk v3 INTER
                             moi_s34_bd tt kk)` THEN
      REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)) THENL
     [MAP_EVERY EXISTS_TAC [`v1:real^N`; `v2:real^N`];
      MAP_EVERY EXISTS_TAC [`v1:real^N`; `v3:real^N`];
      MAP_EVERY EXISTS_TAC [`v2:real^N`; `v3:real^N`]] THEN
    ASM_REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN CONJ_TAC THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = a` THENL
   [EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(a:real^N = b)` THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = b` THENL
   [EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `a:real^N`; `b:real^N`] MOI_S4T_TRI_PAIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^N` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[]);;

(* A gap between consecutive rim times: the arc lies in one A_u and its   *)
(* ends lie on the rims of the two different edges of s at u (Lemma 10).  *)
let MOI_S4T_GAP = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j l x y.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     (!s v g a aa. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\ g IN moi_s34_simp kk (&1) /\
                   pl_cell_with_boundary 1 a aa /\
                   a SUBSET moi_s34_trace tt kk f1 (cb s) /\
                   a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                   aa SUBSET IMAGE f1 (moi_s34_sd tt kk g) /\
                   a INTER moi_s34_rims tt kk f1 = aa
                   ==> F) /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     simple_path l /\ pathfinish l = pathstart l /\ pl_map_on (interval[vec 0,vec 1]) l /\
     path_image l = j /\ pathstart l IN moi_s34_rims tt kk f1 /\
     2 <= CARD (j INTER moi_s34_rims tt kk f1) /\
     FINITE (j INTER moi_s34_rims tt kk f1) /\
     moi_s4t_gap {t | &0 <= t /\ t <= &1 /\ l(lift t) IN j INTER moi_s34_rims tt kk f1} x y
     ==> ?u w1 w2. u IN {v1,v2,v3} /\ w1 IN {v1,v2,v3} /\ w2 IN {v1,v2,v3} /\
                   ~(u = w1) /\ ~(u = w2) /\ ~(w1 = w2) /\
                   IMAGE l (interval[lift x,lift y]) SUBSET
                   IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) /\
                   l(lift x) IN IMAGE f1 (moi_s34_vb tt kk u) /\
                   l(lift x) IN IMAGE f1 (moi_s34_vb tt kk w1) /\
                   l(lift y) IN IMAGE f1 (moi_s34_vb tt kk u) /\
                   l(lift y) IN IMAGE f1 (moi_s34_vb tt kk w2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_BALLS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_TRACE) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `moi_s34_trace tt kk (f1:real^N->real^3)
                       ((cb:(real^N->bool)->real^3->bool) s)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4t_tri]) THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s4t_gap; IN_ELIM_THM] o
    check (moi_s4l_has "moi_s4t_gap")) THEN
  SUBGOAL_THEN `path (l:real^1->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `interval[lift x,lift y] SUBSET interval[vec 0,vec 1] /\
                interval(lift x,lift y) SUBSET interval[vec 0,vec 1] /\
                lift x IN interval[vec 0,vec 1] /\ lift y IN interval[vec 0,vec 1] /\
                lift x IN interval[lift x,lift y] /\ lift y IN interval[lift x,lift y]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= x`; `x <= &1`; `&0 <= y`; `y <= &1`; `x < y`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^1->real^3) continuous_on interval[vec 0,vec 1]` ASSUME_TAC THENL
   [ASM_MESON_TAC[path]; ALL_TAC] THEN
  (* the open arc misses the rims *)
  SUBGOAL_THEN
   `connected (IMAGE (l:real^1->real^3) (interval(lift x,lift y))) /\
    IMAGE l (interval(lift x,lift y)) SUBSET
    moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s) /\
    IMAGE l (interval(lift x,lift y)) INTER moi_s34_rims tt kk f1 = {}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_INTERVAL] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
      REWRITE_TAC[path_image] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
      X_GEN_TAC `z:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `z:real^3`)) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `drop t` o check (fun th ->
        is_forall(concl th) && moi_s4l_has "moi_s34_rims" th)) THEN
      REWRITE_TAC[LIFT_DROP; IN_INTER; NOT_IMP] THEN
      SUBGOAL_THEN `(t:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
        REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(t:real^1) IN interval(lift x,lift y)` THEN
        REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `(t:real^1) IN interval(lift x,lift y)` THEN
        REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `IMAGE (l:real^1->real^3) (interval(lift x,lift y))`]
    MOI_S4T_CONNECTED_ONE_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{u:real^N} IN kk` ASSUME_TAC THENL
   [UNDISCH_TAC `(u:real^N) IN {v1,v2,v3}` THEN
    UNDISCH_TAC `{x | x IN s /\ {x} IN kk} = {v1:real^N,v2,v3}` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the closed arc lies in A_u *)
  SUBGOAL_THEN `IMAGE (l:real^1->real^3) (interval[lift x,lift y]) SUBSET
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `interval[lift x,lift y] = closure(interval(lift x,lift y))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
      REWRITE_TAC[INTERVAL_NE_EMPTY_1; LIFT_DROP] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `closure(interval(lift x,lift y)) = interval[lift x,lift y]`
      SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
        REWRITE_TAC[INTERVAL_NE_EMPTY_1; LIFT_DROP] THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `u:real^N`] MOI_S4L_AV_BASIC) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^1->real^3)(lift x) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) /\
                l(lift y) IN IMAGE f1 (moi_s34_vb tt kk u) /\
                l(lift x) IN j /\ l(lift y) IN j /\
                l(lift x) IN moi_s34_rims tt kk f1 /\ l(lift y) IN moi_s34_rims tt kk f1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(ASM SET_TAC[]) THEN
    MATCH_MP_TAC(SET_RULE `!a. (z:real^3) IN a /\ a SUBSET b /\ b SUBSET c ==> z IN c`) THEN
    EXISTS_TAC `IMAGE (l:real^1->real^3) (interval[lift x,lift y])` THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `(l:real^1->real^3)(lift x)`; `u:real^N`] MOI_S4T_TRI_RIMPT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `(l:real^1->real^3)(lift y)`; `u:real^N`] MOI_S4T_TRI_RIMPT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `w1:real^N`; `w2:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(UNDISCH_TAC `~(w1:real^N = u)` THEN MESON_TAC[] THEN NO_TAC) THEN
  TRY(UNDISCH_TAC `~(w2:real^N = u)` THEN MESON_TAC[] THEN NO_TAC) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  (* the two ends differ *)
  SUBGOAL_THEN `~((l:real^1->real^3)(lift x) = l(lift y))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`lift x`; `lift y`] (CONJUNCT2(GEN_REWRITE_RULE I [simple_path]
      (ASSUME `simple_path (l:real^1->real^3)`)))) THEN
    ASM_REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `x < y` THEN ASM_REWRITE_TAC[REAL_LT_REFL];
      ALL_TAC;
      UNDISCH_TAC `x < y` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`l:real^1->real^3`; `j INTER moi_s34_rims tt kk (f1:real^N->real^3)`]
      MOI_S4T_TIMES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INTER_SUBSET] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
      REWRITE_TAC[IN_INTER; PATHSTART_IN_PATH_IMAGE] THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    SUBGOAL_THEN `{t | &0 <= t /\ t <= &1 /\
                       (l:real^1->real^3)(lift t) IN j INTER moi_s34_rims tt kk
                       (f1:real^N->real^3)} SUBSET {&0,&1}` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        is_forall(concl th) && moi_s4l_has "moi_s34_rims" th)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 <= t` THEN UNDISCH_TAC `t <= &1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`{t | &0 <= t /\ t <= &1 /\
                         (l:real^1->real^3)(lift t) IN j INTER moi_s34_rims tt kk
                         (f1:real^N->real^3)}`; `{&0,&1}`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[REAL_ARITH `~(&0 = &1)`] THEN
    UNDISCH_TAC `2 <= CARD (j INTER moi_s34_rims tt kk (f1:real^N->real^3))` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the arc is a 1-cell with the two ends as boundary *)
  MP_TAC(ISPEC `subpath (lift x) (lift y) (l:real^1->real^3)` MOI_S4O_ARC_CELL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_PL2_PL_SUBPATH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  SUBGOAL_THEN `path_image (subpath (lift x) (lift y) (l:real^1->real^3)) =
                IMAGE l (interval[lift x,lift y])` SUBST1_TAC THENL
   [MATCH_MP_TAC PATH_IMAGE_SUBPATH THEN REWRITE_TAC[LIFT_DROP] THEN
    UNDISCH_TAC `x < y` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `u:real^N`; `w2:real^N`] MOI_S4T_TRI_PAIR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(w2:real^N = u)` THEN MESON_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `u:real^N`; `w2:real^N`] MOI_S4L_EDGE_SD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`s:real^N->bool`; `u:real^N`; `segment[u:real^N,w2]`;
    `IMAGE (l:real^1->real^3) (interval[lift x,lift y])`;
    `{(l:real^1->real^3)(lift x),l(lift y)}`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 5)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
    REWRITE_TAC[path_image] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) =
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w2)`)) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `interval[lift x,lift y] = interval(lift x,lift y) UNION {lift x,lift y}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSED_OPEN_INTERVAL_1 THEN REWRITE_TAC[LIFT_DROP] THEN
      UNDISCH_TAC `x < y` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_UNION; IMAGE_CLAUSES] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (l:real^1->real^3) (interval(lift x,lift y)) INTER
       moi_s34_rims tt kk (f1:real^N->real^3) = {}`;
      `(l:real^1->real^3)(lift x) IN moi_s34_rims tt kk (f1:real^N->real^3)`;
      `(l:real^1->real^3)(lift y) IN moi_s34_rims tt kk (f1:real^N->real^3)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`IMAGE (l:real^1->real^3) (interval(lift x,lift y))`, `K:real^3->bool`;
      `moi_s34_rims tt kk (f1:real^N->real^3)`, `RR:real^3->bool`] THEN
    SET_TAC[]]);;


(* Near an interior point of the loop, the trace is the loop's open arc. *)
let MOI_S4T_LOCAL_ARC = prove
 (`!(t:real^N->bool) j (l:real^1->real^N) x y z.
     compact t /\ FINITE (components t) /\ j IN components t /\
     simple_path l /\ pathfinish l = pathstart l /\ path_image l = j /\
     &0 <= x /\ x < y /\ y < z /\ z <= &1
     ==> ?e. &0 < e /\ t INTER ball(l(lift y),e) SUBSET IMAGE l (interval(lift x,lift z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `path (l:real^1->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  ABBREV_TAC `kc = (t DIFF j) UNION IMAGE (l:real^1->real^N) (interval[vec 0,lift x]) UNION
                   IMAGE l (interval[lift z,vec 1])` THEN
  SUBGOAL_THEN `closed (kc:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "kc" THEN REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THENL
     [SUBGOAL_THEN `t DIFF j = UNIONS (components t DELETE (j:real^N->bool))` SUBST1_TAC THENL
       [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [UNIONS_COMPONENTS] THEN
        REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIONS; IN_DELETE] THEN
        X_GEN_TAC `q:real^N` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`t:real^N->bool`; `c:real^N->bool`; `j:real^N->bool`]
          COMPONENTS_NONOVERLAP) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
        ASM_MESON_TAC[CLOSED_COMPONENTS; COMPACT_IMP_CLOSED]];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[COMPACT_INTERVAL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[path]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[COMPACT_INTERVAL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[path]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((l:real^1->real^N)(lift y) IN kc)` ASSUME_TAC THENL
   [EXPAND_TAC "kc" THEN REWRITE_TAC[IN_UNION; IN_DIFF; DE_MORGAN_THM] THEN
    REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `j:real^N->bool`)) THEN
      REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^1` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`lift y`; `r:real^1`] (CONJUNCT2(GEN_REWRITE_RULE I [simple_path]
      (ASSUME `simple_path (l:real^1->real^N)`)))) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; GSYM DROP_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kc:real^N->bool`; `(l:real^1->real^N)(lift y)`] SEPARATE_POINT_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN X_GEN_TAC `q:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((q:real^N) IN kc)` MP_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `q:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "kc" THEN REWRITE_TAC[IN_UNION; IN_DIFF; DE_MORGAN_THM] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(q:real^N) IN j` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && rand(concl th) = `j:real^N->bool`)) THEN
  REWRITE_TAC[path_image; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^1` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((q:real^N) IN IMAGE l (interval[vec 0,lift x]))` THEN
  UNDISCH_TAC `~((q:real^N) IN IMAGE l (interval[lift z,vec 1]))` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(r:real^1) IN interval[vec 0,vec 1]` THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
  MESON_TAC[REAL_NOT_LT; REAL_LE_TOTAL]);;

(* The crossing property: the arcs before and after an interior rim time *)
(* lie in different pieces A_u.                                          *)
let MOI_S4T_CROSS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j l x y z u u'.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     simple_path l /\ pathfinish l = pathstart l /\ path_image l = j /\
     &0 <= x /\ x < y /\ y < z /\ z <= &1 /\
     l(lift y) IN moi_s34_rims tt kk f1 /\ u IN {v1,v2,v3} /\ u' IN {v1,v2,v3} /\
     IMAGE l (interval[lift x,lift y]) SUBSET
     IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) /\
     IMAGE l (interval[lift y,lift z]) SUBSET
     IMAGE f1 (moi_s34_vb tt kk u' INTER moi_s34_bd tt kk)
     ==> ~(u = u')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_TRACE) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `moi_s34_trace tt kk (f1:real^N->real^3)
                       ((cb:(real^N->bool)->real^3->bool) s)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4t_tri]) THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (l:real^1->real^3) (interval[lift x,lift z]) SUBSET
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u' INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `interval[lift x,lift z] = interval[lift x,lift y] UNION
                                            interval[lift y,lift z]` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[IMAGE_UNION; UNION_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^1->real^3)(lift y) IN j /\
                l(lift y) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
      REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(SET_RULE `!a b. (q:real^3) IN a /\ a SUBSET b /\ b SUBSET c ==> q IN c`) THEN
      EXISTS_TAC `IMAGE (l:real^1->real^3) (interval[lift x,lift z])` THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u' INTER moi_s34_bd tt kk)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `(l:real^1->real^3)(lift y)`; `u':real^N`] MOI_S4T_TRI_RIMPT) THEN
  SUBGOAL_THEN `(l:real^1->real^3)(lift y) IN moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a. (q:real^3) IN a /\ a SUBSET b ==> q IN b`) THEN
    EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `u':real^N`; `w:real^N`] MOI_S4T_TRI_PAIR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(w:real^N = u')` THEN MESON_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`;
                 `j:real^3->bool`; `l:real^1->real^3`; `x:real`; `y:real`; `z:real`]
    MOI_S4T_LOCAL_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `(cb:(real^N->bool)->real^3->bool) s`; `u':real^N`; `w:real^N`;
                 `(l:real^1->real^3)(lift y)`; `e:real`] MOI_S4L_CROSS_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    (FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) =
        `IMAGE (f1:real^N->real^3)
           (moi_s34_vb tt kk u' INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`)) THEN
      REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC(SET_RULE `!a. (q:real^3) IN a /\ a SUBSET b ==> q IN b`) THEN
      EXISTS_TAC `IMAGE (l:real^1->real^3) (interval[lift x,lift z])` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `~((q:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u'))` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `!a b c. (q:real^3) IN a /\ a SUBSET b /\ b SUBSET c /\ c SUBSET d
                                 ==> q IN d`) THEN
  MAP_EVERY EXISTS_TAC
   [`moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s) INTER
     ball((l:real^1->real^3)(lift y),e)`;
    `IMAGE (l:real^1->real^3) (interval[lift x,lift z])`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u' INTER moi_s34_bd tt kk)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(k:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                   ((cb:(real^N->bool)->real^3->bool) s) INTER ball(l(lift y),e)` THEN
    UNDISCH_TAC `(q:real^3) IN k` THEN SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (l:real^1->real^3) (interval(lift x,lift z))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED];
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* The winding of the sector map along a trace component: m/3 for m rim      *)
(* points, by equal steps at every rim time.                                 *)
(* ------------------------------------------------------------------------- *)

(* The sector-map increment of a lift over one gap. *)
let MOI_S4T_GAP_INCR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j l x y
    (phi:real^3->complex) (pp:real^N->real^3->real^1) kc sg q.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     (!s v g a aa. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\ g IN moi_s34_simp kk (&1) /\
                   pl_cell_with_boundary 1 a aa /\
                   a SUBSET moi_s34_trace tt kk f1 (cb s) /\
                   a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                   aa SUBSET IMAGE f1 (moi_s34_sd tt kk g) /\
                   a INTER moi_s34_rims tt kk f1 = aa
                   ==> F) /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     simple_path l /\ pathfinish l = pathstart l /\ pl_map_on (interval[vec 0,vec 1]) l /\
     path_image l = j /\ pathstart l IN moi_s34_rims tt kk f1 /\
     2 <= CARD (j INTER moi_s34_rims tt kk f1) /\ FINITE (j INTER moi_s34_rims tt kk f1) /\
     (!u. pp u continuous_on (:real^3)) /\
     (!u x. u IN {v1,v2,v3} /\ x IN IMAGE f1 (moi_s34_vb tt kk u)
            ==> phi x = cexp(Cx(&2 * pi / &3) * ii * (Cx(kc u) + Cx(drop(pp u x))))) /\
     (!u w x. u IN {v1,v2,v3} /\ w IN {v1,v2,v3} /\ ~(u = w) /\
              x IN IMAGE f1 (moi_s34_vb tt kk u) /\ x IN IMAGE f1 (moi_s34_vb tt kk w)
              ==> drop(pp u x) = sg u w) /\
     path q /\ (!t. t IN interval[vec 0,vec 1] ==> phi(l t) = cexp(q t)) /\
     moi_s4t_gap {t | &0 <= t /\ t <= &1 /\ l(lift t) IN j INTER moi_s34_rims tt kk f1} x y
     ==> ?u w1 w2. u IN {v1,v2,v3} /\ w1 IN {v1,v2,v3} /\ w2 IN {v1,v2,v3} /\
                   ~(u = w1) /\ ~(u = w2) /\ ~(w1 = w2) /\
                   IMAGE l (interval[lift x,lift y]) SUBSET
                   IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) /\
                   l(lift x) IN IMAGE f1 (moi_s34_vb tt kk u) /\
                   l(lift x) IN IMAGE f1 (moi_s34_vb tt kk w1) /\
                   l(lift y) IN IMAGE f1 (moi_s34_vb tt kk u) /\
                   l(lift y) IN IMAGE f1 (moi_s34_vb tt kk w2) /\
                   q(lift y) - q(lift x) =
                   Cx(&2 * pi / &3) * ii * (Cx(sg u w2) - Cx(sg u w1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`; `l:real^1->real^3`; `x:real`; `y:real`] MOI_S4T_GAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w1:real^N`
    (X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `w1:real^N`; `w2:real^N`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s4t_gap; IN_ELIM_THM] o
    check (moi_s4l_has "moi_s4t_gap")) THEN
  SUBGOAL_THEN `interval[lift x,lift y] SUBSET interval[vec 0,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^1->real^3) continuous_on interval[vec 0,vec 1]` ASSUME_TAC THENL
   [ASM_MESON_TAC[path; SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^1->complex`;
                 `\t. Cx(&2 * pi / &3) * ii *
                      (Cx(kc(u:real^N)) + Cx(drop((pp:real^N->real^3->real^1) u
                                                  ((l:real^1->real^3) t))))`;
                 `interval[lift x,lift y]`; `lift x`; `lift y`] MOI_S4T_LOG_INCR) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONNECTED_INTERVAL; ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1; LIFT_DROP] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[GSYM path];
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
      SUBGOAL_THEN `(\t. (pp:real^N->real^3->real^1) u ((l:real^1->real^3) t)) = pp u o l`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(t:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME
        `(t:real^1) IN interval[vec 0,vec 1]`))]) o check (fun th ->
        is_forall(concl th) && moi_s4l_has "cexp" th &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!a b. (q:real^3) IN a /\ a SUBSET b /\ b SUBSET c ==> q IN c`) THEN
      EXISTS_TAC `IMAGE (l:real^1->real^3) (interval[lift x,lift y])` THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `drop((pp:real^N->real^3->real^1) u ((l:real^1->real^3)(lift y))) =
                (sg:real^N->real^N->real) u w2 /\
                drop((pp:real^N->real^3->real^1) u ((l:real^1->real^3)(lift x))) = sg u w1`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    CONV_TAC COMPLEX_RING]);;

let MOI_S4T_PM_ONE = prove
 (`!a b c d. (a = &0 \/ a = &1) /\ (b = &0 \/ b = &1) /\ b + a = &1
             ==> c * d * (Cx a - Cx b) = c * d \/ c * d * (Cx a - Cx b) = --(c * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (moi_s4l_has "real_add")) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_SUB_RZERO; COMPLEX_SUB_LZERO; COMPLEX_MUL_RID;
              COMPLEX_MUL_RNEG]);;

let MOI_S4T_COMP_WINDING = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j l
    (phi:real^3->complex) (pp:real^N->real^3->real^1) kc sg.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     (!s v g a aa. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\ g IN moi_s34_simp kk (&1) /\
                   pl_cell_with_boundary 1 a aa /\
                   a SUBSET moi_s34_trace tt kk f1 (cb s) /\
                   a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                   aa SUBSET IMAGE f1 (moi_s34_sd tt kk g) /\
                   a INTER moi_s34_rims tt kk f1 = aa
                   ==> F) /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     simple_path l /\ pathfinish l = pathstart l /\ pl_map_on (interval[vec 0,vec 1]) l /\
     path_image l = j /\ pathstart l IN moi_s34_rims tt kk f1 /\
     2 <= CARD (j INTER moi_s34_rims tt kk f1) /\ FINITE (j INTER moi_s34_rims tt kk f1) /\
     phi continuous_on IMAGE f1 (moi_s34_ft tt kk s) /\
     IMAGE phi (IMAGE f1 (moi_s34_ft tt kk s)) SUBSET sphere(vec 0,&1) /\
     (!u. pp u continuous_on (:real^3)) /\
     (!u x. u IN {v1,v2,v3} /\ x IN IMAGE f1 (moi_s34_vb tt kk u)
            ==> phi x = cexp(Cx(&2 * pi / &3) * ii * (Cx(kc u) + Cx(drop(pp u x))))) /\
     (!u w x. u IN {v1,v2,v3} /\ w IN {v1,v2,v3} /\ ~(u = w) /\
              x IN IMAGE f1 (moi_s34_vb tt kk u) /\ x IN IMAGE f1 (moi_s34_vb tt kk w)
              ==> drop(pp u x) = sg u w) /\
     (!u w. u IN {v1,v2,v3} /\ w IN {v1,v2,v3} /\ ~(u = w) ==> sg u w + sg w u = &1) /\
     (!u w1 w2. u IN {v1,v2,v3} /\ w1 IN {v1,v2,v3} /\ w2 IN {v1,v2,v3} /\
                ~(u = w1) /\ ~(u = w2) /\ ~(w1 = w2)
                ==> sg u w1 + sg u w2 = &1) /\
     (!u w. sg u w = &0 \/ sg u w = &1)
     ==> Cx(&2) * Cx pi * ii * winding_number(phi o l,Cx(&0)) =
         Cx(&(CARD (j INTER moi_s34_rims tt kk f1))) * (Cx(&2 * pi / &3) * ii) \/
         Cx(&2) * Cx pi * ii * winding_number(phi o l,Cx(&0)) =
         --(Cx(&(CARD (j INTER moi_s34_rims tt kk f1))) * (Cx(&2 * pi / &3) * ii))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_BALLS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_TRACE) THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN
    ASM_REWRITE_TAC[] THEN REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `moi_s34_trace tt kk (f1:real^N->real^3)
                       ((cb:(real^N->bool)->real^3->bool) s)`)) THEN
  SUBGOAL_THEN `path ((phi:real^3->complex) o (l:real^1->real^3)) /\
                ~(Cx(&0) IN path_image (phi o l))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC SIMPLE_PATH_IMP_PATH THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `Cx(&0) IN sphere(vec 0,&1)` MP_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!f a b. (z:complex) IN IMAGE (f:real^3->complex) a /\
                                     a SUBSET b /\ IMAGE f b SUBSET c ==> z IN c`) THEN
        MAP_EVERY EXISTS_TAC [`phi:real^3->complex`; `path_image (l:real^1->real^3)`;
                              `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
        FIRST_ASSUM(SUBST1_TAC o check (fun th ->
          is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[IN_SPHERE_0; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(phi:real^3->complex) o (l:real^1->real^3)`; `Cx(&0)`]
    WINDING_NUMBER_AS_CONTINUOUS_LOGARITHM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_ADD_LID; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->complex` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && moi_s4l_has "winding_number" th)) THEN
  REWRITE_TAC[pathstart; pathfinish] THEN
  MP_TAC(ISPECL [`l:real^1->real^3`; `j INTER moi_s34_rims tt kk (f1:real^N->real^3)`]
    MOI_S4T_TIMES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
    REWRITE_TAC[IN_INTER; PATHSTART_IN_PATH_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INTER_SUBSET];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`{t | &0 <= t /\ t <= &1 /\
                       (l:real^1->real^3)(lift t) IN j INTER moi_s34_rims tt kk
                       (f1:real^N->real^3)}`;
                 `\t. (q:real^1->complex)(lift t)`; `Cx(&2 * pi / &3) * ii`;
                 `&0`; `&1`] MOI_S4T_STEPS) THEN
  ASM_REWRITE_TAC[LIFT_NUM; REAL_LT_01; ADD_SUB] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                     `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                     `j:real^3->bool`; `l:real^1->real^3`; `x:real`; `y:real`;
                     `phi:real^3->complex`; `pp:real^N->real^3->real^1`;
                     `kc:real^N->real`; `sg:real^N->real^N->real`; `q:real^1->complex`]
        MOI_S4T_GAP_INCR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w1:real^N`
        (X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4T_PM_ONE THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 3 && moi_s4l_has "real_add" th)) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `z:real`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                     `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                     `j:real^3->bool`; `l:real^1->real^3`; `x:real`; `y:real`;
                     `phi:real^3->complex`; `pp:real^N->real^3->real^1`;
                     `kc:real^N->real`; `sg:real^N->real^N->real`; `q:real^1->complex`]
        MOI_S4T_GAP_INCR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w1:real^N`
        (X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC))) THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                     `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                     `j:real^3->bool`; `l:real^1->real^3`; `y:real`; `z:real`;
                     `phi:real^3->complex`; `pp:real^N->real^3->real^1`;
                     `kc:real^N->real`; `sg:real^N->real^N->real`; `q:real^1->complex`]
        MOI_S4T_GAP_INCR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u':real^N` (X_CHOOSE_THEN `w1':real^N`
        (X_CHOOSE_THEN `w2':real^N` STRIP_ASSUME_TAC))) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY (fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o
          REWRITE_RULE[moi_s4t_gap; IN_ELIM_THM] o check (fun th' -> aconv (concl th') th)))
       [`moi_s4t_gap {t | &0 <= t /\ t <= &1 /\ (l:real^1->real^3)(lift t) IN
                          j INTER moi_s34_rims tt kk (f1:real^N->real^3)} x y`;
        `moi_s4t_gap {t | &0 <= t /\ t <= &1 /\ (l:real^1->real^3)(lift t) IN
                          j INTER moi_s34_rims tt kk (f1:real^N->real^3)} y z`] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                     `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                     `j:real^3->bool`; `l:real^1->real^3`; `x:real`; `y:real`; `z:real`;
                     `u:real^N`; `u':real^N`] MOI_S4T_CROSS) THEN
      SUBGOAL_THEN `(l:real^1->real^3)(lift y) IN moi_s34_rims tt kk (f1:real^N->real^3)`
      ASSUME_TAC THENL
       [UNDISCH_TAC `(l:real^1->real^3)(lift y) IN j INTER moi_s34_rims tt kk
                      (f1:real^N->real^3)` THEN REWRITE_TAC[IN_INTER] THEN MESON_TAC[];
        ALL_TAC] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                     `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                     `u:real^N`; `u':real^N`] MOI_S4T_TRI_PAIR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o last o CONJUNCTS)] THEN
      DISCH_THEN(LABEL_TAC "trip") THEN
      SUBGOAL_THEN `w2:real^N = u' /\ w1':real^N = u` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
       [CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THENL
         [USE_THEN "trip" (MP_TAC o SPEC `w2:real^N`);
          USE_THEN "trip" (MP_TAC o SPEC `w1':real^N`)] THEN
        (ANTS_TAC THENL
          [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN ASM_REWRITE_TAC[];
           ALL_TAC]) THEN
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `(l:real^1->real^3)(lift y)`) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM CX_SUB] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `(sg:real^N->real^N->real) u u' + sg u' u = &1 /\
                    sg u w1 + sg u u' = &1 /\ sg u' u + sg u' w2' = &1` MP_TAC THENL
       [REPEAT CONJ_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          moi_s4l_has "real_add" th && moi_s4l_has "IN" th)) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 28.8 in the used form gives three rim points on every trace component,    *)
(* one on each rim of the triangle (towards TRACE).                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4T_COUNT_ARITH = prove
 (`!n w. (Cx(&2) * Cx pi * ii * w = Cx(&n) * (Cx(&2 * pi / &3) * ii) \/
          Cx(&2) * Cx pi * ii * w = --(Cx(&n) * (Cx(&2 * pi / &3) * ii)))
         ==> ((w = Cx(&1) \/ w = --Cx(&1)) ==> n = 3) /\ (w = Cx(&0) ==> n = 0)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `~(Cx(&2) * Cx pi * ii = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; II_NZ; PI_NZ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Cx(&2 * pi / &3) * ii = (Cx(&2) * Cx pi * ii) / Cx(&3)` SUBST1_TAC THENL
   [REWRITE_TAC[CX_MUL; CX_DIV] THEN CONV_TAC COMPLEX_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Cx(&2) * Cx pi * ii * w = Cx(&n) * (Cx(&2) * Cx pi * ii) / Cx(&3) <=>
     Cx(&n) = Cx(&3) * w) /\
    (Cx(&2) * Cx pi * ii * w = --(Cx(&n) * (Cx(&2) * Cx pi * ii) / Cx(&3)) <=>
     Cx(&n) = --(Cx(&3) * w))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `~(Cx(&2) * Cx pi * ii = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD; ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `Cx(&n)`)) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RID; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG; COMPLEX_MUL_RZERO;
                  COMPLEX_NEG_0] THEN
  REWRITE_TAC[GSYM CX_NEG; CX_INJ; REAL_OF_NUM_EQ; REAL_ARITH `~(&n = -- &3)`]);;

(* Lemma 11, counting form: every trace component has exactly three rim points. *)
let MOI_S4T_COMP_THREE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j.
     MOISE_288_STATEMENT /\
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     (!s v j. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
              j IN components (moi_s34_trace tt kk f1 (cb s))
              ==> ~(j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))) /\
     (!s v g a aa. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\ g IN moi_s34_simp kk (&1) /\
                   pl_cell_with_boundary 1 a aa /\
                   a SUBSET moi_s34_trace tt kk f1 (cb s) /\
                   a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                   aa SUBSET IMAGE f1 (moi_s34_sd tt kk g) /\
                   a INTER moi_s34_rims tt kk f1 = aa
                   ==> F) /\
     j IN components (moi_s34_trace tt kk f1 (cb s))
     ==> CARD (j INTER moi_s34_rims tt kk f1) = 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_BALLS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_TRACE) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `moi_s34_trace tt kk (f1:real^N->real^3)
                       ((cb:(real^N->bool)->real^3->bool) s)`)) THEN
  SUBGOAL_THEN `closed (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`] MOI_S4T_COMP_RIMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`] MOI_S4T_COMP_LOOP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `2 <= CARD (j INTER moi_s34_rims tt kk (f1:real^N->real^3))` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `l:real^1->real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`]
    MOI_S4T_TRI_SECTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->complex` (X_CHOOSE_THEN `pp:real^N->real^3->real^1`
    (X_CHOOSE_THEN `kc:real^N->real` (X_CHOOSE_THEN `sg:real^N->real^N->real`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`; `l:real^1->real^3`; `phi:real^3->complex`;
                 `pp:real^N->real^3->real^1`; `kc:real^N->real`;
                 `sg:real^N->real^N->real`] MOI_S4T_COMP_WINDING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_COUNT_ARITH) THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET frontier (IMAGE (f1:real^N->real^3)
                  (moi_s34_ft tt kk s))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)) SUBSET
                IMAGE f1 (moi_s34_ft tt kk s)` ASSUME_TAC THENL
   [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* 28.8 *)
  UNDISCH_TAC `MOISE_288_STATEMENT` THEN REWRITE_TAC[MOISE_288_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`;
    `components (moi_s34_trace tt kk (f1:real^N->real^3)
                   ((cb:(real^N->bool)->real^3->bool) s))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PAIRWISE_DISJOINT_COMPONENTS; GSYM UNIONS_COMPONENTS] THEN
    X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3)
                    ((cb:(real^N->bool)->real^3->bool) s)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC MOI_S4T_CARRIES_UNIT THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
    EXISTS_TAC `g:real^1->real^3` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    MP_TAC(ISPECL [`d:real^3->bool`; `phi:real^3->complex`; `l:real^1->real^3`]
      MOI_S4T_CONTRACTIBLE_WINDING) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `(d:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) /\
                    (j:real^3->bool) SUBSET d` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` THEN
          CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS o check (fun th ->
            moi_s4l_has "pl_cell_with_boundary" th)) THEN SIMP_TAC[]];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4T_CELL_CONTRACTIBLE THEN
        MAP_EVERY EXISTS_TAC [`2`; `j:real^3->bool`] THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(phi:real^3->complex) x IN sphere(vec 0,&1)` MP_TAC THENL
         [MATCH_MP_TAC(SET_RULE `!a b. (x:real^3) IN a /\ a SUBSET b /\
                                       IMAGE (f:real^3->complex) b SUBSET c ==> f x IN c`) THEN
          MAP_EVERY EXISTS_TAC [`d:real^3->bool`;
                                `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`] THEN
          REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          DISCH_TAC THEN DISCH_TAC THEN UNDISCH_TAC `(phi:real^3->complex) x IN sphere(vec 0,&1)` THEN
          ASM_REWRITE_TAC[IN_SPHERE_0; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC];
        MATCH_MP_TAC SIMPLE_PATH_IMP_PATH THEN FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      DISCH_TAC] THEN
    SUBGOAL_THEN `CARD (j INTER moi_s34_rims tt kk (f1:real^N->real^3)) = 0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `2 <= CARD (j INTER moi_s34_rims tt kk (f1:real^N->real^3))` THEN
    ARITH_TAC]);;

(* A four-element set of times from 0 to 1 and its three gaps. *)
let MOI_S4T_FOUR_TIMES = prove
 (`!r. FINITE r /\ &0 IN r /\ &1 IN r /\ (!x. x IN r ==> &0 <= x /\ x <= &1) /\
       CARD r = 4
       ==> ?r1 r2. &0 < r1 /\ r1 < r2 /\ r2 < &1 /\ r = {&0,r1,r2,&1} /\
                   moi_s4t_gap r (&0) r1 /\ moi_s4t_gap r r1 r2 /\ moi_s4t_gap r r2 (&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r DELETE &0 DELETE &1) HAS_SIZE 2` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE; IN_DELETE] THEN
    REWRITE_TAC[REAL_ARITH `~(&1 = &0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `r = {&0,a,b,&1}` ASSUME_TAC THENL
   [UNDISCH_TAC `r DELETE &0 DELETE &1 = {a:real,b}` THEN
    UNDISCH_TAC `&0 IN r` THEN UNDISCH_TAC `&1 IN r` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a /\ a < &1 /\ &0 < b /\ b < &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(a:real) IN r DELETE &0 DELETE &1 /\ b IN r DELETE &0 DELETE &1`
    MP_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `a:real` o check (is_forall o concl)) THEN
    FIRST_ASSUM(MP_TAC o SPEC `b:real` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[REAL_LT_LE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c d. &0 < c /\ c < d /\ d < &1 /\ {&0,a,b,&1} = {&0,c,d,&1}
                      ==> ?r1 r2. &0 < r1 /\ r1 < r2 /\ r2 < &1 /\ r = {&0,r1,r2,&1} /\
                                  moi_s4t_gap r (&0) r1 /\ moi_s4t_gap r r1 r2 /\
                                  moi_s4t_gap r r2 (&1)`
  MATCH_MP_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`c:real`; `d:real`] THEN
    ASM_REWRITE_TAC[moi_s4t_gap; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real < b` THENL
   [MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`b:real`; `a:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; SET_TAC[]]]);;

(* Three pairwise different 2-subsets of a 3-set are all of them. *)
let MOI_S4T_THREE_PAIRS = prove
 (`!(v1:A) v2 v3 e0 e1 e2.
     ~(v1 = v2) /\ ~(v1 = v3) /\ ~(v2 = v3) /\
     (e0 = {v1,v2} \/ e0 = {v1,v3} \/ e0 = {v2,v3}) /\
     (e1 = {v1,v2} \/ e1 = {v1,v3} \/ e1 = {v2,v3}) /\
     (e2 = {v1,v2} \/ e2 = {v1,v3} \/ e2 = {v2,v3}) /\
     ~(e0 = e1) /\ ~(e1 = e2) /\ ~(e0 = e2)
     ==> !e. (e = {v1,v2} \/ e = {v1,v3} \/ e = {v2,v3})
             ==> e = e0 \/ e = e1 \/ e = e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && is_var(lhs(concl th))))) THEN
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_neg o concl))) THEN
  REWRITE_TAC[]);;

let MOI_S4T_PAIR_CASES = prove
 (`!(v1:A) v2 v3 a b.
     a IN {v1,v2,v3} /\ b IN {v1,v2,v3} /\ ~(a = b)
     ==> {a,b} = {v1,v2} \/ {a,b} = {v1,v3} \/ {a,b} = {v2,v3}`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
  moi_s4t_vcases [`a:A`; `b:A`] THEN REWRITE_TAC[INSERT_AC]);;

(* The vertex balls containing a point of two of them. *)
let MOI_S4T_EDGE_SET = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 u w p.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     u IN {v1,v2,v3} /\ w IN {v1,v2,v3} /\ ~(u = w) /\
     p IN IMAGE f1 (moi_s34_vb tt kk u) /\ p IN IMAGE f1 (moi_s34_vb tt kk w)
     ==> {x | x IN {v1,v2,v3} /\ p IN IMAGE f1 (moi_s34_vb tt kk x)} = {u,w}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `u:real^N`; `w:real^N`] MOI_S4T_TRI_PAIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o last o CONJUNCTS)] THEN
  DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    ASM_CASES_TAC `x:real^N = u` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `x:real^N = w` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && moi_s4l_has "INTER" th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(p:real^3) IN a /\ p IN b /\ p IN c
                           ==> a INTER b INTER c = {} ==> F`) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY]) THEN ASM_REWRITE_TAC[]]);;

(* A trace component does not lie in a contractible part of the face torus *)
(* (the disk branch of 28.8; exported for s34_fdisk).                     *)
let MOI_S4T_COMP_NO_DISK = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j d.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     (!s v j. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
              j IN components (moi_s34_trace tt kk f1 (cb s))
              ==> ~(j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))) /\
     (!s v g a aa. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\ g IN moi_s34_simp kk (&1) /\
                   pl_cell_with_boundary 1 a aa /\
                   a SUBSET moi_s34_trace tt kk f1 (cb s) /\
                   a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                   aa SUBSET IMAGE f1 (moi_s34_sd tt kk g) /\
                   a INTER moi_s34_rims tt kk f1 = aa
                   ==> F) /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     contractible d /\ j SUBSET d /\ d SUBSET IMAGE f1 (moi_s34_ft tt kk s)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`] MOI_S4T_COMP_RIMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`] MOI_S4T_COMP_LOOP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `2 <= CARD (j INTER moi_s34_rims tt kk (f1:real^N->real^3))` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `l:real^1->real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`]
    MOI_S4T_TRI_SECTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->complex` (X_CHOOSE_THEN `pp:real^N->real^3->real^1`
    (X_CHOOSE_THEN `kc:real^N->real` (X_CHOOSE_THEN `sg:real^N->real^N->real`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`; `l:real^1->real^3`; `phi:real^3->complex`;
                 `pp:real^N->real^3->real^1`; `kc:real^N->real`;
                 `sg:real^N->real^N->real`] MOI_S4T_COMP_WINDING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_COUNT_ARITH) THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `phi:real^3->complex`; `l:real^1->real^3`]
    MOI_S4T_CONTRACTIBLE_WINDING) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(phi:real^3->complex) x IN sphere(vec 0,&1)` MP_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!a b. (x:real^3) IN a /\ a SUBSET b /\
                                     IMAGE (f:real^3->complex) b SUBSET c ==> f x IN c`) THEN
        MAP_EVERY EXISTS_TAC [`d:real^3->bool`;
                              `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`] THEN
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        DISCH_TAC THEN DISCH_TAC THEN
        UNDISCH_TAC `(phi:real^3->complex) x IN sphere(vec 0,&1)` THEN
        ASM_REWRITE_TAC[IN_SPHERE_0; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC SIMPLE_PATH_IMP_PATH THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `CARD (j INTER moi_s34_rims tt kk (f1:real^N->real^3)) = 0` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  UNDISCH_TAC `2 <= CARD (j INTER moi_s34_rims tt kk (f1:real^N->real^3))` THEN
  ARITH_TAC);;

(* Lemma 11: a trace component meets each splitting disk of s in one point. *)
(* A trace point in two vertex balls is a rim point. *)
let MOI_S4T_TRI_MEET_RIMS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 u w q.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     u IN {v1,v2,v3} /\ w IN {v1,v2,v3} /\ ~(u = w) /\
     q IN moi_s34_trace tt kk f1 (cb s) /\
     q IN IMAGE f1 (moi_s34_vb tt kk u) /\ q IN IMAGE f1 (moi_s34_vb tt kk w)
     ==> q IN moi_s34_rims tt kk f1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_BALLS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_TRACE) THEN
  SUBGOAL_THEN `?x:real^N. x IN {v1,v2,v3} /\
                (q:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3)
                   ((cb:(real^N->bool)->real^3->bool) s)` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `moi_s34_trace tt kk (f1:real^N->real^3)
                         ((cb:(real^N->bool)->real^3->bool) s)`)) THEN
    REWRITE_TAC[IN_INTER; IN_UNION] THEN
    MESON_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x)` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk x INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `x:real^N = u` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                   `u:real^N`; `w:real^N`] MOI_S4T_TRI_PAIR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!a. (q:real^3) IN a /\ a SUBSET b ==> q IN b`) THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`)) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  ASM_CASES_TAC `x:real^N = w` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                   `w:real^N`; `u:real^N`] MOI_S4T_TRI_PAIR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!a. (q:real^3) IN a /\ a SUBSET b ==> q IN b`) THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk w INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk w INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`)) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `u:real^N`; `w:real^N`] MOI_S4T_TRI_PAIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `x:real^N` o last o CONJUNCTS)] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `!P. (q:real^3) IN a /\ q IN b /\ q IN c
                            ==> a INTER b INTER c = {} ==> P`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4T_COMP_EDGE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j g.
     MOISE_288_STATEMENT /\
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     (!s v j. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
              j IN components (moi_s34_trace tt kk f1 (cb s))
              ==> ~(j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))) /\
     (!s v g a aa. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\ g IN moi_s34_simp kk (&1) /\
                   pl_cell_with_boundary 1 a aa /\
                   a SUBSET moi_s34_trace tt kk f1 (cb s) /\
                   a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                   aa SUBSET IMAGE f1 (moi_s34_sd tt kk g) /\
                   a INTER moi_s34_rims tt kk f1 = aa
                   ==> F) /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET s
     ==> ?p. j INTER IMAGE f1 (moi_s34_sd tt kk g) = {p}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`] MOI_S4T_COMP_THREE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`] MOI_S4T_COMP_RIMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`] MOI_S4T_COMP_LOOP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `CARD (j INTER moi_s34_rims tt kk (f1:real^N->real^3)) = 3` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `l:real^1->real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`l:real^1->real^3`; `j INTER moi_s34_rims tt kk (f1:real^N->real^3)`]
    MOI_S4T_TIMES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
    REWRITE_TAC[IN_INTER; PATHSTART_IN_PATH_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INTER_SUBSET];
    STRIP_TAC] THEN
  MP_TAC(ISPEC `{t | &0 <= t /\ t <= &1 /\
                     (l:real^1->real^3)(lift t) IN j INTER moi_s34_rims tt kk
                     (f1:real^N->real^3)}` MOI_S4T_FOUR_TIMES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [SIMP_TAC[IN_ELIM_THM]; ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC)) THEN
  (* the three gaps and their vertex data *)
  MAP_EVERY (fun (x,y,(a,b,c)) ->
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                   `j:real^3->bool`; `l:real^1->real^3`; x; y] MOI_S4T_GAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN a (X_CHOOSE_THEN b (X_CHOOSE_THEN c STRIP_ASSUME_TAC))))
   [`&0`, `r1:real`, (`a0:real^N`, `b0:real^N`, `c0:real^N`);
    `r1:real`, `r2:real`, (`a1:real^N`, `b1:real^N`, `c1:real^N`);
    `r2:real`, `&1`, (`a2:real^N`, `b2:real^N`, `c2:real^N`)] THEN
  SUBGOAL_THEN `(l:real^1->real^3)(lift(&1)) = l(lift(&0))` ASSUME_TAC THENL
   [UNDISCH_TAC `pathfinish (l:real^1->real^3) = pathstart l` THEN
    REWRITE_TAC[pathstart; pathfinish; LIFT_NUM];
    ALL_TAC] THEN
  ABBREV_TAC `ee = \q. {x | x IN {v1:real^N,v2,v3} /\
                            q IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x)}` THEN
  SUBGOAL_THEN
   `!q u w. u IN {v1,v2,v3} /\ w IN {v1,v2,v3} /\ ~(u:real^N = w) /\
            q IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) /\
            q IN IMAGE f1 (moi_s34_vb tt kk w)
            ==> ee q = {u,w}`
  (LABEL_TAC "ee") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ee" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4T_EDGE_SET THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
      `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
      `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the edge sets of the three rim points *)
  SUBGOAL_THEN
   `ee ((l:real^1->real^3)(lift(&0))) = {a0:real^N,b0} /\ ee (l(lift(&0))) = {a2,c2} /\
    ee (l(lift r1)) = {a0,c0} /\ ee (l(lift r1)) = {a1,b1} /\
    ee (l(lift r2)) = {a1,c1} /\ ee (l(lift r2)) = {a2,b2}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "ee" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `(l:real^1->real^3)(lift(&1))`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a0:real^N,c0} = {a1,b1} /\ {a0:real^N,b0} = {a2,c2} /\
                {a1:real^N,c1} = {a2,b2}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r1)) = {a1,b1}`;
      UNDISCH_TAC `(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift(&0))) = {a2,c2}`;
      UNDISCH_TAC `(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r2)) = {a2,b2}`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b c:real^N. ~(a = b) /\ ~(a = c) /\ ~(b = c) ==> ~({a,b} = {a,c})`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(b:real^N) IN {a,c}` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INSERT];
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~({a0:real^N,b0} = {a0,c0}) /\ ~({a0:real^N,c0} = {a1,c1}) /\
                ~({a0:real^N,b0} = {a1,c1})` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ALL_TAC;
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `{a0:real^N,c0}`));
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `{a0:real^N,b0}`)) THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `{a1:real^N,c1}`))] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the edge g *)
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4t_tri] o
    check (moi_s4l_has "moi_s4t_tri")) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u:real^N) IN {v1,v2,v3} /\ (w:real^N) IN {v1,v2,v3}` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> is_eq(concl th) && rand(concl th) = `{v1:real^N,v2,v3}`)) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(g:real^N->bool) SUBSET s` THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `u:real^N`; `w:real^N`] MOI_S4T_TRI_PAIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `IMAGE (f1:real^N->real^3)
                        (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w)`)) THEN
  (* the points of j on D_uw are among the three rim points *)
  SUBGOAL_THEN
   `!q. q IN j /\ q IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) /\
        q IN IMAGE f1 (moi_s34_vb tt kk w)
        ==> (q = (l:real^1->real^3)(lift(&0)) \/ q = l(lift r1) \/ q = l(lift r2)) /\
            ee q = {u,w}`
  (LABEL_TAC "pts") THENL
   [GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ALL_TAC; USE_THEN "ee" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `(q:real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4T_TRI_MEET_RIMS THEN
      MAP_EVERY EXISTS_TAC [
        `h:real^N->real^3`; `ep:real^N->real`; `car:(real^N->bool)->real^3->bool`;
        `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v1:real^N`; `v2:real^N`;
        `v3:real^N`; `u:real^N`; `w:real^N`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!a. (q:real^3) IN a /\ a SUBSET b ==> q IN b`) THEN
      EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `(q:real^3) IN j`)) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
    REWRITE_TAC[path_image; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `drop t IN {t | &0 <= t /\ t <= &1 /\
                   (l:real^1->real^3)(lift t) IN j INTER moi_s34_rims tt kk
                   (f1:real^N->real^3)}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; IN_INTER] THEN
      UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `q:real^3`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `{&0,r1,r2,&1}`)) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (fun th ->
      SUBST_ALL_TAC(REWRITE_RULE[LIFT_DROP] (AP_TERM `lift` th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* which of the three it is *)
  MP_TAC(ISPECL [`v1:real^N`; `v2:real^N`; `v3:real^N`; `{a0:real^N,b0}`; `{a0:real^N,c0}`;
                 `{a1:real^N,c1}`] MOI_S4T_THREE_PAIRS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S4T_PAIR_CASES THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `{u:real^N,w}`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC MOI_S4T_PAIR_CASES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. (x = (l:real^1->real^3)(lift(&0)) \/ x = l(lift r1) \/ x = l(lift r2)) /\
          (y = l(lift(&0)) \/ y = l(lift r1) \/ y = l(lift r2)) /\
          (ee:real^3->real^N->bool) x = ee y ==> x = y`
  (LABEL_TAC "inj") THENL
   [MAP_EVERY UNDISCH_TAC
     [`(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift(&0))) = {a0,b0}`;
      `(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r1)) = {a0,c0}`;
      `(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r2)) = {a1,c1}`;
      `~({a0:real^N,b0} = {a0,c0})`; `~({a0:real^N,c0} = {a1,c1})`;
      `~({a0:real^N,b0} = {a1,c1})`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`{a0:real^N,b0}`, `e0:real^N->bool`; `{a0:real^N,c0}`, `e1:real^N->bool`;
      `{a1:real^N,c1}`, `e2:real^N->bool`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. (p = (l:real^1->real^3)(lift(&0)) \/ p = l(lift r1) \/ p = l(lift r2)) /\
        (ee:real^3->real^N->bool) p = {u,w}
        ==> ?p'. j INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) INTER
                 IMAGE f1 (moi_s34_vb tt kk w) = {p'}`
  (LABEL_TAC "fin") THENL
   [GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    EXISTS_TAC `p:real^3` THEN
    SUBGOAL_THEN `(p:real^3) IN j /\ p IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) /\
                  p IN IMAGE f1 (moi_s34_vb tt kk w)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
        REWRITE_TAC[path_image] THEN
        FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
          is_disj(concl th) && vfree_in `p:real^3` (concl th))) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(ee:real^3->real^N->bool) p = {u,w}` THEN EXPAND_TAC "ee" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_SING] THEN X_GEN_TAC `q:real^3` THEN
    EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
    STRIP_TAC THEN USE_THEN "pts" (MP_TAC o SPEC `q:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  USE_THEN "fin" MATCH_MP_TAC THENL
   [EXISTS_TAC `(l:real^1->real^3)(lift(&0))`;
    EXISTS_TAC `(l:real^1->real^3)(lift r1)`;
    EXISTS_TAC `(l:real^1->real^3)(lift r2)`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The trace is nonempty and inside the face torus; the theorem TRACE.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S4T_TRACE_NONEMPTY = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3
     ==> ~(moi_s34_trace tt kk f1 (cb s) = {}) /\
         moi_s34_trace tt kk f1 (cb s) SUBSET IMAGE f1 (moi_s34_ft tt kk s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_BALLS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_TRACE) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `moi_s34_trace tt kk (f1:real^N->real^3)
                       ((cb:(real^N->bool)->real^3->bool) s)`)) THEN
  SUBGOAL_THEN `closed (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`]
    MOI_S4T_TRI_SECTOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->complex` (X_CHOOSE_THEN `pp:real^N->real^3->real^1`
    (X_CHOOSE_THEN `kc:real^N->real` (X_CHOOSE_THEN `sg:real^N->real^N->real`
      STRIP_ASSUME_TAC)))) THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`{}:real^3->bool`; `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`;
                   `phi:real^3->complex`; `g:real^1->real^3`] MOI_S4L_CARRIES_H1_KILL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[EMPTY_SUBSET; NOT_IN_EMPTY] THEN
      UNDISCH_TAC `carries_h1 (moi_s34_trace tt kk (f1:real^N->real^3)
                     ((cb:(real^N->bool)->real^3->bool) s))
                   (IMAGE f1 (moi_s34_ft tt kk s))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `(phi:real^3->complex) o (g:real^1->real^3)` MOI_FH1_CIRCLE_CLASS_ZERO) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (phi:real^3->complex) (IMAGE (f1:real^N->real^3)
                     (moi_s34_ft tt kk s))` THEN
        ASM_SIMP_TAC[IMAGE_SUBSET]];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[COMPLEX_VEC_0] THEN
    REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED]]);;

(* The main theorem TRACE: Lemma 11 of Sec 34 (p.244), with 28.8 in the used form. *)
let TRACE = prove
 (MOI_S34_TRACE,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s34_l910] o
    check (moi_s4l_has "moi_s34_l910")) THEN
  REWRITE_TAC[moi_s34_traced] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4T_TRI_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N` (X_CHOOSE_THEN `v2:real^N`
    (X_CHOOSE_TAC `v3:real^N`))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`]
    MOI_S4T_TRACE_NONEMPTY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`]
    MOI_S4T_TRI_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:real^3->bool` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4T_COMP_EDGE THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
    `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
    `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`] THEN
  ASM_REWRITE_TAC[]);;

