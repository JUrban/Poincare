(* ========================================================================= *)
(* pc_sch_surg: the surgery construction SCH5_SURG_CONSTRUCT, which derives  *)
(* SCH_SURG_CONSTRUCT_STATEMENT from the three statements about regular      *)
(* levels. The bottom surgered sphere comes from pc_sch_surgb; the top one   *)
(* is the bottom construction for the reflected data (x3 -> -x3), reflected  *)
(* back. The parameter sphere splits into the bottom disc, the band of the   *)
(* pancake chart and the top disc (clopen argument on the connected sphere), *)
(* which gives the slab configuration, the saddle count and the level        *)
(* components.                                                               *)
(* ========================================================================= *)

needs "src/pc_sch_surgb.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Reflection of the pancake data.                                           *)
(* ------------------------------------------------------------------------- *)

let SCH5S_FLIP3_FACTS = prove
 (`(!x:real^3. sch_flip3(sch_flip3 x) = x) /\ linear sch_flip3 /\
   (!x:real^3. (sch_flip3 x)$1 = x$1 /\ (sch_flip3 x)$2 = x$2 /\ (sch_flip3 x)$3 = --(x$3)) /\
   (!y:real^3. sch5v_pr(sch_flip3 y) = sch5v_pr y)`,
  SUBGOAL_THEN `!x:real^3. (sch_flip3 x)$1 = x$1 /\ (sch_flip3 x)$2 = x$2 /\
                           (sch_flip3 x)$3 = --(x$3)` ASSUME_TAC THENL
   [REWRITE_TAC[sch_flip3; VECTOR_3]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN ASM_REWRITE_TAC[REAL_NEG_NEG];
    REWRITE_TAC[linear; sch_flip3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[sch5v_pr; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REWRITE_TAC[]]);;

(* Membership iffs; never put these into the assumptions (they loop under rewriting). *)

let SCH5S_FLIP3_SETS = prove
 (`(!x:real^3. sch_flip3 x IN sphere(vec 0,&1) <=> x IN sphere(vec 0,&1)) /\
   (!y:real^3 H. sch_flip3 y IN sch5v_slab H <=> y IN sch5v_slab H) /\
   (!y:real^3. (sch_flip3 y)$1 pow 2 + (sch_flip3 y)$2 pow 2 = y$1 pow 2 + y$2 pow 2)`,
  REWRITE_TAC[sch_flip3; IN_SPHERE_0; NORM_EQ_1; DOT_3; VECTOR_3; sch5v_slab; IN_ELIM_THM;
              REAL_ABS_NEG] THEN
  REAL_ARITH_TAC);;

let SCH5S_FLIP_DIFFEO = prove
 (`!s:real^3->bool. open s ==> diffeomorphism_on s (IMAGE sch_flip3 s) sch_flip3 sch_flip3`,
  REPEAT STRIP_TAC THEN MP_TAC SCH5S_FLIP3_FACTS THEN STRIP_TAC THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t:real^3->bool. smooth_map_on t sch_flip3` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    SUBGOAL_THEN `sch_flip3 = sch_flip3 o (\x:real^3. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`sch_flip3`; `s:real^3->bool`] OPEN_BIJECTIVE_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [REPEAT STRIP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]);;

let SCH5S_FLIP_IN_IMAGE = prove
 (`!s (x:real^3). sch_flip3 x IN IMAGE sch_flip3 s <=> x IN s`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[SCH_FLIP3_INVOLUTION]);;


let SCH5S_PANCAKE_FLIP = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch5b_pancake g g' a lam c c' Theta Theta'
     ==> sch5b_pancake (sch_flip3 o g o sch_flip3) (sch_flip3 o g' o sch_flip3) (--a) lam c c'
                       (sch_flip3 o Theta o sch_flip3) (sch_flip3 o Theta' o sch_flip3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5b_pancake] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "HT") (CONJUNCTS_THEN2 (LABEL_TAC "PF") (LABEL_TAC "SC"))))))) THEN
  MP_TAC SCH5S_FLIP3_FACTS THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SCH5_NECK_FLIP] THEN
  SUBGOAL_THEN `IMAGE sch_flip3 (sch5v_slab(&3 / &2)) = sch5v_slab(&3 / &2)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_IMAGE] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[SCH5S_FLIP3_SETS];
      DISCH_TAC THEN EXISTS_TAC `sch_flip3 y` THEN ASM_REWRITE_TAC[SCH5S_FLIP3_SETS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(sch5v_slab(&3 / &2)) /\
                open(IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2)))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (sch5v_slab(&3 / &2))
                   (IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))) Theta Theta'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `sch5v_slab(&3 / &2)` SCH5S_FLIP_DIFFEO) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))` SCH5S_FLIP_DIFFEO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`sch5v_slab(&3 / &2)`; `sch5v_slab(&3 / &2)`;
                   `IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))`; `sch_flip3`; `sch_flip3`;
                   `Theta:real^3->real^3`; `Theta':real^3->real^3`] DIFFEOMORPHISM_ON_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`sch5v_slab(&3 / &2)`; `IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))`;
                   `IMAGE sch_flip3 (IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2)))`;
                   `(Theta:real^3->real^3) o sch_flip3`; `sch_flip3 o (Theta':real^3->real^3)`;
                   `sch_flip3`; `sch_flip3`] DIFFEOMORPHISM_ON_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (sch_flip3 o (Theta:real^3->real^3) o sch_flip3) (sch5v_slab(&3 / &2)) =
                  IMAGE sch_flip3 (IMAGE Theta (sch5v_slab(&3 / &2)))` SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[o_ASSOC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "HT" (fun th -> REWRITE_TAC[MATCH_MP th (EQ_MP (SYM(SPECL [`y:real^3`; `&3 / &2`]
      (CONJUNCT1(CONJUNCT2 SCH5S_FLIP3_SETS))))
      (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`))]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `sch_flip3 (y:real^3) IN sch5v_slab(&3 / &2) /\
                  (sch_flip3 y)$1 pow 2 + (sch_flip3 y)$2 pow 2 < &1 / &4` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SCH5S_FLIP3_SETS]; ALL_TAC] THEN
    USE_THEN "PF" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `sch_flip3 (y:real^3) IN sch5v_slab(&3 / &2) /\
       (sch_flip3 y)$1 pow 2 + (sch_flip3 y)$2 pow 2 < &1 / &4`)]) THEN
    ASM_REWRITE_TAC[sch5v_at; sch_flip3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[SCH5_IMAGE_FLIP_NECK; o_THM] THEN
    REWRITE_TAC[SCH5S_FLIP_IN_IMAGE] THEN
    USE_THEN "SC" (fun th -> REWRITE_TAC[MATCH_MP th (EQ_MP (SYM(SPECL [`y:real^3`; `&3 / &2`]
      (CONJUNCT1(CONJUNCT2 SCH5S_FLIP3_SETS))))
      (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`))]) THEN
    REWRITE_TAC[CONJUNCT2(CONJUNCT2 SCH5S_FLIP3_SETS)]]);;

(* ------------------------------------------------------------------------- *)
(* The top surgered sphere, by the bottom construction for the               *)
(* reflected data (x3 -> -x3, level -a), reflected back.                     *)
(* ------------------------------------------------------------------------- *)

let SCH5S_IMAGE_FLIP_INJ = prove
 (`!s t:real^3->bool. IMAGE sch_flip3 s = IMAGE sch_flip3 t <=> s = t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\u:real^3->bool. sch_flip3 x IN u`) THEN
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[SCH_FLIP3_INVOLUTION]);;


let SCH5S_FLIP_IMAGE_FACTS = prove
 (`(!s:real^3->bool. IMAGE sch_flip3 (IMAGE sch_flip3 s) = s) /\
   (!(f:real^3->real^3) s.
      IMAGE sch_flip3 (IMAGE (sch_flip3 o f o sch_flip3) s) = IMAGE f (IMAGE sch_flip3 s)) /\
   (!s t:real^3->bool. IMAGE sch_flip3 (s INTER t) = IMAGE sch_flip3 s INTER IMAGE sch_flip3 t) /\
   (!s:real^3->bool. FINITE s ==> CARD(IMAGE sch_flip3 s) = CARD s) /\
   (!lo hi. IMAGE sch_flip3 (sch5b_band lo hi) = sch5b_band (--hi) (--lo)) /\
   IMAGE sch_flip3 sch_cap1 = sch_cap2 /\
   IMAGE sch_flip3 (sphere(vec 0,&1)) = sphere(vec 0,&1) /\
   (!s:real^3->bool. compact s ==> compact(IMAGE sch_flip3 s)) /\
   (!s:real^3->bool. connected s ==> connected(IMAGE sch_flip3 s)) /\
   (!s:real^3->bool. open s ==> open(IMAGE sch_flip3 s))`,
  MP_TAC SCH5S_FLIP3_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y:real^3. sch_flip3 x = sch_flip3 y ==> x = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. IMAGE sch_flip3 (IMAGE sch_flip3 s) = s` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN MATCH_MP_TAC IMAGE_INTER_INJ THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_IMAGE; sch5b_band; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN EXISTS_TAC `sch_flip3 y` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_IMAGE] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[SCH_FLIP3_CAP];
      DISCH_TAC THEN EXISTS_TAC `sch_flip3 y` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[GSYM SCH_FLIP3_CAP] THEN ASM_REWRITE_TAC[]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_IMAGE] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[SCH5S_FLIP3_SETS];
      DISCH_TAC THEN EXISTS_TAC `sch_flip3 y` THEN ASM_REWRITE_TAC[SCH5S_FLIP3_SETS]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_LINEAR_IMAGE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`sch_flip3`; `s:real^3->bool`] OPEN_BIJECTIVE_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]]);;

let SCH5S_IN_IMAGE_FLIP = prove
 (`!s (x:real^3). x IN IMAGE sch_flip3 s <=> sch_flip3 x IN s`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[SCH_FLIP3_INVOLUTION]);;

(* Critical points in image form transfer through the reflection.           *)

let SCH5S_FLIP_CRITS = prove
 (`!(g:real^3->real^3) g' (g1:real^3->real^3) g1' (Theta:real^3->real^3) (D0:real^3->bool).
     sch_neck g g' /\ sch_neck g1 g1' /\
     IMAGE g1 (sch_saddles g1) =
     IMAGE (sch_flip3 o g o sch_flip3) (sch_saddles (sch_flip3 o g o sch_flip3) INTER D0) /\
     (!t. sch_crit g1 t
          ==> t = basis 3 /\
              g1 t = (sch_flip3 o Theta o sch_flip3) (vector[&0; &0; --(&1 / &2)]) \/
              (?u. u IN D0 /\ sch_crit (sch_flip3 o g o sch_flip3) u /\
                   g1 t = (sch_flip3 o g o sch_flip3) u)) /\
     (!u. u IN D0 /\ sch_crit (sch_flip3 o g o sch_flip3) u
          ==> ?t. sch_crit g1 t /\ g1 t = (sch_flip3 o g o sch_flip3) u)
     ==> IMAGE (sch_flip3 o g1 o sch_flip3) (sch_saddles (sch_flip3 o g1 o sch_flip3)) =
         IMAGE g (sch_saddles g INTER IMAGE sch_flip3 D0) /\
         (!t. sch_crit (sch_flip3 o g1 o sch_flip3) t
              ==> t = --(basis 3) /\
                  (sch_flip3 o g1 o sch_flip3) t = Theta(vector[&0; &0; &1 / &2]) \/
                  (?u. u IN IMAGE sch_flip3 D0 /\ sch_crit g u /\
                       (sch_flip3 o g1 o sch_flip3) t = g u)) /\
         (!u. u IN IMAGE sch_flip3 D0 /\ sch_crit g u
              ==> ?t. sch_crit (sch_flip3 o g1 o sch_flip3) t /\
                      (sch_flip3 o g1 o sch_flip3) t = g u)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "IMS") (CONJUNCTS_THEN2 (LABEL_TAC "CR1") (LABEL_TAC "CR2"))))) THEN
  MP_TAC SCH5S_FLIP_IMAGE_FACTS THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "II") (CONJUNCTS_THEN2 (LABEL_TAC "IC")
    (CONJUNCTS_THEN2 (LABEL_TAC "IN") (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCH5_SADDLES_FLIP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!t:real^3. sch_crit (sch_flip3 o g o sch_flip3) t <=> sch_crit g (sch_flip3 t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`]
      SCH5_CRIT_FLIP) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^3. sch_crit (sch_flip3 o g1 o sch_flip3) t <=> sch_crit g1 (sch_flip3 t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`g1:real^3->real^3`; `g1':real^3->real^3`; `t:real^3`]
      SCH5_CRIT_FLIP) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`g1:real^3->real^3`; `g1':real^3->real^3`] SCH5_SADDLES_FLIP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN
    SUBGOAL_THEN `((sch_flip3 o (g1:real^3->real^3) o sch_flip3) o sch_flip3) = sch_flip3 o g1`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; SCH_FLIP3_INVOLUTION]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN USE_THEN "IMS" SUBST1_TAC THEN
    USE_THEN "IC" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "IN" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "II" (fun th -> REWRITE_TAC[th]);
    X_GEN_TAC `t:real^3` THEN ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
    USE_THEN "CR1" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `sch_crit (g1:real^3->real^3) (sch_flip3 t)`))) THEN
    REWRITE_TAC[o_THM] THEN STRIP_TAC THENL
     [DISJ1_TAC THEN
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
        lhand(concl th) = `(g1:real^3->real^3)(sch_flip3 t)` then SUBST1_TAC th
        else failwith "not") THEN
      REWRITE_TAC[SCH_FLIP3_INVOLUTION] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o AP_TERM `sch_flip3` o check (fun th ->
          concl th = `sch_flip3 t = basis 3`)) THEN
        REWRITE_TAC[SCH_FLIP3_INVOLUTION] THEN DISCH_THEN SUBST1_TAC THEN
        SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; sch_flip3; VECTOR_3; VECTOR_NEG_COMPONENT;
                 BASIS_COMPONENT; ARITH] THEN
        REAL_ARITH_TAC;
        AP_TERM_TAC THEN REWRITE_TAC[sch_flip3; VECTOR_3; REAL_NEG_NEG]];
      DISJ2_TAC THEN EXISTS_TAC `sch_flip3 u` THEN
      CONJ_TAC THENL [REWRITE_TAC[SCH5S_FLIP_IN_IMAGE] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `sch_crit (sch_flip3 o (g:real^3->real^3) o sch_flip3) u` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
        lhand(concl th) = `(g1:real^3->real^3)(sch_flip3 t)` then SUBST1_TAC th
        else failwith "not") THEN
      REWRITE_TAC[SCH_FLIP3_INVOLUTION]];
    X_GEN_TAC `u:real^3` THEN REWRITE_TAC[SCH5S_IN_IMAGE_FLIP] THEN STRIP_TAC THEN
    SUBGOAL_THEN `sch_crit (sch_flip3 o (g:real^3->real^3) o sch_flip3) (sch_flip3 u)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[SCH_FLIP3_INVOLUTION]; ALL_TAC] THEN
    USE_THEN "CR2" (fun th -> MP_TAC(MATCH_MP th (CONJ
      (ASSUME `sch_flip3 u IN (D0:real^3->bool)`)
      (ASSUME `sch_crit (sch_flip3 o (g:real^3->real^3) o sch_flip3) (sch_flip3 u)`)))) THEN
    REWRITE_TAC[o_THM; SCH_FLIP3_INVOLUTION] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sch_flip3 s` THEN ASM_REWRITE_TAC[o_THM; SCH_FLIP3_INVOLUTION]]);;

let SCH5S_TOP = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch5b_pancake g g' a lam c c' Theta Theta' /\ sch_morse g /\
     (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     (!t. sch_crit g t ==> ~((g t)$3 = a + lam / &2))
     ==> ?g2 g2' e2 D D0.
           sch_neck g2 g2' /\ sch_morse g2 /\ (!t. sch_crit g2 t ==> ~((g2 t)$3 = a)) /\
           &0 < e2 /\ e2 <= &1 / &16 /\
           (!x. x IN sch_capcone ==> g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e2 x))) /\
           D SUBSET sphere(vec 0,&1) /\ D0 SUBSET D /\
           (?U. open U /\ D0 = sphere(vec 0,&1) INTER U) /\ compact D /\ connected D /\
           (!y. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1 /\ --(&4 / &3) < y$3
                ==> (g'(Theta y) IN D <=> &9 / &8 <= y$3) /\
                    (g'(Theta y) IN D0 <=> &9 / &8 < y$3)) /\
           (!x. x IN D /\ ~(x IN D0) ==> ?y. y IN sch5b_circ(&9 / &8) /\ x = g'(Theta y)) /\
           IMAGE g2 (sphere(vec 0,&1)) =
           (IMAGE g D UNION IMAGE Theta (sch5b_band (&1) (&9 / &8))) UNION
           IMAGE Theta sch_cap2 /\
           CARD(sch_saddles g2) = CARD(sch_saddles g INTER D0) /\
           (!u. u IN sch_saddles g INTER D0 ==> ?t. t IN sch_saddles g2 /\ g2 t = g u) /\
           sch_level g2 a = {x | x IN IMAGE g D0 /\ x$3 = a} /\
           IMAGE g2 (sch_saddles g2) = IMAGE g (sch_saddles g INTER D0) /\
           (!t. sch_crit g2 t
                ==> t = --(basis 3) /\ g2 t = Theta(vector[&0; &0; &1 / &2]) \/
                    (?u. u IN D0 /\ sch_crit g u /\ g2 t = g u)) /\
           (!u. u IN D0 /\ sch_crit g u ==> ?t. sch_crit g2 t /\ g2 t = g u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch_neck (g:real^3->real^3) g'` ASSUME_TAC THENL
   [ASM_MESON_TAC[sch5b_pancake]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sch_flip3 o (g:real^3->real^3) o sch_flip3`; `sch_flip3 o (g':real^3->real^3) o sch_flip3`;
                 `--a:real`; `lam:real`; `c:real^2->real^2`; `c':real^2->real^2`;
                 `sch_flip3 o (Theta:real^3->real^3) o sch_flip3`;
                 `sch_flip3 o (Theta':real^3->real^3) o sch_flip3`] SCH5B_BOTTOM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SCH5S_PANCAKE_FLIP] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCH5_MORSE_FLIP THEN EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCH5_CRIT_FLIP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th; o_THM]) THEN
    MP_TAC SCH5S_FLIP3_FACTS THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC `t:real^3` THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `sch_flip3 t` o check (fun th -> can (term_match [`a:real`]
        `!t:real^3. sch_crit g t ==> ~((g t)$3 = a)`) (concl th)));
      FIRST_X_ASSUM(MP_TAC o SPEC `sch_flip3 t` o check (fun th -> can (term_match [`a:real`; `lam:real`]
        `!t:real^3. sch_crit g t ==> ~((g t)$3 = a + lam / &2)`) (concl th)))] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[o_THM; SCH_FLIP3_INVOLUTION] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `D:real^3->bool` (X_CHOOSE_THEN `D0:real^3->bool`
    MP_TAC))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "BCH") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "BCAP")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "BU") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "BBAND")
    (CONJUNCTS_THEN2 (LABEL_TAC "BBDY") (CONJUNCTS_THEN2 (LABEL_TAC "BIM")
    (CONJUNCTS_THEN2 (LABEL_TAC "BCARD") (CONJUNCTS_THEN2 (LABEL_TAC "BSAD")
    (CONJUNCTS_THEN2 (LABEL_TAC "BLEV") (CONJUNCTS_THEN2 (LABEL_TAC "BIMS")
    (CONJUNCTS_THEN2 (LABEL_TAC "BCR1") (LABEL_TAC "BCR2")))))))))))))))))))) THEN
  MAP_EVERY EXISTS_TAC [`sch_flip3 o (g1:real^3->real^3) o sch_flip3`;
                        `sch_flip3 o (g1':real^3->real^3) o sch_flip3`; `e1:real`;
                        `IMAGE sch_flip3 D`; `IMAGE sch_flip3 D0`] THEN
  MP_TAC SCH5S_FLIP_IMAGE_FACTS THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "II") (CONJUNCTS_THEN2 (LABEL_TAC "IC")
    (CONJUNCTS_THEN2 (LABEL_TAC "IN") (CONJUNCTS_THEN2 (LABEL_TAC "CA")
    (CONJUNCTS_THEN2 (LABEL_TAC "BA") (CONJUNCTS_THEN2 (LABEL_TAC "CP")
    (CONJUNCTS_THEN2 (LABEL_TAC "SP") (CONJUNCTS_THEN2 (LABEL_TAC "CO")
    (CONJUNCTS_THEN2 (LABEL_TAC "CN") (LABEL_TAC "OP")))))))))) THEN
  SUBGOAL_THEN `!x:real^3. sch_flip3 x IN IMAGE sch_flip3 D0 <=> x IN D0` (LABEL_TAC "F0") THENL
   [REWRITE_TAC[SCH5S_FLIP_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. sch_flip3 x IN IMAGE sch_flip3 D <=> x IN D` (LABEL_TAC "F1") THENL
   [REWRITE_TAC[SCH5S_FLIP_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `g1:real^3->real^3`;
                 `g1':real^3->real^3`; `Theta:real^3->real^3`; `D0:real^3->bool`]
    SCH5S_FLIP_CRITS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_THM; SCH_FLIP3_INVOLUTION] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "TIMS")
      (CONJUNCTS_THEN2 (LABEL_TAC "TCR1") (LABEL_TAC "TCR2")))] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCH5_NECK_FLIP THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCH5_MORSE_FLIP THEN EXISTS_TAC `g1':real^3->real^3` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`g1:real^3->real^3`; `g1':real^3->real^3`] SCH5_CRIT_FLIP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th; o_THM]) THEN
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "BCH" (fun th -> MP_TAC(MP (SPEC `sch_flip3 t` th)
      (ASSUME `sch_crit (g1:real^3->real^3) (sch_flip3 t)`))) THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 SCH5S_FLIP3_FACTS))] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM; SCH_FLIP3_INVOLUTION] THEN
    USE_THEN "BCAP" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN sch_capcone`)]) THEN
    REWRITE_TAC[SCH_FLIP3_INVOLUTION];
    USE_THEN "SP" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    USE_THEN "BU" (X_CHOOSE_THEN `U:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE sch_flip3 U` THEN USE_THEN "OP" (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "IN" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "SP" (fun th -> REWRITE_TAC[th]);
    USE_THEN "CO" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "CN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    USE_THEN "BBAND" (MP_TAC o SPEC `sch_flip3 y`) THEN
    REWRITE_TAC[SCH_FLIP3_INVOLUTION; SCH5S_FLIP3_SETS] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[sch_flip3; VECTOR_3] THEN
      UNDISCH_TAC `--(&4 / &3) < (y:real^3)$3` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SCH5S_IN_IMAGE_FLIP] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[sch_flip3; VECTOR_3] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[SCH5S_IN_IMAGE_FLIP] THEN STRIP_TAC THEN
    USE_THEN "BBDY" (fun th -> MP_TAC(MP (SPEC `sch_flip3 x` th)
      (CONJ (ASSUME `sch_flip3 x IN D`) (ASSUME `~(sch_flip3 x IN D0)`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sch_flip3 y` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN sch5b_circ(--(&9 / &8))` THEN
      REWRITE_TAC[sch5b_circ; IN_ELIM_THM; sch_flip3; VECTOR_3] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o AP_TERM `sch_flip3` o check (fun th -> is_eq(concl th) &&
        lhand(concl th) = `sch_flip3 x`)) THEN
      REWRITE_TAC[SCH_FLIP3_INVOLUTION]];
    REWRITE_TAC[SCH5_IMAGE_FLIP_NECK] THEN ASM_REWRITE_TAC[IMAGE_UNION] THEN
    USE_THEN "IC" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "BA" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "CP" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_NEG_NEG];
    MP_TAC(ISPECL [`g1:real^3->real^3`; `g1':real^3->real^3`] SCH5_SADDLES_FLIP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCH5_SADDLES_FLIP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(sch_saddles (g1:real^3->real^3)) /\ FINITE(sch_saddles (g:real^3->real^3))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THENL
       [EXISTS_TAC `{t | sch_crit (g1:real^3->real^3) t}`;
        EXISTS_TAC `{t | sch_crit (g:real^3->real^3) t}`] THEN
      REWRITE_TAC[sch_saddles; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[] THEN
      ASM_MESON_TAC[sch_morse];
      ALL_TAC] THEN
    USE_THEN "CA" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "BCARD" SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE sch_flip3 (sch_saddles (g:real^3->real^3)) INTER D0 =
                  IMAGE sch_flip3 (sch_saddles g INTER IMAGE sch_flip3 D0)` SUBST1_TAC THENL
     [USE_THEN "IN" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "II" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    USE_THEN "CA" MATCH_MP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `sch_saddles (g:real^3->real^3)` THEN ASM_REWRITE_TAC[INTER_SUBSET];
    X_GEN_TAC `u:real^3` THEN REWRITE_TAC[IN_INTER; SCH5S_IN_IMAGE_FLIP] THEN STRIP_TAC THEN
    SUBGOAL_THEN `sch_flip3 u IN sch_saddles (sch_flip3 o (g:real^3->real^3) o sch_flip3) INTER D0`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCH5_SADDLES_FLIP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[IN_INTER; SCH5S_FLIP_IN_IMAGE];
      ALL_TAC] THEN
    USE_THEN "BSAD" (fun th -> MP_TAC(MP (SPEC `sch_flip3 u` th)
      (ASSUME `sch_flip3 u IN sch_saddles (sch_flip3 o (g:real^3->real^3) o sch_flip3) INTER D0`))) THEN
    REWRITE_TAC[SCH_FLIP3_INVOLUTION] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sch_flip3 t` THEN
    MP_TAC(ISPECL [`g1:real^3->real^3`; `g1':real^3->real^3`] SCH5_SADDLES_FLIP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[SCH5S_FLIP_IN_IMAGE; o_THM; SCH_FLIP3_INVOLUTION];
    REWRITE_TAC[SCH5_LEVEL_FLIP] THEN ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[SCH5S_IN_IMAGE_FLIP; IN_ELIM_THM] THEN
    SUBGOAL_THEN `!w:real^3. w IN IMAGE (sch_flip3 o g o sch_flip3) D0 <=>
                             sch_flip3 w IN IMAGE g (IMAGE sch_flip3 D0)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN USE_THEN "IC" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[SCH5S_FLIP_IN_IMAGE];
      ALL_TAC] THEN
    REWRITE_TAC[SCH_FLIP3_INVOLUTION; sch_flip3; VECTOR_3; REAL_EQ_NEG2];
    USE_THEN "TIMS" ACCEPT_TAC;
    USE_THEN "TCR1" ACCEPT_TAC;
    USE_THEN "TCR2" ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A radial compression of a neck keeps the sphere, the Morse                *)
(* data and the values on the sphere, and turns the model collar e into e k; *)
(* this gives a common collar parameter for the two surgered spheres.        *)
(* ------------------------------------------------------------------------- *)

let SCH5S_SHRINK = prove
 (`!(g1:real^3->real^3) g1' k.
     sch_neck g1 g1' /\ &0 < k /\ k <= &1 / &4
     ==> sch_neck (g1 o sch5_radial k) (sch5_radinv k o g1') /\
         (!t. t IN sphere(vec 0,&1) ==> (g1 o sch5_radial k) t = g1 t) /\
         IMAGE (g1 o sch5_radial k) (sphere(vec 0,&1)) = IMAGE g1 (sphere(vec 0,&1)) /\
         (!t. sch_crit (g1 o sch5_radial k) t <=> sch_crit g1 t) /\
         sch_saddles (g1 o sch5_radial k) = sch_saddles g1 /\
         (sch_morse (g1 o sch5_radial k) <=> sch_morse g1) /\
         (!a. sch_level (g1 o sch5_radial k) a = sch_level g1 a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g1:real^3->real^3`; `g1':real^3->real^3`; `&2 * k`] SCH5_NECK_FROM_THIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SCH5_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^3->bool`;
                          `IMAGE (g1:real^3->real^3) (annulus (&1 / &2) (&2))`] THEN
    REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[sch_neck];
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(&2 * k) / &2 = k`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE ((g1:real^3->real^3) o sch5_radial k) (sphere(vec 0,&1)) =
                IMAGE g1 (sphere(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. sch_crit ((g1:real^3->real^3) o sch5_radial k) t <=> sch_crit g1 t`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[sch_crit] THEN
    ASM_CASES_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3`) THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sch_saddles ((g1:real^3->real^3) o sch5_radial k) = sch_saddles g1` ASSUME_TAC THENL
   [REWRITE_TAC[sch_saddles; EXTENSION; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^3` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `((g1:real^3->real^3) o sch5_radial k) t = g1 t` (fun th -> ASM_MESON_TAC[th]);
      SUBGOAL_THEN `((g1:real^3->real^3) o sch5_radial k) t = g1 t` (fun th -> ASM_MESON_TAC[th])] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[sch_crit];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sch_level] THEN
  REWRITE_TAC[sch_morse] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. sch_crit (g1:real^3->real^3) t ==> ((g1 o sch5_radial k) t = g1 t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[sch_crit]; ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let SCH5S_SHRINK_CAP = prove
 (`!(Theta:real^3->real^3) e k x.
     &0 < k /\ k <= &1 / &4 /\ x IN sch_capcone
     ==> sch5_radial k x IN sch_capcone /\
         sch_cap_collar e (sch5_radial k x) = sch_cap_collar (e * k) x /\
         sch5_radial k (sch_flip3 x) = sch_flip3(sch5_radial k x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[sch_capcone; IN_ELIM_THM] o
    check (fun th -> concl th = `(x:real^3) IN sch_capcone`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0) /\ &0 < norm x` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 / &2 < norm(vec 0:real^3)` THEN
      REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + k * (norm(x:real^3) - &1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `k * --(&1 / &2) <= k * (norm(x:real^3) - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:real`; `x:real^3`] SCH5_RADIAL_FACTS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 + k * (norm x - &1)) / norm(x:real^3)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[sch5_radial; NORM_MUL; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`] THEN
    ABBREV_TAC `l = (&1 + k * (norm x - &1)) / norm(x:real^3)` THEN
    SUBGOAL_THEN `&0 < l * ((x:real^3)$3 + &1 / &4 * norm x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `--(&1 / &4) * norm x < (x:real^3)$3` THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    MATCH_MP_TAC SCH5C_COLLAR_RADIAL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[sch5_radial] THEN
    SUBGOAL_THEN `norm(sch_flip3 x) = norm(x:real^3)` SUBST1_TAC THENL
     [REWRITE_TAC[vector_norm; DOT_3; sch_flip3; VECTOR_3] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC SCH5S_FLIP3_FACTS THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th])]);;

(* ------------------------------------------------------------------------- *)
(* The band of the pancake on the parameter sphere: its images               *)
(* are relatively open, its points are not critical (the height grows with   *)
(* speed lam along the band), and the sphere is the union of the bottom      *)
(* disc, the closed band and the top disc (clopen argument).                 *)
(* ------------------------------------------------------------------------- *)

(* A curve on the unit sphere moves orthogonally to its position. *)

let SCH5S_SPHERE_CURVE_ORTH = prove
 (`!(c:real^1->real^3) w s0 d.
     (c has_vector_derivative w) (at s0) /\ &0 < d /\
     (!s. dist(s,s0) < d ==> c s IN sphere(vec 0,&1))
     ==> orthogonal (c s0) w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x y:real^3. lift(x dot y)`; `c:real^1->real^3`; `c:real^1->real^3`;
                 `w:real^3`; `w:real^3`; `s0:real^1`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\s:real^1. lift((c:real^1->real^3) s dot c s)) has_vector_derivative vec 0)
                (at s0)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\s:real^1. lift(&1)` THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^1` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real^1. lift((c:real^1->real^3) s dot c s)`; `s0:real^1`;
                 `lift((c:real^1->real^3) s0 dot w) + lift(w dot c s0)`; `vec 0:real^1`]
    VECTOR_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_NUM; LIFT_EQ; orthogonal; DOT_SYM] THEN
  REAL_ARITH_TAC);;

let SCH5S_BAND_NOT_CRIT = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' y.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1
     ==> ~(sch_crit g (g'(Theta y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5B_BETA_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "B1") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_pancake] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_pancake" with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GN") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "TD")
    (CONJUNCTS_THEN2 (LABEL_TAC "HT") (K ALL_TAC)))))) THEN
  ABBREV_TAC `l = \s:real^1. (y:real^3) + drop s % basis 3` THEN
  SUBGOAL_THEN `(l:real^1->real^3)(vec 0) = y` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `((l:real^1->real^3) has_vector_derivative basis 3) (at (vec 0))` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[SCH5B_VD_LINE]; ALL_TAC] THEN
  ABBREV_TAC `d = &3 / &2 - abs((y:real^3)$3)` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN UNDISCH_TAC `(y:real^3) IN sch5v_slab(&3 / &2)` THEN
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^1. dist(s,vec 0) < d
                ==> (l:real^1->real^3) s IN sch5v_slab(&3 / &2) /\
                    (l s)$1 pow 2 + (l s)$2 pow 2 = &1 /\ (l s)$3 = (y:real^3)$3 + drop s`
  (LABEL_TAC "LS") THENL
   [GEN_TAC THEN REWRITE_TAC[DIST_0; NORM_1] THEN DISCH_TAC THEN EXPAND_TAC "l" THEN
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(drop s) < d` THEN EXPAND_TAC "d" THEN
    UNDISCH_TAC `(y:real^3) IN sch5v_slab(&3 / &2)` THEN
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN sch5b_ub g Theta /\
                (((g':real^3->real^3) o (Theta:real^3->real^3)) differentiable (at y))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "B1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
            (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `sch5b_ub g Theta` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w = frechet_derivative ((g':real^3->real^3) o (Theta:real^3->real^3)) (at y) (basis 3)` THEN
  SUBGOAL_THEN `(((g':real^3->real^3) o (Theta:real^3->real^3)) o (l:real^1->real^3)
                 has_vector_derivative w) (at (vec 0))` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC SCH5_CHAIN_VECTOR THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  USE_THEN "B1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
          (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)))) THEN
  ABBREV_TAC `u = (g':real^3->real^3)((Theta:real^3->real^3) y)` THEN
  SUBGOAL_THEN `orthogonal (u:real^3) w` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`((g':real^3->real^3) o (Theta:real^3->real^3)) o (l:real^1->real^3)`;
                   `w:real^3`; `vec 0:real^1`; `d:real`] SCH5S_SPHERE_CURVE_ORTH) THEN
    ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
     [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      USE_THEN "LS" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `dist(s:real^1,vec 0) < d`))) THEN
      USE_THEN "B1" (fun th -> MP_TAC(MATCH_MP th
        (CONJ (ASSUME `(l:real^1->real^3) s IN sch5v_slab(&3 / &2)`)
              (ASSUME `((l:real^1->real^3) s)$1 pow 2 + (l s)$2 pow 2 = &1`)))) THEN
      SIMP_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Theta:real^3->real^3) differentiable (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `sch5v_slab(&3 / &2)` THEN
    USE_THEN "TD" (fun th -> REWRITE_TAC[REWRITE_RULE[diffeomorphism_on] th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) differentiable (at u)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `u:real^3`] SCH5_NECK_FACTS) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (g:real^3->real^3) (at u) w =
                frechet_derivative (Theta:real^3->real^3) (at y) (basis 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `(g:real^3->real^3) o ((g':real^3->real^3) o (Theta:real^3->real^3)) o
                (l:real^1->real^3)` THEN
    EXISTS_TAC `vec 0:real^1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCH5_CHAIN_VECTOR THEN ASM_REWRITE_TAC[o_THM] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(Theta:real^3->real^3) o (l:real^1->real^3)` THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      USE_THEN "LS" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `dist(s:real^1,vec 0) < d`))) THEN
      USE_THEN "B1" (fun th -> MP_TAC(MATCH_MP th
        (CONJ (ASSUME `(l:real^1->real^3) s IN sch5v_slab(&3 / &2)`)
              (ASSUME `((l:real^1->real^3) s)$1 pow 2 + (l s)$2 pow 2 = &1`)))) THEN
      SIMP_TAC[];
      MATCH_MP_TAC SCH5_CHAIN_VECTOR THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(frechet_derivative (Theta:real^3->real^3) (at y) (basis 3))$3 = lam`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LIFT_EQ] THEN MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `(\x:real^3. lift(x$3)) o (Theta:real^3->real^3) o (l:real^1->real^3)` THEN
    EXISTS_TAC `vec 0:real^1` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `lift((frechet_derivative (Theta:real^3->real^3) (at y) (basis 3))$3) =
                    (\x:real^3. lift(x$3)) (frechet_derivative Theta (at y) (basis 3))`
      SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SCH5_CHAIN_VECTOR THEN REWRITE_TAC[HAS_DERIVATIVE_LIFT_COMPONENT] THEN
      MATCH_MP_TAC SCH5_CHAIN_VECTOR THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\s:real^1. lift(a + lam * (y:real^3)$3) + drop s % lift lam` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      USE_THEN "LS" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `dist(s:real^1,vec 0) < d`))) THEN
      USE_THEN "HT" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(l:real^1->real^3) s IN sch5v_slab(&3 / &2)`)]) THEN
      ASM_REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN REAL_ARITH_TAC;
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_LID] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
      REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]];
    ALL_TAC] THEN
  REWRITE_TAC[sch_crit] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC);;

(* Two discs on the sphere whose boundaries avoid each other are disjoint.  *)

let SCH5S_DISCS_DISJOINT = prove
 (`!Db Dt Dt0 Ut (B9:real^3->bool) p.
     connected Db /\ Db SUBSET sphere(vec 0,&1) /\
     compact Dt /\ Dt0 SUBSET Dt /\ open Ut /\ Dt0 = sphere(vec 0,&1) INTER Ut /\
     (!x. x IN Dt /\ ~(x IN Dt0) ==> x IN B9) /\ DISJOINT B9 Db /\
     p IN Db /\ ~(p IN Dt)
     ==> DISJOINT Db Dt`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `Db SUBSET ((:real^3) DIFF Dt) UNION Ut` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN ASM_CASES_TAC `(x:real^3) IN Dt` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(x:real^3) IN Dt0` THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((:real^3) DIFF Dt) INTER Ut INTER Db = {}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(((:real^3) DIFF Dt) INTER Db = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open((:real^3) DIFF Dt)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `Ut INTER (Db:real^3->bool) = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `connected(Db:real^3->bool)` THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`(:real^3) DIFF Dt`; `Ut:real^3->bool`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* The clopen argument: an open part of the sphere that equals a closed set  *)
(* and is nonempty is the whole sphere.                                      *)

let SCH5S_SPHERE_CLOPEN = prove
 (`!O K (U:real^3->bool).
     open U /\ O = sphere(vec 0,&1) INTER U /\ closed K /\ K SUBSET sphere(vec 0,&1) /\
     O = K /\ ~(O = {})
     ==> O = sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `&1`] CONNECTED_SPHERE) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `O:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `U:real^3->bool` THEN
    UNDISCH_TAC `O:real^3->bool = K` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `K:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The two discs on the parameter sphere.  The bottom disc D                 *)
(* (bounded by the band circle at height -9/8) and the top disc (bounded by  *)
(* the band circle at height 9/8) are disjoint, and together with the image  *)
(* of the closed band -9/8 <= y3 <= 9/8 they cover the parameter sphere.    *)
(* ------------------------------------------------------------------------- *)

let sch5s_bdisc = new_definition
 `sch5s_bdisc (g':real^3->real^3) (Theta:real^3->real^3) D D0 <=>
    D SUBSET sphere(vec 0,&1) /\ D0 SUBSET D /\
    (?U. open U /\ D0 = sphere(vec 0,&1) INTER U) /\ compact D /\ connected D /\
    (!y. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1 /\ y$3 < &4 / &3
         ==> (g'(Theta y) IN D <=> y$3 <= --(&9 / &8)) /\
             (g'(Theta y) IN D0 <=> y$3 < --(&9 / &8))) /\
    (!x. x IN D /\ ~(x IN D0) ==> ?y. y IN sch5b_circ(--(&9 / &8)) /\ x = g'(Theta y))`;;

let sch5s_tdisc = new_definition
 `sch5s_tdisc (g':real^3->real^3) (Theta:real^3->real^3) D D0 <=>
    D SUBSET sphere(vec 0,&1) /\ D0 SUBSET D /\
    (?U. open U /\ D0 = sphere(vec 0,&1) INTER U) /\ compact D /\ connected D /\
    (!y. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1 /\ --(&4 / &3) < y$3
         ==> (g'(Theta y) IN D <=> &9 / &8 <= y$3) /\
             (g'(Theta y) IN D0 <=> &9 / &8 < y$3)) /\
    (!x. x IN D /\ ~(x IN D0) ==> ?y. y IN sch5b_circ(&9 / &8) /\ x = g'(Theta y))`;;

let SCH5S_BOTTOM2 = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch5b_pancake g g' a lam c c' Theta Theta' /\ sch_morse g /\
     (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     (!t. sch_crit g t ==> ~((g t)$3 = a - lam / &2))
     ==> ?g1 g1' e1 D D0.
           sch_neck g1 g1' /\ sch_morse g1 /\ (!t. sch_crit g1 t ==> ~((g1 t)$3 = a)) /\
           &0 < e1 /\ e1 <= &1 / &16 /\
           (!x. x IN sch_capcone ==> g1 x = Theta(sch_cap_collar e1 x)) /\
           sch5s_bdisc g' Theta D D0 /\
           IMAGE g1 (sphere(vec 0,&1)) =
           (IMAGE g D UNION IMAGE Theta (sch5b_band (--(&9 / &8)) (-- &1))) UNION
           IMAGE Theta sch_cap1 /\
           CARD(sch_saddles g1) = CARD(sch_saddles g INTER D0) /\
           (!u. u IN sch_saddles g INTER D0 ==> ?t. t IN sch_saddles g1 /\ g1 t = g u) /\
           sch_level g1 a = {x | x IN IMAGE g D0 /\ x$3 = a} /\
           IMAGE g1 (sch_saddles g1) = IMAGE g (sch_saddles g INTER D0) /\
           (!t. sch_crit g1 t
                ==> t = basis 3 /\ g1 t = Theta(vector[&0; &0; --(&1 / &2)]) \/
                    (?u. u IN D0 /\ sch_crit g u /\ g1 t = g u)) /\
           (!u. u IN D0 /\ sch_crit g u ==> ?t. sch_crit g1 t /\ g1 t = g u)`,
  REWRITE_TAC[sch5s_bdisc; GSYM CONJ_ASSOC] THEN MATCH_ACCEPT_TAC SCH5B_BOTTOM);;

let SCH5S_TOP2 = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch5b_pancake g g' a lam c c' Theta Theta' /\ sch_morse g /\
     (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     (!t. sch_crit g t ==> ~((g t)$3 = a + lam / &2))
     ==> ?g2 g2' e2 D D0.
           sch_neck g2 g2' /\ sch_morse g2 /\ (!t. sch_crit g2 t ==> ~((g2 t)$3 = a)) /\
           &0 < e2 /\ e2 <= &1 / &16 /\
           (!x. x IN sch_capcone ==> g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e2 x))) /\
           sch5s_tdisc g' Theta D D0 /\
           IMAGE g2 (sphere(vec 0,&1)) =
           (IMAGE g D UNION IMAGE Theta (sch5b_band (&1) (&9 / &8))) UNION
           IMAGE Theta sch_cap2 /\
           CARD(sch_saddles g2) = CARD(sch_saddles g INTER D0) /\
           (!u. u IN sch_saddles g INTER D0 ==> ?t. t IN sch_saddles g2 /\ g2 t = g u) /\
           sch_level g2 a = {x | x IN IMAGE g D0 /\ x$3 = a} /\
           IMAGE g2 (sch_saddles g2) = IMAGE g (sch_saddles g INTER D0) /\
           (!t. sch_crit g2 t
                ==> t = --(basis 3) /\ g2 t = Theta(vector[&0; &0; &1 / &2]) \/
                    (?u. u IN D0 /\ sch_crit g u /\ g2 t = g u)) /\
           (!u. u IN D0 /\ sch_crit g u ==> ?t. sch_crit g2 t /\ g2 t = g u)`,
  REWRITE_TAC[sch5s_tdisc; GSYM CONJ_ASSOC] THEN MATCH_ACCEPT_TAC SCH5S_TOP);;

(* The image of an open band is open in the parameter sphere.               *)

let SCH5S_BAND_OPEN = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' lo hi.
     sch5b_pancake g g' a lam c c' Theta Theta' /\ --(&3 / &2) <= lo /\ hi <= &3 / &2
     ==> ?U. open U /\
             IMAGE (\y. g'(Theta y)) (sch5b_band lo hi) = sphere(vec 0,&1) INTER U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5B_BETA_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "B1" o CONJUNCT1) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_pancake] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_pancake" with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GN") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "TD")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "SIFF"))))))) THEN
  SUBGOAL_THEN `open {y:real^3 | y IN sch5v_slab(&3 / &2) /\ lo < y$3 /\ y$3 < hi}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | y IN sch5v_slab(&3 / &2) /\ lo < y$3 /\ y$3 < hi} =
                  sch5v_slab(&3 / &2) INTER {y | y$3 > lo} INTER {y | y$3 < hi}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT; SCH5V_SLAB_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (Theta:real^3->real^3)
                  {y:real^3 | y IN sch5v_slab(&3 / &2) /\ lo < y$3 /\ y$3 < hi})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sch5v_slab(&3 / &2)`; `IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))`;
                   `Theta:real^3->real^3`; `Theta':real^3->real^3`;
                   `{y:real^3 | y IN sch5v_slab(&3 / &2) /\ lo < y$3 /\ y$3 < hi}`]
      SCH5_DIFFEO_RESTRICT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SET_TAC[];
      SIMP_TAC[diffeomorphism_on]];
    ALL_TAC] THEN
  EXISTS_TAC `{x:real^3 | x IN annulus (&1 / &2) (&2) /\
                          (g:real^3->real^3) x IN IMAGE (Theta:real^3->real^3)
                            {y:real^3 | y IN sch5v_slab(&3 / &2) /\ lo < y$3 /\ y$3 < hi}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    USE_THEN "GN" (fun th -> REWRITE_TAC[REWRITE_RULE[sch_neck; diffeomorphism_on] th]);
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    REWRITE_TAC[sch5b_band; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&3 / &2)` ASSUME_TAC THENL
     [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `lo < (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 < hi` THEN
      UNDISCH_TAC `--(&3 / &2) <= lo` THEN UNDISCH_TAC `hi <= &3 / &2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "B1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
            (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)))) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `y:real^3` THEN
  SUBGOAL_THEN `(g':real^3->real^3)((g:real^3->real^3) x) = x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `x:real^3`] SCH5_NECK_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 = &1` ASSUME_TAC THENL
   [USE_THEN "SIFF" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`))]) THEN
    UNDISCH_TAC `(g:real^3->real^3) x = Theta(y:real^3)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[sch5b_band; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(g:real^3->real^3) x = Theta(y:real^3)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[]);;

(* The image of the closed band -9/8 <= y3 <= 9/8 is compact.              *)

let SCH5S_CBAND_COMPACT = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch5b_pancake g g' a lam c c' Theta Theta'
     ==> compact(IMAGE (\y. g'(Theta y))
                   {y:real^3 | y$1 pow 2 + y$2 pow 2 = &1 /\
                               --(&9 / &8) <= y$3 /\ y$3 <= &9 / &8})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5B_BETA_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "B1") STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sch5b_ub g Theta` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\y. (g':real^3->real^3)((Theta:real^3->real^3) y)) = g' o Theta`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      USE_THEN "B1" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
      UNDISCH_TAC `--(&9 / &8) <= (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 <= &9 / &8` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [REWRITE_TAC[bounded; IN_ELIM_THM] THEN EXISTS_TAC `&3` THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN REWRITE_TAC[NORM_LE_SQUARE; DOT_3] THEN
    MP_TAC(SPECL [`&9 / &8 - (y:real^3)$3`; `&9 / &8 + (y:real^3)$3`] REAL_LE_MUL) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `--(&9 / &8) <= (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 <= &9 / &8` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 = &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^3 | y$1 pow 2 + y$2 pow 2 = &1 /\ --(&9 / &8) <= y$3 /\ y$3 <= &9 / &8} =
                {y | (\y:real^3. lift(y$1 pow 2 + y$2 pow 2)) y IN {lift(&1)}} INTER
                {y | y$3 >= --(&9 / &8)} INTER {y | y$3 <= &9 / &8}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING; LIFT_EQ; real_ge]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
  REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE; CLOSED_HALFSPACE_COMPONENT_LE] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN REWRITE_TAC[CLOSED_SING] THEN
  GEN_TAC THEN REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ADD THEN
  REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[o_DEF] THEN
  SIMP_TAC[CONTINUOUS_AT_LIFT_COMPONENT; DIMINDEX_3; ARITH]);;

(* Destructuring the disc predicates without opening the existential.       *)

let sch5s_disc_tac (l1,l2,l3) =
  CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC l1)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC l2) (LABEL_TAC l3))))));;

let SCH5S_DISCS_DISJ = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'
    Db Db0 Dt Dt0.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5s_bdisc g' Theta Db Db0 /\ sch5s_tdisc g' Theta Dt Dt0
     ==> DISJOINT Db Dt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5s_bdisc; sch5s_tdisc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (sch5s_disc_tac ("UB","BB","BBD")) (sch5s_disc_tac ("UT","TB","TBD")))) THEN
  USE_THEN "UT" (X_CHOOSE_THEN `Ut:real^3->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SCH5S_DISCS_DISJOINT THEN
  MAP_EVERY EXISTS_TAC
   [`Dt0:real^3->bool`; `Ut:real^3->bool`;
    `IMAGE (\y. (g':real^3->real^3)((Theta:real^3->real^3) y)) (sch5b_circ(&9 / &8))`;
    `(g':real^3->real^3)((Theta:real^3->real^3)(vector[&1; &0; --(&9 / &8)]))`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "TBD" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(x:real^3) IN Dt /\ ~(x IN Dt0)`))) THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    UNDISCH_TAC `(y:real^3) IN sch5b_circ(&9 / &8)` THEN
    REWRITE_TAC[sch5b_circ; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&3 / &2)` ASSUME_TAC THENL
     [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((g':real^3->real^3)((Theta:real^3->real^3) y) IN Db)` MP_TAC THENL
     [USE_THEN "BB" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_MESON_TAC[]];
    USE_THEN "BB" (MP_TAC o SPEC `vector[&1; &0; --(&9 / &8)]:real^3`) THEN
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM; VECTOR_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[];
    USE_THEN "TB" (MP_TAC o SPEC `vector[&1; &0; --(&9 / &8)]:real^3`) THEN
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM; VECTOR_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[]]);;

(* The parameter sphere is covered by the open discs and the closed band.  *)

let SCH5S_DISCS_COVER = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'
    Db Db0 Dt Dt0.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5s_bdisc g' Theta Db Db0 /\ sch5s_tdisc g' Theta Dt Dt0
     ==> sphere(vec 0,&1) =
         Db0 UNION
         IMAGE (\y. g'(Theta y))
           {y:real^3 | y$1 pow 2 + y$2 pow 2 = &1 /\ --(&9 / &8) <= y$3 /\ y$3 <= &9 / &8}
         UNION Dt0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5s_bdisc; sch5s_tdisc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (sch5s_disc_tac ("UB","BB","BBD")) (sch5s_disc_tac ("UT","TB","TBD")))) THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5B_BETA_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "B1" o CONJUNCT1) THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5S_CBAND_COMPACT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y:real^3. y$1 pow 2 + y$2 pow 2 = &1 /\ --(&5 / &4) < y$3 /\ y$3 < &5 / &4
                ==> y IN sch5v_slab(&3 / &2) /\ y$3 < &4 / &3 /\ --(&4 / &3) < y$3`
  (LABEL_TAC "SL") THENL
   [GEN_TAC THEN REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `Db0 UNION IMAGE (\y. (g':real^3->real^3)((Theta:real^3->real^3) y))
                (sch5b_band (--(&5 / &4)) (&5 / &4)) UNION Dt0 =
    sphere(vec 0,&1)` (LABEL_TAC "OX") THENL
   [USE_THEN "UB" (X_CHOOSE_THEN `Ub:real^3->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "UT" (X_CHOOSE_THEN `Ut:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL (sch5b_bvars8 @ [`--(&5 / &4)`; `&5 / &4`]) SCH5S_BAND_OPEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Um:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SCH5S_SPHERE_CLOPEN THEN
    EXISTS_TAC `Db UNION IMAGE (\y. (g':real^3->real^3)((Theta:real^3->real^3) y))
                  {y:real^3 | y$1 pow 2 + y$2 pow 2 = &1 /\ --(&9 / &8) <= y$3 /\ y$3 <= &9 / &8}
                UNION Dt` THEN
    EXISTS_TAC `Ub UNION Um UNION Ut:real^3->bool` THEN
    REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC OPEN_UNION THEN CONJ_TAC) THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
      USE_THEN "B1" (fun th -> MP_TAC(SPEC `y:real^3` th)) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
      UNDISCH_TAC `--(&9 / &8) <= (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 <= &9 / &8` THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_ELIM_THM; sch5b_band] THEN
      X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
       [DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2
          (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THENL
         [DISJ1_TAC THEN UNDISCH_TAC `(x:real^3) IN Db0` THEN
          UNDISCH_TAC `(Db0:real^3->bool) SUBSET Db` THEN SET_TAC[];
          USE_THEN "SL" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
          USE_THEN "BB" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
          USE_THEN "TB" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
          ASM_CASES_TAC `(y:real^3)$3 <= --(&9 / &8)` THENL
           [DISJ1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          ASM_CASES_TAC `&9 / &8 <= (y:real^3)$3` THENL
           [DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `~((y:real^3)$3 <= --(&9 / &8))` THEN
          UNDISCH_TAC `~(&9 / &8 <= (y:real^3)$3)` THEN REAL_ARITH_TAC;
          DISJ2_TAC THEN DISJ2_TAC THEN UNDISCH_TAC `(x:real^3) IN Dt0` THEN
          UNDISCH_TAC `(Dt0:real^3->bool) SUBSET Dt` THEN SET_TAC[]];
        DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2
          (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THENL
         [ASM_CASES_TAC `(x:real^3) IN Db0` THENL
           [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
          USE_THEN "BBD" (fun th -> MP_TAC(MATCH_MP th
            (CONJ (ASSUME `(x:real^3) IN Db`) (ASSUME `~((x:real^3) IN Db0)`)))) THEN
          REWRITE_TAC[sch5b_circ; IN_ELIM_THM] THEN
          DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
          DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV;
          DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `--(&9 / &8) <= (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 <= &9 / &8` THEN
          REAL_ARITH_TAC;
          ASM_CASES_TAC `(x:real^3) IN Dt0` THENL
           [DISJ2_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
          USE_THEN "TBD" (fun th -> MP_TAC(MATCH_MP th
            (CONJ (ASSUME `(x:real^3) IN Dt`) (ASSUME `~((x:real^3) IN Dt0)`)))) THEN
          REWRITE_TAC[sch5b_circ; IN_ELIM_THM] THEN
          DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
          DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `(g':real^3->real^3)((Theta:real^3->real^3)(vector[&1; &0; &0]))` THEN
      REWRITE_TAC[IN_UNION; IN_IMAGE] THEN DISJ2_TAC THEN DISJ1_TAC THEN
      EXISTS_TAC `vector[&1; &0; &0]:real^3` THEN
      REWRITE_TAC[sch5b_band; IN_ELIM_THM; VECTOR_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  USE_THEN "OX" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_ELIM_THM; sch5b_band] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "SL" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "BB" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    USE_THEN "TB" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    ASM_CASES_TAC `(y:real^3)$3 < --(&9 / &8)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&9 / &8 < (y:real^3)$3` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((y:real^3)$3 < --(&9 / &8))` THEN
    UNDISCH_TAC `~(&9 / &8 < (y:real^3)$3)` THEN REAL_ARITH_TAC;
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `--(&9 / &8) <= (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 <= &9 / &8` THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The slab configuration.  With E1 = g(D_bottom) plus the band               *)
(* -9/8 < y3 < -1 and E2 = g(D_top) plus the band 1 < y3 < 9/8, the sphere  *)
(* S = g(S^2) is E1 + Theta(sch_lat) + E2 and the surgered spheres are       *)
(* E1 + Theta(cap1) and E2 + Theta(cap2) (sch_slab_config, N = slab 5/4).    *)
(* ------------------------------------------------------------------------- *)

let sch5s_pancake_tac =
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_pancake] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_pancake" with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GN") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "TD")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "SIFF")))))));;

let SCH5S_THETA_INJ = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' y y'.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     y IN sch5v_slab(&3 / &2) /\ y' IN sch5v_slab(&3 / &2) /\ Theta y = Theta y'
     ==> y = y'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN sch5s_pancake_tac THEN
  SUBGOAL_THEN `!x:real^3. x IN sch5v_slab(&3 / &2) ==> (Theta':real^3->real^3)(Theta x) = x`
  MP_TAC THENL
   [USE_THEN "TD" (fun th -> MP_TAC(REWRITE_RULE[diffeomorphism_on] th)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `y':real^3` th) THEN MP_TAC(SPEC `y:real^3` th)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let SCH5S_E1_MEMBER = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' Db Db0 y.
     sch5b_pancake g g' a lam c c' Theta Theta' /\ sch5s_bdisc g' Theta Db Db0 /\
     y IN sch5v_slab(&5 / &4)
     ==> (Theta y IN IMAGE g Db UNION IMAGE Theta (sch5b_band (--(&9 / &8)) (-- &1)) <=>
          y$1 pow 2 + y$2 pow 2 = &1 /\ y$3 < -- &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5s_bdisc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (sch5s_disc_tac ("UB","BB","BBD")) ASSUME_TAC)) THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5B_BETA_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "B1" o CONJUNCT1) THEN sch5s_pancake_tac THEN
  SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&3 / &2) /\ y$3 < &4 / &3` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN sch5v_slab(&5 / &4)` THEN
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EQ_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
                                (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THENL
     [SUBGOAL_THEN `(x:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN Db` THEN UNDISCH_TAC `(Db:real^3->bool) SUBSET sphere(vec 0,&1)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 = &1` ASSUME_TAC THENL
       [USE_THEN "SIFF" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
          (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`))]) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(g':real^3->real^3)((Theta:real^3->real^3) y) = x` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `x:real^3`] SCH5_NECK_FACTS) THEN
        ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
        ALL_TAC] THEN
      USE_THEN "BB" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(z:real^3) IN sch5b_band (--(&9 / &8)) (-- &1)` THEN
      REWRITE_TAC[sch5b_band; IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) = z` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC SCH5S_THETA_INJ THEN
        MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                              `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                              `Theta':real^3->real^3`] THEN
        ASM_REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
        UNDISCH_TAC `--(&9 / &8) < (z:real^3)$3` THEN UNDISCH_TAC `(z:real^3)$3 < -- &1` THEN
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    STRIP_TAC THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
    ASM_CASES_TAC `(y:real^3)$3 <= --(&9 / &8)` THENL
     [DISJ1_TAC THEN EXISTS_TAC `(g':real^3->real^3)((Theta:real^3->real^3) y)` THEN
      USE_THEN "B1" (fun th -> MP_TAC(MATCH_MP th
        (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
              (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "BB" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `y:real^3` THEN REWRITE_TAC[sch5b_band; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((y:real^3)$3 <= --(&9 / &8))` THEN REAL_ARITH_TAC]]);;

let SCH5S_E2_MEMBER = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' Dt Dt0 y.
     sch5b_pancake g g' a lam c c' Theta Theta' /\ sch5s_tdisc g' Theta Dt Dt0 /\
     y IN sch5v_slab(&5 / &4)
     ==> (Theta y IN IMAGE g Dt UNION IMAGE Theta (sch5b_band (&1) (&9 / &8)) <=>
          y$1 pow 2 + y$2 pow 2 = &1 /\ &1 < y$3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch5s_tdisc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (sch5s_disc_tac ("UT","TB","TBD")) ASSUME_TAC)) THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5B_BETA_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "B1" o CONJUNCT1) THEN sch5s_pancake_tac THEN
  SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&3 / &2) /\ --(&4 / &3) < y$3` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN sch5v_slab(&5 / &4)` THEN
    REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EQ_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
                                (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THENL
     [SUBGOAL_THEN `(x:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN Dt` THEN UNDISCH_TAC `(Dt:real^3->bool) SUBSET sphere(vec 0,&1)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 = &1` ASSUME_TAC THENL
       [USE_THEN "SIFF" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
          (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`))]) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(g':real^3->real^3)((Theta:real^3->real^3) y) = x` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `x:real^3`] SCH5_NECK_FACTS) THEN
        ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
        ALL_TAC] THEN
      USE_THEN "TB" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(z:real^3) IN sch5b_band (&1) (&9 / &8)` THEN
      REWRITE_TAC[sch5b_band; IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) = z` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC SCH5S_THETA_INJ THEN
        MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                              `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                              `Theta':real^3->real^3`] THEN
        ASM_REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
        UNDISCH_TAC `&1 < (z:real^3)$3` THEN UNDISCH_TAC `(z:real^3)$3 < &9 / &8` THEN
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    STRIP_TAC THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
    ASM_CASES_TAC `&9 / &8 <= (y:real^3)$3` THENL
     [DISJ1_TAC THEN EXISTS_TAC `(g':real^3->real^3)((Theta:real^3->real^3) y)` THEN
      USE_THEN "B1" (fun th -> MP_TAC(MATCH_MP th
        (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
              (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "TB" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `y:real^3` THEN REWRITE_TAC[sch5b_band; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(&9 / &8 <= (y:real^3)$3)` THEN REAL_ARITH_TAC]]);;

let SCH5S_SLAB_CONFIG = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'
    Db Db0 Dt Dt0.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     ((!y. y IN sch5v_slab(&3 / &2)
           ==> (Theta y IN inside(IMAGE g (sphere(vec 0,&1))) <=>
                y$1 pow 2 + y$2 pow 2 < &1)) \/
      (!y. y IN sch5v_slab(&3 / &2)
           ==> (Theta y IN outside(IMAGE g (sphere(vec 0,&1))) <=>
                y$1 pow 2 + y$2 pow 2 < &1))) /\
     sch5s_bdisc g' Theta Db Db0 /\ sch5s_tdisc g' Theta Dt Dt0
     ==> sch_slab_config (IMAGE g (sphere(vec 0,&1)))
           ((IMAGE g Db UNION IMAGE Theta (sch5b_band (--(&9 / &8)) (-- &1))) UNION
            IMAGE Theta sch_cap1)
           ((IMAGE g Dt UNION IMAGE Theta (sch5b_band (&1) (&9 / &8))) UNION
            IMAGE Theta sch_cap2)
           Theta`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "SIDES")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`; `Dt:real^3->bool`;
                                 `Dt0:real^3->bool`]) SCH5S_DISCS_DISJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`; `Dt:real^3->bool`;
                                 `Dt0:real^3->bool`]) SCH5S_DISCS_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "COV" o SYM) THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`]) SCH5S_E1_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "E1M") THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`Dt:real^3->bool`; `Dt0:real^3->bool`]) SCH5S_E2_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "E2M") THEN
  SUBGOAL_THEN `(Db0:real^3->bool) SUBSET Db /\ Db SUBSET sphere(vec 0,&1) /\
                (Dt0:real^3->bool) SUBSET Dt /\ Dt SUBSET sphere(vec 0,&1)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sch5s_bdisc (g':real^3->real^3) (Theta:real^3->real^3) Db Db0` THEN
    UNDISCH_TAC `sch5s_tdisc (g':real^3->real^3) (Theta:real^3->real^3) Dt Dt0` THEN
    REWRITE_TAC[sch5s_bdisc; sch5s_tdisc] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5B_BETA_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "B1" o CONJUNCT1) THEN sch5s_pancake_tac THEN
  SUBGOAL_THEN `sch5v_slab(&5 / &4) SUBSET sch5v_slab(&3 / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; sch5v_slab; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1
                ==> (Theta:real^3->real^3) y IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`
  (LABEL_TAC "INS") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "SIFF" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)]) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[sch_slab_config] THEN
  MAP_EVERY EXISTS_TAC
   [`sch_slab_nbhd`; `Theta':real^3->real^3`;
    `IMAGE (g:real^3->real^3) Db UNION
     IMAGE (Theta:real^3->real^3) (sch5b_band (--(&9 / &8)) (-- &1))`;
    `IMAGE (g:real^3->real^3) Dt UNION IMAGE (Theta:real^3->real^3) (sch5b_band (&1) (&9 / &8))`] THEN
  REWRITE_TAC[CONJUNCT1 SCH5V_SLAB_FACTS; SUBSET_REFL; CONJUNCT2(CONJUNCT2 SCH5V_SLAB_FACTS)] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCH5_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`sch5v_slab(&3 / &2)`;
                          `IMAGE (Theta:real^3->real^3) (sch5v_slab(&3 / &2))`] THEN
    ASM_REWRITE_TAC[SCH5V_SLAB_FACTS];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "SIFF" MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN sch5v_slab(&5 / &4)` THEN
    UNDISCH_TAC `sch5v_slab(&5 / &4) SUBSET sch5v_slab(&3 / &2)` THEN SET_TAC[];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      UNDISCH_TAC `(u:real^3) IN sphere(vec 0,&1)` THEN
      USE_THEN "COV" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[IN_UNION; IN_IMAGE; IN_ELIM_THM]) THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2
        (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THENL
       [REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `(u:real^3) IN Db0` THEN UNDISCH_TAC `(Db0:real^3->bool) SUBSET Db` THEN
        SET_TAC[];
        SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&5 / &4)` ASSUME_TAC THENL
         [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `--(&9 / &8) <= (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 <= &9 / &8` THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `(g:real^3->real^3) u = (Theta:real^3->real^3) y` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[] THEN USE_THEN "B1" (fun th -> MP_TAC(SPEC `y:real^3` th)) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `sch5v_slab(&5 / &4) SUBSET sch5v_slab(&3 / &2)` THEN
            UNDISCH_TAC `(y:real^3) IN sch5v_slab(&5 / &4)` THEN SET_TAC[];
            SIMP_TAC[]];
          ALL_TAC] THEN
        ASM_CASES_TAC `(y:real^3)$3 < -- &1` THENL
         [MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> x IN s UNION t`) THEN
          USE_THEN "E1M" (fun th -> REWRITE_TAC[MATCH_MP th
            (ASSUME `(y:real^3) IN sch5v_slab(&5 / &4)`)]) THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        ASM_CASES_TAC `&1 < (y:real^3)$3` THENL
         [MATCH_MP_TAC(SET_RULE `(x:real^3) IN u ==> x IN s UNION t UNION u`) THEN
          USE_THEN "E2M" (fun th -> REWRITE_TAC[MATCH_MP th
            (ASSUME `(y:real^3) IN sch5v_slab(&5 / &4)`)]) THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE `(x:real^3) IN t ==> x IN s UNION t UNION u`) THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN
        REWRITE_TAC[sch_lat; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~((y:real^3)$3 < -- &1)` THEN UNDISCH_TAC `~(&1 < (y:real^3)$3)` THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `(u:real^3) IN Dt0` THEN UNDISCH_TAC `(Dt0:real^3->bool) SUBSET Dt` THEN
        SET_TAC[]];
      REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN IMAGE (g:real^3->real^3) Db` THEN
        UNDISCH_TAC `(Db:real^3->bool) SUBSET sphere(vec 0,&1)` THEN SET_TAC[];
        UNDISCH_TAC `(x:real^3) IN IMAGE (Theta:real^3->real^3) (sch5b_band (--(&9 / &8)) (-- &1))` THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o
          REWRITE_RULE[IN_IMAGE; sch5b_band; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "INS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
        UNDISCH_TAC `--(&9 / &8) < (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 < -- &1` THEN
        REAL_ARITH_TAC;
        UNDISCH_TAC `(x:real^3) IN IMAGE (Theta:real^3->real^3) sch_lat` THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o
          REWRITE_RULE[IN_IMAGE; sch_lat; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "INS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
        UNDISCH_TAC `abs((y:real^3)$3) <= &1` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `(x:real^3) IN IMAGE (g:real^3->real^3) Dt` THEN
        UNDISCH_TAC `(Dt:real^3->bool) SUBSET sphere(vec 0,&1)` THEN SET_TAC[];
        UNDISCH_TAC `(x:real^3) IN IMAGE (Theta:real^3->real^3) (sch5b_band (&1) (&9 / &8))` THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o
          REWRITE_RULE[IN_IMAGE; sch5b_band; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "INS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
        UNDISCH_TAC `&1 < (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 < &9 / &8` THEN
        REAL_ARITH_TAC]];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "X1") (LABEL_TAC "X2")) THEN
    ASM_CASES_TAC `(x:real^3) IN IMAGE (Theta:real^3->real^3) (sch5b_band (--(&9 / &8)) (-- &1))` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
      UNDISCH_TAC `(y:real^3) IN sch5b_band (--(&9 / &8)) (-- &1)` THEN
      REWRITE_TAC[sch5b_band; IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&5 / &4)` ASSUME_TAC THENL
       [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `--(&9 / &8) < (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 < -- &1` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "E2M" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(x:real^3) = (Theta:real^3->real^3) y` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        USE_THEN "X2" ACCEPT_TAC;
        UNDISCH_TAC `(y:real^3)$3 < -- &1` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^3) IN IMAGE (Theta:real^3->real^3) (sch5b_band (&1) (&9 / &8))` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
      UNDISCH_TAC `(y:real^3) IN sch5b_band (&1) (&9 / &8)` THEN
      REWRITE_TAC[sch5b_band; IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&5 / &4)` ASSUME_TAC THENL
       [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&1 < (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 < &9 / &8` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "E1M" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(x:real^3) = (Theta:real^3->real^3) y` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        USE_THEN "X1" ACCEPT_TAC;
        UNDISCH_TAC `&1 < (y:real^3)$3` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN IMAGE (g:real^3->real^3) Db /\ x IN IMAGE g Dt` MP_TAC THENL
     [UNDISCH_TAC `~((x:real^3) IN IMAGE (Theta:real^3->real^3) (sch5b_band (--(&9 / &8)) (-- &1)))` THEN
      UNDISCH_TAC `~((x:real^3) IN IMAGE (Theta:real^3->real^3) (sch5b_band (&1) (&9 / &8)))` THEN
      USE_THEN "X1" MP_TAC THEN USE_THEN "X2" MP_TAC THEN REWRITE_TAC[IN_UNION] THEN
      CONV_TAC TAUT;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(u:real^3) = v` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `(u:real^3) IN sphere(vec 0,&1) /\ (v:real^3) IN sphere(vec 0,&1)` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `u:real^3`] SCH5_NECK_FACTS) THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `v:real^3`] SCH5_NECK_FACTS) THEN
      ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN
      UNDISCH_TAC `(x:real^3) = (g:real^3->real^3) u` THEN
      UNDISCH_TAC `(x:real^3) = (g:real^3->real^3) v` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (Db:real^3->bool) Dt` THEN UNDISCH_TAC `(v:real^3) IN Db` THEN
    UNDISCH_TAC `(v:real^3) IN Dt` THEN SET_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "E1M" MATCH_MP_TAC; USE_THEN "E2M" MATCH_MP_TAC] THEN FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "SIDES" (DISJ_CASES_THEN ASSUME_TAC) THENL [DISJ1_TAC; DISJ2_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN sch5v_slab(&5 / &4)` THEN
    UNDISCH_TAC `sch5v_slab(&5 / &4) SUBSET sch5v_slab(&3 / &2)` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Bookkeeping.  Critical points of g lie in the two open discs;              *)
(* the saddles split accordingly; the level a of g is the disjoint union of  *)
(* the two disc parts and the cut circle C = Theta(r = 1, y3 = 0), so it has *)
(* one more component than the two disc parts together.                     *)
(* ------------------------------------------------------------------------- *)

let SCH5S_COMPONENTS_COUNT = prove
 (`!L1 C L2 (s:real^N->bool).
     s = L1 UNION (C UNION L2) /\ closed L1 /\ closed C /\ closed L2 /\
     connected C /\ ~(C = {}) /\
     DISJOINT L1 C /\ DISJOINT L2 C /\ DISJOINT L1 L2 /\ FINITE(components s)
     ==> CARD(components L1) + CARD(components L2) + 1 = CARD(components s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `components(s:real^N->bool) = components L1 UNION ({C} UNION components L2)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `components((L1:real^N->bool) UNION (C UNION L2)) =
                  components L1 UNION components (C UNION L2)` SUBST1_TAC THENL
     [MATCH_MP_TAC COMPONENTS_SEPARATED_UNION THEN
      ASM_SIMP_TAC[CLOSURE_CLOSED; CLOSED_UNION] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `components((C:real^N->bool) UNION L2) = components C UNION components L2`
    SUBST1_TAC THENL
     [MATCH_MP_TAC COMPONENTS_SEPARATED_UNION THEN
      ASM_SIMP_TAC[CLOSURE_CLOSED] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `components (C:real^N->bool) = {C}` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[COMPONENTS_EQ_SING]; REFL_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(components(L1:real^N->bool)) /\ FINITE(components(L2:real^N->bool))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `FINITE(components(s:real^N->bool))` THEN ASM_REWRITE_TAC[FINITE_UNION] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNION o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION; FINITE_SING] THEN
    REWRITE_TAC[GSYM DISJOINT; IN_DISJOINT; IN_UNION; IN_SING; NOT_EXISTS_THM] THEN
    X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THENL
     [UNDISCH_TAC `(k:real^N->bool) = C` THEN DISCH_THEN SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`L1:real^N->bool`; `C:real^N->bool`] IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (L1:real^N->bool) C` THEN
      UNDISCH_TAC `~(C:real^N->bool = {})` THEN SET_TAC[];
      MP_TAC(ISPECL [`L1:real^N->bool`; `k:real^N->bool`] IN_COMPONENTS_SUBSET) THEN
      MP_TAC(ISPECL [`L2:real^N->bool`; `k:real^N->bool`] IN_COMPONENTS_SUBSET) THEN
      MP_TAC(ISPECL [`L2:real^N->bool`; `k:real^N->bool`] IN_COMPONENTS_NONEMPTY) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (L1:real^N->bool) L2` THEN SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNION o rand o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_SING] THEN
    REWRITE_TAC[GSYM DISJOINT; IN_DISJOINT; IN_SING; NOT_EXISTS_THM] THEN
    X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `(k:real^N->bool) = C` THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`L2:real^N->bool`; `C:real^N->bool`] IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (L2:real^N->bool) C` THEN
    UNDISCH_TAC `~(C:real^N->bool = {})` THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[CARD_SING] THEN ARITH_TAC);;

let SCH5S_CIRC_IMAGE = prove
 (`!h. sch5b_circ h = IMAGE (\w:real^2. vector[w$1; w$2; h]:real^3) (sphere(vec 0,&1)) /\
       compact(sch5b_circ h) /\ connected(sch5b_circ h)`,
  GEN_TAC THEN
  SUBGOAL_THEN `sch5b_circ h = IMAGE (\w:real^2. vector[w$1; w$2; h]:real^3) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; sch5b_circ; IN_ELIM_THM; IN_IMAGE; IN_SPHERE_0] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `vector[(x:real^3)$1; x$2]:real^2` THEN
      REWRITE_TAC[NORM_EQ_SQUARE; DOT_2; VECTOR_2] THEN CONJ_TAC THENL
       [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(x:real^3)$1 pow 2 + x$2 pow 2 = &1` THEN REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `w:real^2` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      REWRITE_TAC[NORM_EQ_SQUARE; DOT_2; VECTOR_3] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE; MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE] THEN
  SIMP_TAC[COMPACT_SPHERE; CONNECTED_SPHERE; DIMINDEX_2; LE_REFL] THEN
  GEN_REWRITE_TAC I [CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; CONTINUOUS_ON_CONST] THEN
  SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH]);;

let sch5s_pancake_tac2 =
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_pancake] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_pancake" with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GN") (CONJUNCTS_THEN2 (LABEL_TAC "LP")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "TD")
    (CONJUNCTS_THEN2 (LABEL_TAC "HT") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "SIFF")))))));;

(* Points of the band: g(g'(Theta y)) = Theta y at height a + lam y3.      *)

let SCH5S_BAND_POINT = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' y.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1
     ==> g'(Theta y) IN sphere(vec 0,&1) /\ g(g'(Theta y)) = Theta y /\
         Theta y IN IMAGE g (sphere(vec 0,&1)) /\ (Theta y)$3 = a + lam * y$3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5B_BETA_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "B1" o CONJUNCT1) THEN sch5s_pancake_tac2 THEN
  USE_THEN "B1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (CONJ (ASSUME `(y:real^3) IN sch5v_slab(&3 / &2)`)
          (ASSUME `(y:real^3)$1 pow 2 + y$2 pow 2 = &1`)))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g':real^3->real^3)((Theta:real^3->real^3) y)` THEN
    ASM_REWRITE_TAC[];
    USE_THEN "HT" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let SCH5S_LEVEL_PIECES = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'
    Db Db0 Dt Dt0.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5s_bdisc g' Theta Db Db0 /\ sch5s_tdisc g' Theta Dt Dt0
     ==> sch_level g a =
         {x | x IN IMAGE g Db0 /\ x$3 = a} UNION
         (IMAGE Theta (sch5b_circ(&0)) UNION {x | x IN IMAGE g Dt0 /\ x$3 = a}) /\
         compact {x | x IN IMAGE g Db0 /\ x$3 = a} /\
         compact {x | x IN IMAGE g Dt0 /\ x$3 = a} /\
         compact(IMAGE Theta (sch5b_circ(&0))) /\ connected(IMAGE Theta (sch5b_circ(&0))) /\
         ~(IMAGE Theta (sch5b_circ(&0)) = {}) /\
         DISJOINT {x | x IN IMAGE g Db0 /\ x$3 = a} (IMAGE Theta (sch5b_circ(&0))) /\
         DISJOINT {x | x IN IMAGE g Dt0 /\ x$3 = a} (IMAGE Theta (sch5b_circ(&0))) /\
         DISJOINT {x | x IN IMAGE g Db0 /\ x$3 = a} {x | x IN IMAGE g Dt0 /\ x$3 = a}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`; `Dt:real^3->bool`;
                                 `Dt0:real^3->bool`]) SCH5S_DISCS_DISJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`; `Dt:real^3->bool`;
                                 `Dt0:real^3->bool`]) SCH5S_DISCS_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "COV" o SYM) THEN
  UNDISCH_TAC `sch5s_bdisc (g':real^3->real^3) (Theta:real^3->real^3) Db Db0` THEN
  UNDISCH_TAC `sch5s_tdisc (g':real^3->real^3) (Theta:real^3->real^3) Dt Dt0` THEN
  REWRITE_TAC[sch5s_bdisc; sch5s_tdisc] THEN
  DISCH_THEN(sch5s_disc_tac ("UT","TB","TBD")) THEN
  DISCH_THEN(sch5s_disc_tac ("UB","BB","BBD")) THEN
  sch5s_pancake_tac2 THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5S_BAND_POINT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "BP") THEN
  SUBGOAL_THEN `!u:real^3. u IN sphere(vec 0,&1) ==> (g':real^3->real^3)((g:real^3->real^3) u) = u`
  (LABEL_TAC "GI") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `u:real^3`] SCH5_NECK_FACTS) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sch5b_circ(&0) ==> y IN sch5v_slab(&3 / &2) /\
                y$1 pow 2 + y$2 pow 2 = &1 /\ y$3 = &0 /\ y$3 < &4 / &3 /\ --(&4 / &3) < y$3`
  (LABEL_TAC "C0") THENL
   [GEN_TAC THEN REWRITE_TAC[sch5b_circ; sch5v_slab; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `{x | x IN IMAGE (g:real^3->real^3) Db0 /\ x$3 = a} =
                IMAGE g Db INTER {x:real^3 | x$3 = a}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN IMAGE (g:real^3->real^3) Db0` THEN
      UNDISCH_TAC `(Db0:real^3->bool) SUBSET Db` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real^3` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(u:real^3) IN Db0` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "BBD" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(u:real^3) IN Db`) (ASSUME `~((u:real^3) IN Db0)`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(y:real^3) IN sch5b_circ(--(&9 / &8))` THEN
    REWRITE_TAC[sch5b_circ; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&3 / &2)` ASSUME_TAC THENL
     [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    USE_THEN "BP" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    UNDISCH_TAC `((x:real^3))$3 = a` THEN
    UNDISCH_TAC `(x:real^3) = (g:real^3->real^3) u` THEN
    UNDISCH_TAC `(u:real^3) = (g':real^3->real^3)((Theta:real^3->real^3) y)` THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{x | x IN IMAGE (g:real^3->real^3) Dt0 /\ x$3 = a} =
                IMAGE g Dt INTER {x:real^3 | x$3 = a}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN IMAGE (g:real^3->real^3) Dt0` THEN
      UNDISCH_TAC `(Dt0:real^3->bool) SUBSET Dt` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real^3` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(u:real^3) IN Dt0` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "TBD" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(u:real^3) IN Dt`) (ASSUME `~((u:real^3) IN Dt0)`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(y:real^3) IN sch5b_circ(&9 / &8)` THEN
    REWRITE_TAC[sch5b_circ; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&3 / &2)` ASSUME_TAC THENL
     [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    USE_THEN "BP" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    UNDISCH_TAC `((x:real^3))$3 = a` THEN
    UNDISCH_TAC `(x:real^3) = (g:real^3->real^3) u` THEN
    UNDISCH_TAC `(u:real^3) = (g':real^3->real^3)((Theta:real^3->real^3) y)` THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&0` SCH5S_CIRC_IMAGE) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Theta:real^3->real^3) continuous_on sch5b_circ(&0)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sch5v_slab(&3 / &2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      USE_THEN "TD" (fun th -> REWRITE_TAC[REWRITE_RULE[diffeomorphism_on] th]);
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "C0" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^3) IN sch5b_circ(&0)`)])];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      USE_THEN "GN" (fun th -> REWRITE_TAC[REWRITE_RULE[sch_neck; diffeomorphism_on] th]);
      REWRITE_TAC[SUBSET; SCH5_SPHERE_IN_ANNULUS]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[sch_level; EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) o
        REWRITE_RULE[IN_IMAGE]) THEN
      USE_THEN "COV" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[IN_UNION; IN_IMAGE; IN_ELIM_THM]) THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2
        (X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) ASSUME_TAC)) THENL
       [DISJ1_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
        SUBGOAL_THEN `(y:real^3) IN sch5v_slab(&3 / &2)` ASSUME_TAC THENL
         [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `--(&9 / &8) <= (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 <= &9 / &8` THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        USE_THEN "BP" (MP_TAC o SPEC `y:real^3`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN
        REWRITE_TAC[sch5b_circ; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `lam * (y:real^3)$3 = &0` MP_TAC THENL
         [UNDISCH_TAC `((g:real^3->real^3)((g':real^3->real^3)((Theta:real^3->real^3) y)))$3 = a` THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          REWRITE_TAC[REAL_ENTIRE] THEN UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC];
        DISJ2_TAC THEN DISJ2_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE]];
      DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC (DISJ_CASES_THEN2 MP_TAC STRIP_ASSUME_TAC)) THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN IMAGE (g:real^3->real^3) Db0` THEN
        UNDISCH_TAC `(Db0:real^3->bool) SUBSET Db` THEN
        UNDISCH_TAC `(Db:real^3->bool) SUBSET sphere(vec 0,&1)` THEN SET_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) o
          REWRITE_RULE[IN_IMAGE]) THEN
        USE_THEN "C0" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
          (ASSUME `(y:real^3) IN sch5b_circ(&0)`))) THEN
        USE_THEN "BP" (MP_TAC o SPEC `y:real^3`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN IMAGE (g:real^3->real^3) Dt0` THEN
        UNDISCH_TAC `(Dt0:real^3->bool) SUBSET Dt` THEN
        UNDISCH_TAC `(Dt:real^3->bool) SUBSET sphere(vec 0,&1)` THEN SET_TAC[]]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    REWRITE_TAC[CLOSED_STANDARD_HYPERPLANE] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    REWRITE_TAC[CLOSED_STANDARD_HYPERPLANE] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `vector[&1; &0; &0]:real^3` THEN
    REWRITE_TAC[sch5b_circ; IN_ELIM_THM; VECTOR_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[IN_DISJOINT; IN_ELIM_THM; IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    USE_THEN "C0" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(y:real^3) IN sch5b_circ(&0)`))) THEN
    SUBGOAL_THEN `(u:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(u:real^3) IN Db0` THEN UNDISCH_TAC `(Db0:real^3->bool) SUBSET Db` THEN
      UNDISCH_TAC `(Db:real^3->bool) SUBSET sphere(vec 0,&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(g':real^3->real^3)((Theta:real^3->real^3) y) IN Db0` MP_TAC THENL
     [SUBGOAL_THEN `(Theta:real^3->real^3) y = (g:real^3->real^3) u` SUBST1_TAC THENL
       [UNDISCH_TAC `(x:real^3) = (g:real^3->real^3) u` THEN
        UNDISCH_TAC `(x:real^3) = (Theta:real^3->real^3) y` THEN MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "GI" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(u:real^3) IN sphere(vec 0,&1)`)]) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "BB" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[IN_DISJOINT; IN_ELIM_THM; IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    USE_THEN "C0" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(y:real^3) IN sch5b_circ(&0)`))) THEN
    SUBGOAL_THEN `(u:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(u:real^3) IN Dt0` THEN UNDISCH_TAC `(Dt0:real^3->bool) SUBSET Dt` THEN
      UNDISCH_TAC `(Dt:real^3->bool) SUBSET sphere(vec 0,&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(g':real^3->real^3)((Theta:real^3->real^3) y) IN Dt0` MP_TAC THENL
     [SUBGOAL_THEN `(Theta:real^3->real^3) y = (g:real^3->real^3) u` SUBST1_TAC THENL
       [UNDISCH_TAC `(x:real^3) = (g:real^3->real^3) u` THEN
        UNDISCH_TAC `(x:real^3) = (Theta:real^3->real^3) y` THEN MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "GI" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(u:real^3) IN sphere(vec 0,&1)`)]) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "TB" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[IN_DISJOINT; IN_ELIM_THM; IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `(u:real^3) IN sphere(vec 0,&1) /\ (v:real^3) IN sphere(vec 0,&1)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(u:real^3) IN Db0` THEN UNDISCH_TAC `(Db0:real^3->bool) SUBSET Db` THEN
      UNDISCH_TAC `(Db:real^3->bool) SUBSET sphere(vec 0,&1)` THEN
      UNDISCH_TAC `(v:real^3) IN Dt0` THEN UNDISCH_TAC `(Dt0:real^3->bool) SUBSET Dt` THEN
      UNDISCH_TAC `(Dt:real^3->bool) SUBSET sphere(vec 0,&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^3) = v` SUBST_ALL_TAC THENL
     [USE_THEN "GI" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(u:real^3) IN sphere(vec 0,&1)`)) THEN
        MP_TAC(MATCH_MP th (ASSUME `(v:real^3) IN sphere(vec 0,&1)`))) THEN
      UNDISCH_TAC `(x:real^3) = (g:real^3->real^3) u` THEN
      UNDISCH_TAC `(x:real^3) = (g:real^3->real^3) v` THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (Db:real^3->bool) Dt` THEN
    UNDISCH_TAC `(v:real^3) IN Db0` THEN UNDISCH_TAC `(Db0:real^3->bool) SUBSET Db` THEN
    UNDISCH_TAC `(v:real^3) IN Dt0` THEN UNDISCH_TAC `(Dt0:real^3->bool) SUBSET Dt` THEN
    SET_TAC[]]);;

let SCH5S_CRIT_DISCS = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'
    Db Db0 Dt Dt0 u.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5s_bdisc g' Theta Db Db0 /\ sch5s_tdisc g' Theta Dt Dt0 /\ sch_crit g u
     ==> u IN Db0 \/ u IN Dt0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`; `Dt:real^3->bool`;
                                 `Dt0:real^3->bool`]) SCH5S_DISCS_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "COV" o SYM) THEN
  SUBGOAL_THEN `(u:real^3) IN sphere(vec 0,&1)` MP_TAC THENL
   [UNDISCH_TAC `sch_crit (g:real^3->real^3) u` THEN SIMP_TAC[sch_crit]; ALL_TAC] THEN
  USE_THEN "COV" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th]) (DISJ_CASES_THEN2
    (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) (fun th -> REWRITE_TAC[th]))) THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`y:real^3`]) SCH5S_BAND_NOT_CRIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
    UNDISCH_TAC `--(&9 / &8) <= (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 <= &9 / &8` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `sch_crit (g:real^3->real^3) u` THEN ASM_REWRITE_TAC[]);;

let SCH5S_SADDLE_SPLIT = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'
    Db Db0 Dt Dt0.
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5s_bdisc g' Theta Db Db0 /\ sch5s_tdisc g' Theta Dt Dt0 /\ sch_morse g
     ==> CARD(sch_saddles g INTER Db0) + CARD(sch_saddles g INTER Dt0) =
         CARD(sch_saddles g) /\
         IMAGE g (sch_saddles g INTER Db0) UNION IMAGE g (sch_saddles g INTER Dt0) =
         IMAGE g (sch_saddles g) /\
         DISJOINT (IMAGE g (sch_saddles g INTER Db0)) (IMAGE g (sch_saddles g INTER Dt0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`; `Dt:real^3->bool`;
                                 `Dt0:real^3->bool`]) SCH5S_DISCS_DISJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `DISJOINT (Db0:real^3->bool) Dt0` ASSUME_TAC THENL
   [UNDISCH_TAC `sch5s_bdisc (g':real^3->real^3) (Theta:real^3->real^3) Db Db0` THEN
    UNDISCH_TAC `sch5s_tdisc (g':real^3->real^3) (Theta:real^3->real^3) Dt Dt0` THEN
    UNDISCH_TAC `DISJOINT (Db:real^3->bool) Dt` THEN
    REWRITE_TAC[sch5s_bdisc; sch5s_tdisc] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. u IN sch_saddles (g:real^3->real^3) ==> u IN Db0 \/ u IN Dt0` ASSUME_TAC THENL
   [REWRITE_TAC[sch_saddles; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SCH5S_CRIT_DISCS THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                          `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                          `Theta':real^3->real^3`; `Db:real^3->bool`; `Dt:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(sch_saddles (g:real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t | sch_crit (g:real^3->real^3) t}` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `sch_morse (g:real^3->real^3)` THEN SIMP_TAC[sch_morse];
      REWRITE_TAC[sch_saddles; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v. u IN sphere(vec 0,&1) /\ v IN sphere(vec 0,&1) /\
                      (g:real^3->real^3) u = g v ==> u = v` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `u:real^3`] SCH5_NECK_FACTS) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `v:real^3`] SCH5_NECK_FACTS) THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[sch5b_pancake] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "sch5b_pancake" with Failure _ -> false)) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_saddles (g:real^3->real^3) SUBSET sphere(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[sch_saddles; sch_crit; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (Db0:real^3->bool) Dt0` THEN
    UNDISCH_TAC `!u. u IN sch_saddles (g:real^3->real^3) ==> u IN Db0 \/ u IN Dt0` THEN
    SET_TAC[];
    REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `!u. u IN sch_saddles (g:real^3->real^3) ==> u IN Db0 \/ u IN Dt0` THEN
    SET_TAC[];
    REWRITE_TAC[IN_DISJOINT; IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(u:real^3) = v` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!u v. u IN sphere(vec 0,&1) /\ v IN sphere(vec 0,&1) /\ (g:real^3->real^3) u = g v
               ==> u = v`) (concl th))) THEN
      UNDISCH_TAC `(x:real^3) = (g:real^3->real^3) u` THEN
      UNDISCH_TAC `(x:real^3) = (g:real^3->real^3) v` THEN
      UNDISCH_TAC `(u:real^3) IN sch_saddles g` THEN UNDISCH_TAC `(v:real^3) IN sch_saddles g` THEN
      UNDISCH_TAC `sch_saddles (g:real^3->real^3) SUBSET sphere(vec 0,&1)` THEN SET_TAC[];
      UNDISCH_TAC `DISJOINT (Db0:real^3->bool) Dt0` THEN UNDISCH_TAC `(v:real^3) IN Db0` THEN
      UNDISCH_TAC `(v:real^3) IN Dt0` THEN SET_TAC[]]]);;

let SCH5S_NECK_INJ = prove
 (`!(g:real^3->real^3) g' u v.
     sch_neck g g' /\ u IN sphere(vec 0,&1) /\ v IN sphere(vec 0,&1) /\ g u = g v ==> u = v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `u:real^3`] SCH5_NECK_FACTS) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `v:real^3`] SCH5_NECK_FACTS) THEN
  ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN ASM_MESON_TAC[]);;

let SCH5S_POLES_OFF = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch5b_pancake g g' a lam c c' Theta Theta'
     ==> ~(Theta(vector[&0; &0; --(&1 / &2)]) IN IMAGE g (sphere(vec 0,&1))) /\
         ~(Theta(vector[&0; &0; &1 / &2]) IN IMAGE g (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN sch5s_pancake_tac THEN CONJ_TAC THENL
   [USE_THEN "SIFF" (MP_TAC o SPEC `vector[&0; &0; --(&1 / &2)]:real^3`);
    USE_THEN "SIFF" (MP_TAC o SPEC `vector[&0; &0; &1 / &2]:real^3`)] THEN
  REWRITE_TAC[sch5v_slab; IN_ELIM_THM; VECTOR_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[]);;

let SCH5S_CRIT_EXCL = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'
    Db Db0 Dt Dt0 (g1:real^3->real^3) (g2:real^3->real^3).
     sch5b_pancake g g' a lam c c' Theta Theta' /\
     sch5s_bdisc g' Theta Db Db0 /\ sch5s_tdisc g' Theta Dt Dt0 /\
     (!t. sch_crit g1 t
          ==> t = basis 3 /\ g1 t = Theta(vector[&0; &0; --(&1 / &2)]) \/
              (?u. u IN Db0 /\ sch_crit g u /\ g1 t = g u)) /\
     (!u. u IN Db0 /\ sch_crit g u ==> ?t. sch_crit g1 t /\ g1 t = g u) /\
     (!t. sch_crit g2 t
          ==> t = --(basis 3) /\ g2 t = Theta(vector[&0; &0; &1 / &2]) \/
              (?u. u IN Dt0 /\ sch_crit g u /\ g2 t = g u)) /\
     (!u. u IN Dt0 /\ sch_crit g u ==> ?t. sch_crit g2 t /\ g2 t = g u)
     ==> (!t. sch_crit g1 t
              ==> t = basis 3 /\ g1 t = Theta(vector[&0; &0; --(&1 / &2)]) \/
                  (?u. sch_crit g u /\ g1 t = g u)) /\
         (!t. sch_crit g2 t
              ==> t = --(basis 3) /\ g2 t = Theta(vector[&0; &0; &1 / &2]) \/
                  (?u. sch_crit g u /\ g2 t = g u)) /\
         (!u. sch_crit g u
              ==> ((?t. sch_crit g1 t /\ g1 t = g u) <=> ~(?t. sch_crit g2 t /\ g2 t = g u)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "C1") (CONJUNCTS_THEN2 (LABEL_TAC "D1")
    (CONJUNCTS_THEN2 (LABEL_TAC "C2") (LABEL_TAC "D2"))))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "C1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `sch_crit (g1:real^3->real^3) t`))) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "C2" (fun th -> MP_TAC(MATCH_MP th (ASSUME `sch_crit (g2:real^3->real^3) t`))) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(u:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_crit (g:real^3->real^3) u` THEN SIMP_TAC[sch_crit]; ALL_TAC] THEN
  SUBGOAL_THEN `sch_neck (g:real^3->real^3) g'` ASSUME_TAC THENL
   [ASM_MESON_TAC[sch5b_pancake]; ALL_TAC] THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5S_POLES_OFF) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^3->real^3) u IN IMAGE g (sphere(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (Db0:real^3->bool) Dt0` ASSUME_TAC THENL
   [MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`; `Dt:real^3->bool`;
                                   `Dt0:real^3->bool`]) SCH5S_DISCS_DISJ) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sch5s_bdisc (g':real^3->real^3) (Theta:real^3->real^3) Db Db0` THEN
    UNDISCH_TAC `sch5s_tdisc (g':real^3->real^3) (Theta:real^3->real^3) Dt Dt0` THEN
    REWRITE_TAC[sch5s_bdisc; sch5s_tdisc] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Db0:real^3->bool) SUBSET sphere(vec 0,&1) /\ (Dt0:real^3->bool) SUBSET sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sch5s_bdisc (g':real^3->real^3) (Theta:real^3->real^3) Db Db0` THEN
    UNDISCH_TAC `sch5s_tdisc (g':real^3->real^3) (Theta:real^3->real^3) Dt Dt0` THEN
    REWRITE_TAC[sch5s_bdisc; sch5s_tdisc] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?t. sch_crit (g1:real^3->real^3) t /\ g1 t = (g:real^3->real^3) u) ==> u IN Db0`
  ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "C1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `sch_crit (g1:real^3->real^3) t`))) THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `~((Theta:real^3->real^3)(vector[&0; &0; --(&1 / &2)]) IN
                    IMAGE (g:real^3->real^3) (sphere(vec 0,&1)))` THEN
      UNDISCH_TAC `(g1:real^3->real^3) t = (Theta:real^3->real^3)(vector[&0; &0; --(&1 / &2)])` THEN
      UNDISCH_TAC `(g1:real^3->real^3) t = (g:real^3->real^3) u` THEN
      UNDISCH_TAC `(g:real^3->real^3) u IN IMAGE g (sphere(vec 0,&1))` THEN MESON_TAC[];
      SUBGOAL_THEN `(u:real^3) = u'` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC SCH5S_NECK_INJ THEN
      MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?t. sch_crit (g2:real^3->real^3) t /\ g2 t = (g:real^3->real^3) u) ==> u IN Dt0`
  ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "C2" (fun th -> MP_TAC(MATCH_MP th (ASSUME `sch_crit (g2:real^3->real^3) t`))) THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `~((Theta:real^3->real^3)(vector[&0; &0; &1 / &2]) IN
                    IMAGE (g:real^3->real^3) (sphere(vec 0,&1)))` THEN
      UNDISCH_TAC `(g2:real^3->real^3) t = (Theta:real^3->real^3)(vector[&0; &0; &1 / &2])` THEN
      UNDISCH_TAC `(g2:real^3->real^3) t = (g:real^3->real^3) u` THEN
      UNDISCH_TAC `(g:real^3->real^3) u IN IMAGE g (sphere(vec 0,&1))` THEN MESON_TAC[];
      SUBGOAL_THEN `(u:real^3) = u'` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC SCH5S_NECK_INJ THEN
      MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`; `Dt:real^3->bool`;
                                 `Dt0:real^3->bool`; `u:real^3`]) SCH5S_CRIT_DISCS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [USE_THEN "D1" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(u:real^3) IN Db0`) (ASSUME `sch_crit (g:real^3->real^3) u`)))) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(?t. sch_crit (g2:real^3->real^3) t /\ g2 t = (g:real^3->real^3) u)
                 ==> u IN Dt0` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `DISJOINT (Db0:real^3->bool) Dt0` THEN UNDISCH_TAC `(u:real^3) IN Db0` THEN
    UNDISCH_TAC `(u:real^3) IN Dt0` THEN SET_TAC[];
    USE_THEN "D2" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(u:real^3) IN Dt0`) (ASSUME `sch_crit (g:real^3->real^3) u`)))) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(?t. sch_crit (g1:real^3->real^3) t /\ g1 t = (g:real^3->real^3) u)
                 ==> u IN Db0` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `DISJOINT (Db0:real^3->bool) Dt0` THEN UNDISCH_TAC `(u:real^3) IN Db0` THEN
    UNDISCH_TAC `(u:real^3) IN Dt0` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The single cut.  From a pancake chart (with the side                      *)
(* dichotomy) at a regular level a, with a +/- lam/2 not critical values,    *)
(* the two surgered Morse necks in slab configuration with a common model    *)
(* collar e0, the saddle and component bookkeeping, and the critical points  *)
(* in image form.                                                            *)
(* ------------------------------------------------------------------------- *)

let rec sch5s_labels ls =
  match ls with
    [l] -> LABEL_TAC l
  | l::t -> CONJUNCTS_THEN2 (LABEL_TAC l) (sch5s_labels t)
  | [] -> failwith "sch5s_labels";;

let SCH5S_CUT_PRE = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch5b_pancake g g' a lam c c' Theta Theta' /\ sch_morse g /\
     (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     (!t. sch_crit g t ==> ~((g t)$3 = a + lam / &2) /\ ~((g t)$3 = a - lam / &2)) /\
     FINITE(components(sch_level g a)) /\
     ((!y. y IN sch5v_slab(&3 / &2)
           ==> (Theta y IN inside(IMAGE g (sphere(vec 0,&1))) <=>
                y$1 pow 2 + y$2 pow 2 < &1)) \/
      (!y. y IN sch5v_slab(&3 / &2)
           ==> (Theta y IN outside(IMAGE g (sphere(vec 0,&1))) <=>
                y$1 pow 2 + y$2 pow 2 < &1)))
     ==> ?g1 g1' e1 g2 g2' e2.
           sch_neck g1 g1' /\ sch_morse g1 /\ sch_neck g2 g2' /\ sch_morse g2 /\
           (!t. sch_crit g1 t ==> ~((g1 t)$3 = a)) /\
           (!t. sch_crit g2 t ==> ~((g2 t)$3 = a)) /\
           sch_slab_config (IMAGE g (sphere(vec 0,&1))) (IMAGE g1 (sphere(vec 0,&1)))
                           (IMAGE g2 (sphere(vec 0,&1))) Theta /\
           &0 < e1 /\ e1 <= &1 / &16 /\ &0 < e2 /\ e2 <= &1 / &16 /\
           (!x. x IN sch_capcone ==> g1 x = Theta(sch_cap_collar e1 x)) /\
           (!x. x IN sch_capcone ==> g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e2 x))) /\
           CARD(sch_saddles g1) + CARD(sch_saddles g2) = CARD(sch_saddles g) /\
           IMAGE g1 (sch_saddles g1) UNION IMAGE g2 (sch_saddles g2) = IMAGE g (sch_saddles g) /\
           DISJOINT (IMAGE g1 (sch_saddles g1)) (IMAGE g2 (sch_saddles g2)) /\
           CARD(components(sch_level g1 a)) + CARD(components(sch_level g2 a)) + 1 =
           CARD(components(sch_level g a)) /\
           (!t. sch_crit g1 t
                ==> t = basis 3 /\ g1 t = Theta(vector[&0; &0; --(&1 / &2)]) \/
                    (?u. sch_crit g u /\ g1 t = g u)) /\
           (!t. sch_crit g2 t
                ==> t = --(basis 3) /\ g2 t = Theta(vector[&0; &0; &1 / &2]) \/
                    (?u. sch_crit g u /\ g2 t = g u)) /\
           (!u. sch_crit g u
                ==> ((?t. sch_crit g1 t /\ g1 t = g u) <=> ~(?t. sch_crit g2 t /\ g2 t = g u)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SIDES")))))) THEN
  SUBGOAL_THEN `(!t. sch_crit (g:real^3->real^3) t ==> ~((g t)$3 = a + lam / &2)) /\
                (!t. sch_crit g t ==> ~((g t)$3 = a - lam / &2))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5S_BOTTOM2) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `Db:real^3->bool` (X_CHOOSE_THEN `Db0:real^3->bool`
    (sch5s_labels ["BN";"BM";"BCH";"BE0";"BE1";"BCAP";"BDISC";"BIM";"BCARD";"BSAD";"BLEV";
                   "BIMS";"BCR1";"BCR2"])))))) THEN
  MP_TAC(ISPECL sch5b_bvars8 SCH5S_TOP2) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^3->real^3` (X_CHOOSE_THEN `g2':real^3->real^3`
    (X_CHOOSE_THEN `e2:real` (X_CHOOSE_THEN `Dt:real^3->bool` (X_CHOOSE_THEN `Dt0:real^3->bool`
    (sch5s_labels ["TN";"TM";"TCH";"TE0";"TE1";"TCAP";"TDISC";"TIM";"TCARD";"TSAD";"TLEV";
                   "TIMS";"TCR1";"TCR2"])))))) THEN
  SUBGOAL_THEN `sch_slab_config (IMAGE (g:real^3->real^3) (sphere(vec 0,&1)))
                  (IMAGE (g1:real^3->real^3) (sphere(vec 0,&1)))
                  (IMAGE (g2:real^3->real^3) (sphere(vec 0,&1))) Theta` ASSUME_TAC THENL
   [USE_THEN "BIM" SUBST1_TAC THEN USE_THEN "TIM" SUBST1_TAC THEN
    MATCH_MP_TAC SCH5S_SLAB_CONFIG THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `a:real`; `lam:real`; `c:real^2->real^2`;
                          `c':real^2->real^2`; `Theta':real^3->real^3`; `Db0:real^3->bool`;
                          `Dt0:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`; `Dt:real^3->bool`;
                                 `Dt0:real^3->bool`]) SCH5S_SADDLE_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SS1") (CONJUNCTS_THEN2 (LABEL_TAC "SS2")
    (LABEL_TAC "SS3"))) THEN
  SUBGOAL_THEN `CARD(sch_saddles (g1:real^3->real^3)) + CARD(sch_saddles (g2:real^3->real^3)) =
                CARD(sch_saddles (g:real^3->real^3))` ASSUME_TAC THENL
   [USE_THEN "BCARD" SUBST1_TAC THEN USE_THEN "TCARD" SUBST1_TAC THEN
    USE_THEN "SS1" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g1:real^3->real^3) (sch_saddles g1) UNION
                IMAGE (g2:real^3->real^3) (sch_saddles g2) =
                IMAGE (g:real^3->real^3) (sch_saddles g) /\
                DISJOINT (IMAGE g1 (sch_saddles g1)) (IMAGE g2 (sch_saddles g2))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "BIMS" SUBST1_TAC THEN USE_THEN "TIMS" SUBST1_TAC THEN
    CONJ_TAC THENL [USE_THEN "SS2" ACCEPT_TAC; USE_THEN "SS3" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(components(sch_level (g1:real^3->real^3) a)) +
                CARD(components(sch_level (g2:real^3->real^3) a)) + 1 =
                CARD(components(sch_level (g:real^3->real^3) a))` ASSUME_TAC THENL
   [USE_THEN "BLEV" SUBST1_TAC THEN USE_THEN "TLEV" SUBST1_TAC THEN
    MATCH_MP_TAC SCH5S_COMPONENTS_COUNT THEN
    EXISTS_TAC `IMAGE (Theta:real^3->real^3) (sch5b_circ(&0))` THEN
    MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`; `Dt:real^3->bool`;
                                   `Dt0:real^3->bool`]) SCH5S_LEVEL_PIECES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL (sch5b_bvars8 @ [`Db:real^3->bool`; `Db0:real^3->bool`; `Dt:real^3->bool`;
                                 `Dt0:real^3->bool`; `g1:real^3->real^3`; `g2:real^3->real^3`])
    SCH5S_CRIT_EXCL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`g1:real^3->real^3`; `g1':real^3->real^3`; `e1:real`;
                        `g2:real^3->real^3`; `g2':real^3->real^3`; `e2:real`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* A common collar parameter by radial compression of both necks.           *)

let SCH5S_COMMON_COLLAR = prove
 (`!(g1:real^3->real^3) g1' (g2:real^3->real^3) g2' e1 e2 (Theta:real^3->real^3).
     sch_neck g1 g1' /\ sch_neck g2 g2' /\
     &0 < e1 /\ e1 <= &1 / &16 /\ &0 < e2 /\ e2 <= &1 / &16 /\
     (!x. x IN sch_capcone ==> g1 x = Theta(sch_cap_collar e1 x)) /\
     (!x. x IN sch_capcone ==> g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e2 x)))
     ==> ?h1 h1' h2 h2' e0.
           sch_neck h1 h1' /\ sch_neck h2 h2' /\ &0 < e0 /\ e0 <= &1 / &16 /\
           (!x. x IN sch_capcone
                ==> h1 x = Theta(sch_cap_collar e0 x) /\
                    h2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x))) /\
           (!t. t IN sphere(vec 0,&1) ==> h1 t = g1 t /\ h2 t = g2 t) /\
           IMAGE h1 (sphere(vec 0,&1)) = IMAGE g1 (sphere(vec 0,&1)) /\
           IMAGE h2 (sphere(vec 0,&1)) = IMAGE g2 (sphere(vec 0,&1)) /\
           (!t. sch_crit h1 t <=> sch_crit g1 t) /\ (!t. sch_crit h2 t <=> sch_crit g2 t) /\
           sch_saddles h1 = sch_saddles g1 /\ sch_saddles h2 = sch_saddles g2 /\
           (sch_morse h1 <=> sch_morse g1) /\ (sch_morse h2 <=> sch_morse g2) /\
           (!a. sch_level h1 a = sch_level g1 a) /\ (!a. sch_level h2 a = sch_level g2 a)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(sch5s_labels ["N1";"N2";"E10";"E11";"E20";"E21";"C1";"C2"]) THEN
  ABBREV_TAC `e0 = min e1 e2 / &4` THEN
  SUBGOAL_THEN `&0 < e0 /\ e0 <= &1 / &16 /\ e0 <= e1 / &4 /\ e0 <= e2 / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e0" THEN UNDISCH_TAC `&0 < e1` THEN UNDISCH_TAC `e1 <= &1 / &16` THEN
    UNDISCH_TAC `&0 < e2` THEN UNDISCH_TAC `e2 <= &1 / &16` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e0 / e1 /\ e0 / e1 <= &1 / &4 /\ e1 * e0 / e1 = e0 /\
                &0 < e0 / e2 /\ e0 / e2 <= &1 / &4 /\ e2 * e0 / e2 = e0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    UNDISCH_TAC `e0 <= e1 / &4` THEN UNDISCH_TAC `e0 <= e2 / &4` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g1:real^3->real^3`; `g1':real^3->real^3`; `e0 / e1`] SCH5S_SHRINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(sch5s_labels ["H1N";"H1V";"H1I";"H1C";"H1S";"H1M";"H1L"]) THEN
  MP_TAC(ISPECL [`g2:real^3->real^3`; `g2':real^3->real^3`; `e0 / e2`] SCH5S_SHRINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(sch5s_labels ["H2N";"H2V";"H2I";"H2C";"H2S";"H2M";"H2L"]) THEN
  MAP_EVERY EXISTS_TAC [`(g1:real^3->real^3) o sch5_radial(e0 / e1)`;
                        `sch5_radinv(e0 / e1) o (g1':real^3->real^3)`;
                        `(g2:real^3->real^3) o sch5_radial(e0 / e2)`;
                        `sch5_radinv(e0 / e2) o (g2':real^3->real^3)`; `e0:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`Theta:real^3->real^3`; `e1:real`; `e0 / e1`; `x:real^3`] SCH5S_SHRINK_CAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`Theta:real^3->real^3`; `e2:real`; `e0 / e2`; `x:real^3`] SCH5S_SHRINK_CAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "C1" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `sch5_radial (e0 / e1) x IN sch_capcone`)]) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      USE_THEN "C2" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `sch5_radial (e0 / e2) x IN sch_capcone`)]) THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "H1V" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "H2V" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

let SCH5S_CUT_CORE = prove
 (`!(g:real^3->real^3) g' a lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch5b_pancake g g' a lam c c' Theta Theta' /\ sch_morse g /\
     (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     (!t. sch_crit g t ==> ~((g t)$3 = a + lam / &2) /\ ~((g t)$3 = a - lam / &2)) /\
     FINITE(components(sch_level g a)) /\
     ((!y. y IN sch5v_slab(&3 / &2)
           ==> (Theta y IN inside(IMAGE g (sphere(vec 0,&1))) <=>
                y$1 pow 2 + y$2 pow 2 < &1)) \/
      (!y. y IN sch5v_slab(&3 / &2)
           ==> (Theta y IN outside(IMAGE g (sphere(vec 0,&1))) <=>
                y$1 pow 2 + y$2 pow 2 < &1)))
     ==> ?g1 g1' g2 g2' e0.
           sch_neck g1 g1' /\ sch_morse g1 /\ sch_neck g2 g2' /\ sch_morse g2 /\
           (!t. sch_crit g1 t ==> ~((g1 t)$3 = a)) /\
           (!t. sch_crit g2 t ==> ~((g2 t)$3 = a)) /\
           sch_slab_config (IMAGE g (sphere(vec 0,&1))) (IMAGE g1 (sphere(vec 0,&1)))
                           (IMAGE g2 (sphere(vec 0,&1))) Theta /\
           &0 < e0 /\ e0 <= &1 / &16 /\
           (!x. x IN sch_capcone
                ==> g1 x = Theta(sch_cap_collar e0 x) /\
                    g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x))) /\
           CARD(sch_saddles g1) + CARD(sch_saddles g2) = CARD(sch_saddles g) /\
           IMAGE g1 (sch_saddles g1) UNION IMAGE g2 (sch_saddles g2) = IMAGE g (sch_saddles g) /\
           DISJOINT (IMAGE g1 (sch_saddles g1)) (IMAGE g2 (sch_saddles g2)) /\
           CARD(components(sch_level g1 a)) + CARD(components(sch_level g2 a)) + 1 =
           CARD(components(sch_level g a)) /\
           (!t. sch_crit g1 t
                ==> t = basis 3 /\ g1 t = Theta(vector[&0; &0; --(&1 / &2)]) \/
                    (?u. sch_crit g u /\ g1 t = g u)) /\
           (!t. sch_crit g2 t
                ==> t = --(basis 3) /\ g2 t = Theta(vector[&0; &0; &1 / &2]) \/
                    (?u. sch_crit g u /\ g2 t = g u)) /\
           (!u. sch_crit g u
                ==> ((?t. sch_crit g1 t /\ g1 t = g u) <=> ~(?t. sch_crit g2 t /\ g2 t = g u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCH5S_CUT_PRE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^3->real^3` (X_CHOOSE_THEN `k1':real^3->real^3`
    (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `k2:real^3->real^3` (X_CHOOSE_THEN `k2':real^3->real^3`
    (X_CHOOSE_THEN `e2:real`
    (sch5s_labels ["N1";"M1";"N2";"M2";"CH1";"CH2";"SL";"E10";"E11";"E20";"E21";"C1";"C2";
                   "CARD";"IMS";"DIS";"COMP";"R1";"R2";"R3"]))))))) THEN
  MP_TAC(ISPECL [`k1:real^3->real^3`; `k1':real^3->real^3`; `k2:real^3->real^3`;
                 `k2':real^3->real^3`; `e1:real`; `e2:real`; `Theta:real^3->real^3`]
    SCH5S_COMMON_COLLAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^3->real^3` (X_CHOOSE_THEN `h1':real^3->real^3`
    (X_CHOOSE_THEN `h2:real^3->real^3` (X_CHOOSE_THEN `h2':real^3->real^3`
    (X_CHOOSE_THEN `e0:real`
    (sch5s_labels ["HN1";"HN2";"HE0";"HE1";"HC";"HV";"HI1";"HI2";"HCR1";"HCR2";"HS1";"HS2";
                   "HM1";"HM2";"HL1";"HL2"])))))) THEN
  SUBGOAL_THEN `(!t. sch_crit (h1:real^3->real^3) t ==> h1 t = (k1:real^3->real^3) t) /\
                (!t. sch_crit (h2:real^3->real^3) t ==> h2 t = (k2:real^3->real^3) t)`
  (CONJUNCTS_THEN2 (LABEL_TAC "HV1") (LABEL_TAC "HV2")) THENL
   [CONJ_TAC THEN X_GEN_TAC `t:real^3` THEN REWRITE_TAC[sch_crit] THEN STRIP_TAC THEN
    USE_THEN "HV" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(t:real^3) IN sphere(vec 0,&1)`)]);
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h1:real^3->real^3) (sch_saddles h1) = IMAGE (k1:real^3->real^3) (sch_saddles k1) /\
                IMAGE (h2:real^3->real^3) (sch_saddles h2) = IMAGE (k2:real^3->real^3) (sch_saddles k2)`
  (CONJUNCTS_THEN2 (LABEL_TAC "HIS1") (LABEL_TAC "HIS2")) THENL
   [CONJ_TAC THENL
     [USE_THEN "HS1" SUBST1_TAC THEN MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> (f:real^3->real^3) x = (h:real^3->real^3) x) ==> IMAGE f s = IMAGE h s`) THEN
      X_GEN_TAC `t:real^3` THEN REWRITE_TAC[sch_saddles; IN_ELIM_THM] THEN STRIP_TAC THEN
      USE_THEN "HV1" MATCH_MP_TAC THEN USE_THEN "HCR1" (fun th -> REWRITE_TAC[th]) THEN
      FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "HS2" SUBST1_TAC THEN MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> (f:real^3->real^3) x = (h:real^3->real^3) x) ==> IMAGE f s = IMAGE h s`) THEN
      X_GEN_TAC `t:real^3` THEN REWRITE_TAC[sch_saddles; IN_ELIM_THM] THEN STRIP_TAC THEN
      USE_THEN "HV2" MATCH_MP_TAC THEN USE_THEN "HCR2" (fun th -> REWRITE_TAC[th]) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`h1:real^3->real^3`; `h1':real^3->real^3`; `h2:real^3->real^3`;
                        `h2':real^3->real^3`; `e0:real`] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "HN1" ACCEPT_TAC;
    USE_THEN "HM1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "M1" ACCEPT_TAC;
    USE_THEN "HN2" ACCEPT_TAC;
    USE_THEN "HM2" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "M2" ACCEPT_TAC;
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "HV1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `sch_crit (h1:real^3->real^3) t`)]) THEN
    USE_THEN "CH1" MATCH_MP_TAC THEN
    USE_THEN "HCR1" (fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "HV2" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `sch_crit (h2:real^3->real^3) t`)]) THEN
    USE_THEN "CH2" MATCH_MP_TAC THEN
    USE_THEN "HCR2" (fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "HI1" SUBST1_TAC THEN USE_THEN "HI2" SUBST1_TAC THEN USE_THEN "SL" ACCEPT_TAC;
    USE_THEN "HE0" ACCEPT_TAC;
    USE_THEN "HE1" ACCEPT_TAC;
    USE_THEN "HC" ACCEPT_TAC;
    USE_THEN "HS1" SUBST1_TAC THEN USE_THEN "HS2" SUBST1_TAC THEN USE_THEN "CARD" ACCEPT_TAC;
    USE_THEN "HIS1" SUBST1_TAC THEN USE_THEN "HIS2" SUBST1_TAC THEN USE_THEN "IMS" ACCEPT_TAC;
    USE_THEN "HIS1" SUBST1_TAC THEN USE_THEN "HIS2" SUBST1_TAC THEN USE_THEN "DIS" ACCEPT_TAC;
    USE_THEN "HL1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "HL2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "COMP" ACCEPT_TAC;
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "HV1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `sch_crit (h1:real^3->real^3) t`)]) THEN
    USE_THEN "R1" MATCH_MP_TAC THEN
    USE_THEN "HCR1" (fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "HV2" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `sch_crit (h2:real^3->real^3) t`)]) THEN
    USE_THEN "R2" MATCH_MP_TAC THEN
    USE_THEN "HCR2" (fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `((?t. sch_crit (h1:real^3->real^3) t /\ h1 t = (g:real^3->real^3) u) <=>
                   (?t. sch_crit (k1:real^3->real^3) t /\ k1 t = g u))` SUBST1_TAC THENL
     [USE_THEN "HCR1" (fun th1 -> USE_THEN "HV1" (fun th2 -> MP_TAC(CONJ th1 th2))) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `((?t. sch_crit (h2:real^3->real^3) t /\ h2 t = (g:real^3->real^3) u) <=>
                   (?t. sch_crit (k2:real^3->real^3) t /\ k2 t = g u))` SUBST1_TAC THENL
     [USE_THEN "HCR2" (fun th1 -> USE_THEN "HV2" (fun th2 -> MP_TAC(CONJ th1 th2))) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "R3" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The single cut in two forms. SCH5S_SINGLE_CUT_CHART takes the pancake     *)
(* chart as a hypothesis (on any sch5v_slab H with 3/2 <= H);                *)
(* SCH5S_SINGLE_CUT builds it with SCH5V_PANCAKE for an innermost component  *)
(* C of a regular level.                                                     *)
(* ------------------------------------------------------------------------- *)

let SCH5S_SINGLE_CUT_CHART = prove
 (`!(g:real^3->real^3) g' a H lam (c:real^2->real^2) c' (Theta:real^3->real^3) Theta'.
     sch_neck g g' /\ sch_morse g /\ (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     FINITE(components(sch_level g a)) /\
     sch_ball c c' /\ &3 / &2 <= H /\ &0 < lam /\
     (!t. sch_crit g t ==> ~((g t)$3 = a + lam / &2) /\ ~((g t)$3 = a - lam / &2)) /\
     diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H)) Theta Theta' /\
     (!y. y IN sch5v_slab H ==> (Theta y)$3 = a + lam * y$3) /\
     (!y. y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1 / &4
          ==> Theta y = sch5v_at (a + lam * y$3) (c(sch5v_pr y))) /\
     (!y. y IN sch5v_slab H
          ==> (Theta y IN IMAGE g (sphere(vec 0,&1)) <=> y$1 pow 2 + y$2 pow 2 = &1)) /\
     ((!y. y IN sch5v_slab H
           ==> (Theta y IN inside(IMAGE g (sphere(vec 0,&1))) <=>
                y$1 pow 2 + y$2 pow 2 < &1)) \/
      (!y. y IN sch5v_slab H
           ==> (Theta y IN outside(IMAGE g (sphere(vec 0,&1))) <=>
                y$1 pow 2 + y$2 pow 2 < &1)))
     ==> ?g1 g1' g2 g2' e0.
           sch_neck g1 g1' /\ sch_morse g1 /\ sch_neck g2 g2' /\ sch_morse g2 /\
           (!t. sch_crit g1 t ==> ~((g1 t)$3 = a)) /\
           (!t. sch_crit g2 t ==> ~((g2 t)$3 = a)) /\
           sch_slab_config (IMAGE g (sphere(vec 0,&1))) (IMAGE g1 (sphere(vec 0,&1)))
                           (IMAGE g2 (sphere(vec 0,&1))) Theta /\
           &0 < e0 /\ e0 <= &1 / &16 /\
           (!x. x IN sch_capcone
                ==> g1 x = Theta(sch_cap_collar e0 x) /\
                    g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x))) /\
           CARD(sch_saddles g1) + CARD(sch_saddles g2) = CARD(sch_saddles g) /\
           IMAGE g1 (sch_saddles g1) UNION IMAGE g2 (sch_saddles g2) = IMAGE g (sch_saddles g) /\
           DISJOINT (IMAGE g1 (sch_saddles g1)) (IMAGE g2 (sch_saddles g2)) /\
           CARD(components(sch_level g1 a)) + CARD(components(sch_level g2 a)) + 1 =
           CARD(components(sch_level g a)) /\
           (!t. sch_crit g1 t
                ==> t = basis 3 /\ g1 t = Theta(vector[&0; &0; --(&1 / &2)]) \/
                    (?u. sch_crit g u /\ g1 t = g u)) /\
           (!t. sch_crit g2 t
                ==> t = --(basis 3) /\ g2 t = Theta(vector[&0; &0; &1 / &2]) \/
                    (?u. sch_crit g u /\ g2 t = g u)) /\
           (!u. sch_crit g u
                ==> ((?t. sch_crit g1 t /\ g1 t = g u) <=> ~(?t. sch_crit g2 t /\ g2 t = g u)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(sch5s_labels ["GN";"GM";"REG";"FIN";"CB";"HH";"LP";"REG2";"TD";"HT";"PF";"SIFF";
                           "SIDES"]) THEN
  SUBGOAL_THEN `sch5v_slab(&3 / &2) SUBSET sch5v_slab H` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; sch5v_slab; IN_ELIM_THM] THEN UNDISCH_TAC `&3 / &2 <= H` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sch5v_slab(&3 / &2) ==> y IN sch5v_slab H` (LABEL_TAC "SUB") THENL
   [UNDISCH_TAC `sch5v_slab(&3 / &2) SUBSET sch5v_slab H` THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCH5S_CUT_CORE) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[sch5b_pancake] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "GN" ACCEPT_TAC;
      USE_THEN "LP" ACCEPT_TAC;
      USE_THEN "CB" ACCEPT_TAC;
      MATCH_MP_TAC SCH5_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`sch5v_slab H`; `IMAGE (Theta:real^3->real^3) (sch5v_slab H)`] THEN
      ASM_REWRITE_TAC[SCH5V_SLAB_FACTS];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "HT" MATCH_MP_TAC THEN
      USE_THEN "SUB" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN USE_THEN "PF" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "SUB" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "SIFF" MATCH_MP_TAC THEN
      USE_THEN "SUB" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    USE_THEN "GM" ACCEPT_TAC;
    USE_THEN "REG" ACCEPT_TAC;
    USE_THEN "REG2" ACCEPT_TAC;
    USE_THEN "FIN" ACCEPT_TAC;
    USE_THEN "SIDES" (DISJ_CASES_THEN ASSUME_TAC) THENL [DISJ1_TAC; DISJ2_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "SUB" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let SCH5S_AVOID_FINITE = prove
 (`!Z lam0. FINITE Z /\ &0 < lam0 ==> ?lam. &0 < lam /\ lam < lam0 /\ ~(lam IN Z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(!lam. &0 < lam /\ lam < lam0 ==> lam IN Z)` MP_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `INFINITE (IMAGE (\n:num. lam0 / (&n + &2)) (:num))` MP_TAC THENL
     [MP_TAC(ISPEC `\n:num. lam0 / (&n + &2)` INFINITE_IMAGE_INJ) THEN REWRITE_TAC[] THEN
      ANTS_TAC THENL [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[num_INFINITE]] THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&m + &2 = &n + &2` MP_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD
          `&0 < lam0 /\ &0 < x /\ &0 < y /\ lam0 / x = lam0 / y ==> x = y`) THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `m:num` REAL_POS) THEN MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_EQ_ADD_RCANCEL; REAL_OF_NUM_EQ]];
      ALL_TAC] THEN
    REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `Z:real->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `x:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `&1 < &n + &2` ASSUME_TAC THENL
     [MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &n + &2` ASSUME_TAC THENL
     [UNDISCH_TAC `&1 < &n + &2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    MESON_TAC[]]);;

let SCH5S_SINGLE_CUT = prove
 (`!(g:real^3->real^3) g' a C (Fn:real^2->real^2) Fn'.
     sch_neck g g' /\ sch_morse g /\ (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     C IN components(sch_level g a) /\ FINITE(components(sch_level g a)) /\
     sch_neck Fn Fn' /\
     C = IMAGE (\x. vector[(Fn x)$1; (Fn x)$2; a]:real^3) (sphere(vec 0,&1)) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; a]:real^3) IN IMAGE g (sphere(vec 0,&1))))
     ==> ?g1 g1' g2 g2' (Theta:real^3->real^3) e0.
           sch_neck g1 g1' /\ sch_morse g1 /\ sch_neck g2 g2' /\ sch_morse g2 /\
           (!t. sch_crit g1 t ==> ~((g1 t)$3 = a)) /\
           (!t. sch_crit g2 t ==> ~((g2 t)$3 = a)) /\
           sch_slab_config (IMAGE g (sphere(vec 0,&1))) (IMAGE g1 (sphere(vec 0,&1)))
                           (IMAGE g2 (sphere(vec 0,&1))) Theta /\
           &0 < e0 /\ e0 <= &1 / &16 /\
           (!x. x IN sch_capcone
                ==> g1 x = Theta(sch_cap_collar e0 x) /\
                    g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x))) /\
           CARD(sch_saddles g1) + CARD(sch_saddles g2) = CARD(sch_saddles g) /\
           IMAGE g1 (sch_saddles g1) UNION IMAGE g2 (sch_saddles g2) = IMAGE g (sch_saddles g) /\
           DISJOINT (IMAGE g1 (sch_saddles g1)) (IMAGE g2 (sch_saddles g2)) /\
           CARD(components(sch_level g1 a)) + CARD(components(sch_level g2 a)) + 1 =
           CARD(components(sch_level g a)) /\
           (!t. sch_crit g1 t
                ==> t = basis 3 /\ g1 t = Theta(vector[&0; &0; --(&1 / &2)]) \/
                    (?u. sch_crit g u /\ g1 t = g u)) /\
           (!t. sch_crit g2 t
                ==> t = --(basis 3) /\ g2 t = Theta(vector[&0; &0; &1 / &2]) \/
                    (?u. sch_crit g u /\ g2 t = g u)) /\
           (!u. sch_crit g u
                ==> ((?t. sch_crit g1 t /\ g1 t = g u) <=> ~(?t. sch_crit g2 t /\ g2 t = g u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `C:real^3->bool`;
                 `Fn:real^2->real^2`; `Fn':real^2->real^2`] SCH5V_PANCAKE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->real^2` (X_CHOOSE_THEN `c':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `&3 / &2`)))))) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LAM"))) THEN
  MP_TAC(ISPECL [`IMAGE (\t:real^3. &2 * ((g:real^3->real^3) t)$3 - &2 * a) {t | sch_crit g t} UNION
                  IMAGE (\t:real^3. &2 * a - &2 * ((g:real^3->real^3) t)$3) {t | sch_crit g t}`;
                 `lam0:real`] SCH5S_AVOID_FINITE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN MATCH_MP_TAC FINITE_IMAGE THEN
    UNDISCH_TAC `sch_morse (g:real^3->real^3)` THEN SIMP_TAC[sch_morse];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "LAM" (MP_TAC o SPEC `lam:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Theta:real^3->real^3` (X_CHOOSE_THEN `Theta':real^3->real^3`
    (sch5s_labels ["TD";"HT";"T0";"PF";"SIFF";"SIDES"]))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `&3 / &2`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCH5S_SINGLE_CUT_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~((lam:real) IN
       IMAGE (\t:real^3. &2 * ((g:real^3->real^3) t)$3 - &2 * a) {t | sch_crit g t} UNION
       IMAGE (\t:real^3. &2 * a - &2 * ((g:real^3->real^3) t)$3) {t | sch_crit g t})` THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THENL
     [DISJ1_TAC; DISJ2_TAC] THEN EXISTS_TAC `t:real^3` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `g2:real^3->real^3` (X_CHOOSE_THEN `g2':real^3->real^3`
    (X_CHOOSE_THEN `e0:real` ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`g1:real^3->real^3`; `g1':real^3->real^3`; `g2:real^3->real^3`;
                        `g2':real^3->real^3`; `Theta:real^3->real^3`; `e0:real`] THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main theorem: surgery along an innermost circle of a regular level    *)
(* between two saddles.                                                      *)
(* ------------------------------------------------------------------------- *)

let SCH5_SURG_CONSTRUCT = prove
 (`SCH_LEVEL_NECK_STATEMENT /\ SCH_LEVEL_INNERMOST_STATEMENT /\ SCH_LEVEL_FINITE_STATEMENT
   ==> SCH_SURG_CONSTRUCT_STATEMENT`,
  REWRITE_TAC[SCH_LEVEL_NECK_STATEMENT; SCH_LEVEL_INNERMOST_STATEMENT;
              SCH_LEVEL_FINITE_STATEMENT; SCH_SURG_CONSTRUCT_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LN") (CONJUNCTS_THEN2 (LABEL_TAC "LI") (LABEL_TAC "LF"))) THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `t1:real^3`; `t2:real^3`;
                       `a:real`] THEN
  STRIP_TAC THEN
  USE_THEN "LF" (MP_TAC o SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `~(sch_level (g:real^3->real^3) a = {})` ASSUME_TAC THENL
   [SUBGOAL_THEN `(t1:real^3) IN sphere(vec 0,&1) /\ (t2:real^3) IN sphere(vec 0,&1)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(t1:real^3) IN sch_saddles g` THEN UNDISCH_TAC `(t2:real^3) IN sch_saddles g` THEN
      REWRITE_TAC[sch_saddles; sch_crit; IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `(g:real^3->real^3) t1`;
                   `(g:real^3->real^3) t2`; `a:real`; `3`] CONNECTED_IVT_COMPONENT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE; DIMINDEX_3; ARITH; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_3; ARITH] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        FIRST_ASSUM((fun th -> REWRITE_TAC[REWRITE_RULE[sch_neck; diffeomorphism_on] th]) o
          check (fun th -> concl th = `sch_neck (g:real^3->real^3) g'`));
        REWRITE_TAC[SUBSET; SCH5_SPHERE_IN_ANNULUS]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; sch_level; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  USE_THEN "LI" (MP_TAC o SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^3->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "LN" (MP_TAC o SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`;
                                  `C:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fn:real^2->real^2` (X_CHOOSE_THEN `Fn':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `C:real^3->bool`;
                 `Fn:real^2->real^2`; `Fn':real^2->real^2`] SCH5S_SINGLE_CUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `g2:real^3->real^3` (X_CHOOSE_THEN `g2':real^3->real^3`
    (X_CHOOSE_THEN `Theta:real^3->real^3` (X_CHOOSE_THEN `e0:real`
    (sch5s_labels ["N1";"M1";"N2";"M2";"CH1";"CH2";"SL";"E0";"E1";"COL";"CARD";"IMS";"DIS";
                   "COMP";"R1";"R2";"R3"]))))))) THEN
  SUBGOAL_THEN `FINITE(sch_saddles (g1:real^3->real^3)) /\ FINITE(sch_saddles (g2:real^3->real^3))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THENL
     [EXISTS_TAC `{t | sch_crit (g1:real^3->real^3) t}`;
      EXISTS_TAC `{t | sch_crit (g2:real^3->real^3) t}`] THEN
    REWRITE_TAC[sch_saddles; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[] THEN
    ASM_MESON_TAC[sch_morse];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`g1:real^3->real^3`; `g1':real^3->real^3`; `g2:real^3->real^3`;
                        `g2':real^3->real^3`; `Theta:real^3->real^3`] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "N1" ACCEPT_TAC;
    USE_THEN "M1" ACCEPT_TAC;
    USE_THEN "N2" ACCEPT_TAC;
    USE_THEN "M2" ACCEPT_TAC;
    USE_THEN "CH1" ACCEPT_TAC;
    USE_THEN "CH2" ACCEPT_TAC;
    USE_THEN "CARD" MP_TAC THEN ARITH_TAC;
    USE_THEN "CARD" MP_TAC THEN ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `sch_saddles (g2:real^3->real^3) = {}` ASSUME_TAC THENL
     [MP_TAC(ISPEC `sch_saddles (g2:real^3->real^3)` CARD_EQ_0) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "CARD" MP_TAC THEN
      UNDISCH_TAC `CARD(sch_saddles (g1:real^3->real^3)) = CARD(sch_saddles (g:real^3->real^3))` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (g1:real^3->real^3) (sch_saddles g1) =
                  IMAGE (g:real^3->real^3) (sch_saddles g)` ASSUME_TAC THENL
     [USE_THEN "IMS" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[IMAGE_CLAUSES; UNION_EMPTY; EMPTY_UNION;
                  ASSUME `sch_saddles (g2:real^3->real^3) = {}`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(g:real^3->real^3) t1 IN IMAGE (g1:real^3->real^3) (sch_saddles g1) /\
                    g t2 IN IMAGE g1 (sch_saddles g1)` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s1:real^3` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `s2:real^3` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`s1:real^3`; `s2:real^3`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(g:real^3->real^3) t1 = (g1:real^3->real^3) s1` THEN
      UNDISCH_TAC `(g:real^3->real^3) t2 = (g1:real^3->real^3) s2` THEN
      REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[];
      USE_THEN "COMP" MP_TAC THEN ARITH_TAC];
    DISCH_TAC THEN
    SUBGOAL_THEN `sch_saddles (g1:real^3->real^3) = {}` ASSUME_TAC THENL
     [MP_TAC(ISPEC `sch_saddles (g1:real^3->real^3)` CARD_EQ_0) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "CARD" MP_TAC THEN
      UNDISCH_TAC `CARD(sch_saddles (g2:real^3->real^3)) = CARD(sch_saddles (g:real^3->real^3))` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (g2:real^3->real^3) (sch_saddles g2) =
                  IMAGE (g:real^3->real^3) (sch_saddles g)` ASSUME_TAC THENL
     [USE_THEN "IMS" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[IMAGE_CLAUSES; UNION_EMPTY; EMPTY_UNION;
                  ASSUME `sch_saddles (g1:real^3->real^3) = {}`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(g:real^3->real^3) t1 IN IMAGE (g2:real^3->real^3) (sch_saddles g2) /\
                    g t2 IN IMAGE g2 (sch_saddles g2)` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s1:real^3` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `s2:real^3` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`s1:real^3`; `s2:real^3`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(g:real^3->real^3) t1 = (g2:real^3->real^3) s1` THEN
      UNDISCH_TAC `(g:real^3->real^3) t2 = (g2:real^3->real^3) s2` THEN
      REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[];
      USE_THEN "COMP" MP_TAC THEN ARITH_TAC];
    USE_THEN "SL" ACCEPT_TAC;
    EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[]]);;

