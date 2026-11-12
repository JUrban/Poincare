(* ========================================================================= *)
(* pc_top_sc3: a map S^3 -> M from a chart ball whose boundary sphere is    *)
(* null-homotopic outside the ball.                                          *)
(*   M7 (ATOP_S3_FROM_NULL_SPHERE_STATEMENT): the upper hemisphere of S^3    *)
(*   goes onto the closed chart ball through the vertical projection, the   *)
(*   lower hemisphere carries the null-homotopy as a cone (the time of the  *)
(*   homotopy is 1 - |x'| for x = (x',x4)); the open upper hemisphere is    *)
(*   mapped homeomorphically onto the open chart ball and nothing else is   *)
(*   mapped into it.                                                        *)
(* Depends on the library, pc_top_iface and pc_top_genpos.                  *)
(*                                                                           *)
(* Projection, lift and cone maps; the theorem.                             *)
(* ========================================================================= *)

needs "src/pc_top_iface.ml";;
needs "src/pc_top_genpos.ml";;

prioritize_real();;
type_invention_error := true;;

let sc3_proj = new_definition
 `sc3_proj (x:real^4) = vector[x$1; x$2; x$3]:real^3`;;

let sc3_up = new_definition
 `sc3_up (y:real^3) =
    vector[y$1; y$2; y$3; sqrt(&1 - (y$1 pow 2 + y$2 pow 2 + y$3 pow 2))]:real^4`;;

let sc3_cone = new_definition
 `sc3_cone (z:real#real^3) =
    vector[(&1 - FST z) * SND z$1; (&1 - FST z) * SND z$2; (&1 - FST z) * SND z$3;
           --sqrt(&1 - (&1 - FST z) pow 2)]:real^4`;;

let SC3_IN_SPHERE_4 = prove
 (`!x:real^4. x IN sphere(vec 0,&1) <=>
              x$1 pow 2 + x$2 pow 2 + x$3 pow 2 + x$4 pow 2 = &1`,
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_4; REAL_POW_2]);;

let SC3_IN_BALLS_3 = prove
 (`(!y:real^3. y IN sphere(vec 0,&1) <=> y$1 pow 2 + y$2 pow 2 + y$3 pow 2 = &1) /\
   (!y:real^3. y IN ball(vec 0,&1) <=> y$1 pow 2 + y$2 pow 2 + y$3 pow 2 < &1) /\
   (!y:real^3. y IN cball(vec 0,&1) <=> y$1 pow 2 + y$2 pow 2 + y$3 pow 2 <= &1)`,
  REWRITE_TAC[IN_SPHERE_0; IN_BALL_0; IN_CBALL_0; NORM_EQ_1; NORM_LT_SQUARE;
              NORM_LE_SQUARE; DOT_3; REAL_POW_2] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let SC3_PROJ_UP = prove
 (`!y:real^3. sc3_proj(sc3_up y) = y`,
  REWRITE_TAC[sc3_proj; sc3_up; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_4]);;

let SC3_UP_PROJ = prove
 (`!x:real^4. x IN sphere(vec 0,&1) /\ &0 <= x$4 ==> sc3_up(sc3_proj x) = x`,
  REWRITE_TAC[SC3_IN_SPHERE_4] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[sc3_proj; sc3_up; CART_EQ; DIMINDEX_4; FORALL_4; VECTOR_3; VECTOR_4] THEN
  MATCH_MP_TAC SQRT_UNIQUE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SC3_UP_IN = prove
 (`!y:real^3. y IN cball(vec 0,&1)
        ==> sc3_up y IN sphere(vec 0,&1) /\ &0 <= (sc3_up y)$4 /\
            (y IN ball(vec 0,&1) ==> &0 < (sc3_up y)$4)`,
  REWRITE_TAC[SC3_IN_BALLS_3; SC3_IN_SPHERE_4; sc3_up; VECTOR_4] THEN
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `&0 <= &1 - ((y:real^3)$1 pow 2 + y$2 pow 2 + y$3 pow 2)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[SQRT_POW_2] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC]);;

let SC3_CONE_IN = prove
 (`!t u:real^3.
        t IN real_interval[&0,&1] /\ u IN sphere(vec 0,&1)
        ==> sc3_cone(t,u) IN sphere(vec 0,&1) /\ (sc3_cone(t,u))$4 <= &0 /\
            sc3_proj(sc3_cone(t,u)) = (&1 - t) % u`,
  REWRITE_TAC[IN_REAL_INTERVAL; SC3_IN_BALLS_3; SC3_IN_SPHERE_4] THEN
  REWRITE_TAC[sc3_cone; sc3_proj; VECTOR_4; FST; SND] THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `&0 <= &1 - (&1 - t) pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ARITH `&1 - (&1 - t) pow 2 = t * (&2 - t)`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_NEG; ARITH; SQRT_POW_2] THEN
    UNDISCH_TAC `(u:real^3)$1 pow 2 + u$2 pow 2 + u$3 pow 2 = &1` THEN
    CONV_TAC REAL_RING;
    REWRITE_TAC[REAL_NEG_LE0] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    REWRITE_TAC[REAL_ARITH `&1 - (&1 - t) pow 2 = t * (&2 - t)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_MUL_COMPONENT]]);;

let SC3_CONE_FIBRES = prove
 (`!t u t' u':real^3.
        t IN real_interval[&0,&1] /\ u IN sphere(vec 0,&1) /\
        t' IN real_interval[&0,&1] /\ u' IN sphere(vec 0,&1) /\
        sc3_cone(t,u) = sc3_cone(t',u')
        ==> t = t' /\ (t < &1 ==> u = u')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real`; `u:real^3`] SC3_CONE_IN) THEN
  MP_TAC(ISPECL [`t':real`; `u':real^3`] SC3_CONE_IN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `(&1 - t) % (u:real^3) = (&1 - t') % u'` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t:real = t'` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:real^3->real`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_SPHERE_0; IN_REAL_INTERVAL]) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `(&1 - t') % (u:real^3) = (&1 - t') % u'` THEN
  REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
  MATCH_MP_TAC(TAUT `~p ==> (p \/ q ==> q)`) THEN ASM_REAL_ARITH_TAC);;

let SC3_CONE_SURJ = prove
 (`!x:real^4. x IN sphere(vec 0,&1) /\ x$4 <= &0
        ==> ?t u. t IN real_interval[&0,&1] /\ u IN sphere(vec 0,&1) /\
                  sc3_cone(t,u) = x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = (x:real^4)$1 pow 2 + x$2 pow 2 + x$3 pow 2` THEN
  SUBGOAL_THEN `&0 <= s /\ s <= &1 /\ s + (x:real^4)$4 pow 2 = &1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^4) IN sphere(vec 0,&1)` THEN REWRITE_TAC[SC3_IN_SPHERE_4] THEN
    EXPAND_TAC "s" THEN
    MAP_EVERY (fun i -> MP_TAC(SPEC (subst [mk_small_numeral i,`n:num`] `(x:real^4)$n`)
                                   REAL_LE_POW_2)) [1;2;3;4] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THENL
   [SUBGOAL_THEN `(x:real^4)$1 = &0 /\ x$2 = &0 /\ x$3 = &0 /\ x$4 = -- &1`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^4)$1 pow 2 + x$2 pow 2 + x$3 pow 2 = s` THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY (fun i -> MP_TAC(SPEC (subst [mk_small_numeral i,`n:num`] `(x:real^4)$n`)
                                     REAL_LE_POW_2)) [1;2;3] THEN
      DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^4)$1 pow 2 = &0 /\ x$2 pow 2 = &0 /\ x$3 pow 2 = &0`
      MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s + (x:real^4)$4 pow 2 = &1` THEN
      UNDISCH_TAC `(x:real^4)$4 <= &0` THEN ASM_REWRITE_TAC[REAL_ADD_LID] THEN
      REWRITE_TAC[REAL_ARITH `x pow 2 = &1 <=> (x - &1) * (x + &1) = &0`] THEN
      REWRITE_TAC[REAL_ENTIRE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`&1`; `vector[&1;&0;&0]:real^3`] THEN
    REWRITE_TAC[IN_REAL_INTERVAL; SC3_IN_BALLS_3; VECTOR_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[sc3_cone; CART_EQ; DIMINDEX_4; FORALL_4; VECTOR_4; VECTOR_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SQRT_1];
    ALL_TAC] THEN
  ABBREV_TAC `r = sqrt s` THEN
  SUBGOAL_THEN `&0 < r /\ r <= &1 /\ r pow 2 = s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`&1 - r`; `inv r % sc3_proj(x:real^4)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SC3_IN_BALLS_3; sc3_proj; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
    UNDISCH_TAC `(x:real^4)$1 pow 2 + x$2 pow 2 + x$3 pow 2 = s` THEN
    UNDISCH_TAC `r pow 2 = s` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[sc3_cone; sc3_proj; CART_EQ; DIMINDEX_4; FORALL_4; VECTOR_4; VECTOR_3;
                VECTOR_MUL_COMPONENT; FST; SND] THEN
    REWRITE_TAC[REAL_ARITH `&1 - (&1 - r) = r`] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&1 - s = (x:real^4)$4 pow 2` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[POW_2_SQRT_ABS] THEN ASM_REAL_ARITH_TAC]]);;

let SC3_RCONT_TAC ths =
  let etas = map (CONV_RULE (TRY_CONV (DEPTH_CONV ETA_CONV))) ths in
  let base = CONTINUOUS_MAP_REAL_CONST :: (ths @ etas) in
  let rec tac g =
    (FIRST (map MATCH_ACCEPT_TAC base) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_POW THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_SQRT THEN tac)) g in
  tac;;

let SC3_COMPONENTS_4 =
  let th = BETA_RULE(MATCH_MP CONTINUOUS_MAP_EUCLIDEAN_COMPONENT
                      (ISPEC `euclidean:(real^4)topology` CONTINUOUS_MAP_ID)) in
  map (fun i -> SPEC (mk_small_numeral i) th) [1;2;3;4];;

let SC3_COMPONENTS_3 =
  let th = BETA_RULE(MATCH_MP CONTINUOUS_MAP_EUCLIDEAN_COMPONENT
                      (ISPEC `euclidean:(real^3)topology` CONTINUOUS_MAP_ID)) in
  map (fun i -> SPEC (mk_small_numeral i) th) [1;2;3];;

let SC3_COMPONENTS_CONE =
  let th = BETA_RULE(MATCH_MP CONTINUOUS_MAP_EUCLIDEAN_COMPONENT
             (ISPECL [`euclideanreal`; `euclidean:(real^3)topology`] CONTINUOUS_MAP_SND)) in
  ISPECL [`euclideanreal`; `euclidean:(real^3)topology`] CONTINUOUS_MAP_FST ::
  map (fun i -> SPEC (mk_small_numeral i) th) [1;2;3];;

let CONTINUOUS_MAP_SC3 = prove
 (`continuous_map (euclidean,euclidean) sc3_proj /\
   continuous_map (euclidean,euclidean) sc3_up /\
   continuous_map (prod_topology euclideanreal euclidean,euclidean) sc3_cone`,
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_REAL; DIMINDEX_3; DIMINDEX_4;
              FORALL_3; FORALL_4] THEN
  REWRITE_TAC[sc3_proj; sc3_up; sc3_cone; VECTOR_3; VECTOR_4] THEN
  REPEAT CONJ_TAC THEN
  SC3_RCONT_TAC (SC3_COMPONENTS_4 @ SC3_COMPONENTS_3 @ SC3_COMPONENTS_CONE));;

let sc3_lower = new_definition
 `sc3_lower = {x:real^4 | x IN sphere(vec 0,&1) /\ x$4 <= &0}`;;

let ATOP_S3_LOWER_LIFT = prove
 (`!top (G:real#real^3->A) a.
        continuous_map (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                      (subtopology euclidean (sphere(vec 0,&1))),top) G /\
        (!u. u IN sphere(vec 0,&1) ==> G(&1,u) = a)
        ==> ?ff. continuous_map (subtopology euclidean sc3_lower,top) ff /\
                (!t u. t IN real_interval[&0,&1] /\ u IN sphere(vec 0,&1)
                       ==> ff(sc3_cone(t,u)) = G(t,u))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                   (subtopology euclidean (sphere(vec 0:real^3,&1)))`;
    `subtopology euclidean sc3_lower`; `top:A topology`; `sc3_cone`;
    `G:real#real^3->A`] QUOTIENT_MAP_LIFT_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_QUOTIENT_MAP THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[COMPACT_SPACE_PROD_TOPOLOGY] THEN DISJ2_TAC THEN CONJ_TAC THEN
        MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
        REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL; COMPACT_IN_EUCLIDEAN;
                    COMPACT_SPHERE];
        MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
        REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
        REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM SUBTOPOLOGY_CROSS] THEN
          MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
          REWRITE_TAC[CONTINUOUS_MAP_SC3];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY;
                      TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                      FORALL_PAIR_THM; IN_CROSS; sc3_lower; IN_ELIM_THM] THEN
          SIMP_TAC[SC3_CONE_IN]];
        REWRITE_TAC[EXTENSION; IN_IMAGE; TOPSPACE_PROD_TOPOLOGY;
                    TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                    EXISTS_PAIR_THM; IN_CROSS; sc3_lower; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^4` THEN EQ_TAC THENL
         [STRIP_TAC THEN ASM_SIMP_TAC[SC3_CONE_IN];
          DISCH_THEN(MP_TAC o MATCH_MP SC3_CONE_SURJ) THEN MESON_TAC[]]];
      REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; FORALL_PAIR_THM; IN_CROSS] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `u:real^3`; `t':real`; `u':real^3`] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`t:real`; `u:real^3`; `t':real`; `u':real^3`] SC3_CONE_FIBRES) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_CASES_TAC `t' < &1` THENL
       [ASM_MESON_TAC[];
        SUBGOAL_THEN `t' = &1` SUBST_ALL_TAC THENL
         [UNDISCH_TAC `t' IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
          ASM_REAL_ARITH_TAC;
          ASM_MESON_TAC[]]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^4->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ff:real^4->A` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_CROSS]);;

let ATOP_S3_FROM_NULL_SPHERE = prove
 (`ATOP_S3_FROM_NULL_SPHERE_STATEMENT (:A)`,
  REWRITE_TAC[ATOP_S3_FROM_NULL_SPHERE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `w:A->bool`; `e:real^3->A`; `a:A`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `e:real^3->A`]
                ATOP_INVERSE_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `g0:A->real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC
   `homotopic_with (\h. T)
      (subtopology euclidean (sphere(vec 0:real^3,&1)),
       subtopology top (topspace top DIFF IMAGE (e:real^3->A) (ball(vec 0,&1))))
      e (\x. (a:A))` THEN
  REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real#real^3->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `G:real#real^3->A`; `a:A`] ATOP_S3_LOWER_LIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `topspace top DIFF IMAGE (e:real^3->A) (ball(vec 0,&1))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^4->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t u. t IN real_interval[&0,&1] /\ u IN sphere(vec 0:real^3,&1)
          ==> ~((G:real#real^3->A)(t,u) IN IMAGE (e:real^3->A) (ball(vec 0,&1)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> is_comb(concl th) &&
        free_in `G:real#real^3->A` (concl th) &&
        free_in `topspace top DIFF IMAGE (e:real^3->A) (ball(vec 0,&1))` (concl th))) THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
                SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `u:real^3`]) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (euclidean,top) ((e:real^3->A) o sc3_proj)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `euclidean:(real^3)topology` THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_SC3];
    ALL_TAC] THEN
  ABBREV_TAC `f = \x:real^4. if &0 <= x$4 then (e:real^3->A)(sc3_proj x) else ff x` THEN
  ABBREV_TAC `v = {x:real^4 | x IN sphere(vec 0,&1) /\ &0 < x$4}` THEN
  SUBGOAL_THEN
   `!x:real^4. x IN sphere(vec 0,&1)
               ==> sc3_proj x IN cball(vec 0,&1) /\
                   (x$4 = &0 ==> sc3_proj x IN sphere(vec 0,&1)) /\
                   (&0 < x$4 ==> sc3_proj x IN ball(vec 0,&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SC3_IN_SPHERE_4; SC3_IN_BALLS_3; sc3_proj; VECTOR_3] THEN
    X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN
    MP_TAC(SPEC `(x:real^4)$4` REAL_LE_POW_2) THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(x:real^4)$1 pow 2 + x$2 pow 2 + x$3 pow 2 + x$4 pow 2 = &1`;
        `&0 <= (x:real^4)$4 pow 2`] THEN REAL_ARITH_TAC;
      DISCH_TAC THEN
      UNDISCH_TAC `(x:real^4)$1 pow 2 + x$2 pow 2 + x$3 pow 2 + x$4 pow 2 = &1` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      DISCH_TAC THEN
      SUBGOAL_THEN `&0 < (x:real^4)$4 pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^4)$1 pow 2 + x$2 pow 2 + x$3 pow 2 + x$4 pow 2 = &1` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^4. x IN sphere(vec 0,&1) /\ x$4 = &0 ==> sc3_cone(&0,sc3_proj x) = x`
  ASSUME_TAC THENL
   [REWRITE_TAC[SC3_IN_SPHERE_4; sc3_cone; sc3_proj; CART_EQ; DIMINDEX_4; FORALL_4;
                VECTOR_3; VECTOR_4; FST; SND] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[SQRT_0; REAL_NEG_0; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^4. x IN sphere(vec 0,&1) /\ x$4 = &0 ==> (ff:real^4->A) x = e(sc3_proj x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM(MATCH_MP th
      (CONJ (ASSUME `(x:real^4) IN sphere(vec 0,&1)`) (ASSUME `(x:real^4)$4 = &0`)))]) THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(G:real#real^3->A)(&0,sc3_proj x)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      free_in `ff:real^4->A` (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^4->A) v = IMAGE (e:real^3->A) (ball(vec 0,&1))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["f"; "v"] THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^4` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `sc3_proj x` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `sc3_up y` THEN
      MP_TAC(SPEC `y:real^3` SC3_UP_IN) THEN
      ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL; SC3_PROJ_UP; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:real^4->A`; `v:real^4->bool`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "f" THEN
    MATCH_MP_TAC(INST_TYPE [`:bool`,`:K`] PASTING_LEMMA_CLOSED) THEN
    MAP_EVERY EXISTS_TAC
     [`\b. if b then (e:real^3->A) o sc3_proj else (ff:real^4->A)`;
      `\b. if b then {x:real^4 | x IN sphere(vec 0,&1) /\ &0 <= x$4} else sc3_lower`;
      `{T,F}`] THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                EXISTS_IN_INSERT; SUBTOPOLOGY_SUBTOPOLOGY] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       `{x:real^4 | x IN sphere(vec 0,&1) /\ &0 <= x$4} =
        sphere(vec 0,&1) INTER {x | x$4 >= &0}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_ge]; ALL_TAC] THEN
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `sc3_lower = sphere(vec 0:real^4,&1) INTER {x | x$4 <= &0}`
      SUBST1_TAC THENL
       [REWRITE_TAC[sc3_lower; EXTENSION; IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE];
      SUBGOAL_THEN `sphere(vec 0:real^4,&1) INTER sc3_lower = sc3_lower`
      SUBST1_TAC THENL [REWRITE_TAC[sc3_lower] THEN SET_TAC[]; ASM_REWRITE_TAC[]];
      REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC [`i:bool`; `j:bool`] THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; sc3_lower;
                  o_THM] THEN
      STRIP_TAC THEN
      (FIRST_X_ASSUM MATCH_MP_TAC ORELSE
       (CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC)) THEN
      ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM];
      X_GEN_TAC `x:real^4` THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM; sc3_lower; o_THM] THEN
      DISCH_TAC THEN ASM_CASES_TAC `&0 <= (x:real^4)$4` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(&0 <= (x:real^4)$4)` THEN REAL_ARITH_TAC];
    EXPAND_TAC "v" THEN
    SUBGOAL_THEN
     `{x:real^4 | x IN sphere(vec 0,&1) /\ &0 < x$4} =
      sphere(vec 0,&1) INTER {x | x$4 > &0}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT];
    EXPAND_TAC "v" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `vector[&0;&0;&0;&1]:real^4` THEN
    REWRITE_TAC[SC3_IN_SPHERE_4; VECTOR_4] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ASM_SIMP_TAC[OPEN_BALL];
    SUBGOAL_THEN `subtopology (subtopology euclidean (sphere(vec 0:real^4,&1))) v =
                  subtopology euclidean v` SUBST1_TAC THENL
     [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN EXPAND_TAC "v" THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_EQ THEN EXISTS_TAC `(e:real^3->A) o sc3_proj` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN MAP_EVERY EXPAND_TAC ["v"; "f"] THEN
      REWRITE_TAC[IN_ELIM_THM; o_THM] THEN SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&1))` THEN CONJ_TAC THENL
     [REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN EXISTS_TAC `sc3_up` THEN
      REWRITE_TAC[HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY; HOMEOMORPHISM] THEN
      MP_TAC CONTINUOUS_MAP_SC3 THEN REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN] THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
        EXPAND_TAC "v" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        ASM_MESON_TAC[];
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
        EXPAND_TAC "v" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        MESON_TAC[SC3_UP_IN; BALL_SUBSET_CBALL; SUBSET];
        EXPAND_TAC "v" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        MESON_TAC[SC3_UP_PROJ; REAL_LT_IMP_LE];
        REWRITE_TAC[SC3_PROJ_UP]];
      MP_TAC(ISPECL [`euclidean:(real^3)topology`; `subtopology top (w:A->bool)`;
                     `e:real^3->A`; `ball(vec 0:real^3,&1)`;
                     `IMAGE (e:real^3->A) (ball(vec 0,&1))`]
                    HOMEOMORPHIC_MAP_SUBTOPOLOGIES) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; INTER_UNIV; SUBTOPOLOGY_SUBTOPOLOGY;
                      TOPSPACE_SUBTOPOLOGY] THEN
      SUBGOAL_THEN `w INTER IMAGE (e:real^3->A) (ball(vec 0,&1)) = IMAGE e (ball(vec 0,&1))`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]];
    X_GEN_TAC `y:real^4` THEN STRIP_TAC THEN EXPAND_TAC "v" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&0 < (y:real^4)$4` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(f:real^4->A) y IN IMAGE (e:real^3->A) (ball(vec 0,&1))` THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `(y:real^4)$4 = &0` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL; IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `g0:A->real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      SUBGOAL_THEN `sc3_proj (y:real^4) IN sphere(vec 0,&1)` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `sc3_proj (y:real^4) IN ball(vec 0,&1)` THEN
      REWRITE_TAC[IN_BALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `~(&0 <= (y:real^4)$4) /\ y$4 <= &0` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`~(&0 < (y:real^4)$4)`; `~((y:real^4)$4 = &0)`] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `y:real^4` SC3_CONE_SURJ) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `u:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[]]]);;


