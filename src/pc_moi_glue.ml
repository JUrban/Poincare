(* ========================================================================= *)
(* pc_moi_glue: the four glue implications of the Moise chain.               *)
(*  - MOI_COMPACT_TRIANGULATION: PL_TRIANGULATION_LF ==> PL_TRIANGULATION;   *)
(*  - MOI_IMAGE_EQUALITY: MOISE_352_OPEN ==> MOISE_APPROX (approximations    *)
(*    with small error have the same image; Brouwer fixed point argument);   *)
(*  - MOI_TRANSFER: MOISE_352_COMPLEX /\ PL_TRIANGULATION_LF ==> MOISE_352_OPEN; *)
(*  - MOI_CHART_GLUING: MOISE_APPROX ==> MOISE_PL_ATLAS (glue the charts of  *)
(*    a compact 3-manifold one at a time; DG ChartGluing.lean; Moise Sec 35). *)
(* ========================================================================= *)

needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_plmap.ml";;

prioritize_real();;
type_invention_error := true;;

(* Compact case of the triangulation statement.                              *)

let MOI_GLUE_SECOND_COUNTABLE_EUCLIDEAN = prove
 (`second_countable (euclidean:(real^N)topology)`,
  REWRITE_TAC[second_countable; OPEN_IN_EUCLIDEAN] THEN
  X_CHOOSE_THEN `b:(real^N->bool)->bool` STRIP_ASSUME_TAC UNIV_SECOND_COUNTABLE THEN
  EXISTS_TAC `b:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^N) IN u` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
  ASM SET_TAC[]);;

let MOI_GLUE_SECOND_COUNTABLE_FINITE_UNION = prove
 (`!(top:A topology) u.
        FINITE u /\
        (!w. w IN u ==> open_in top w /\ second_countable (subtopology top w)) /\
        UNIONS u = topspace top
        ==> second_countable top`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?b:(A->bool)->(A->bool)->bool.
      !w. w IN u
          ==> COUNTABLE (b w) /\ (!v. v IN b w ==> open_in top v) /\
              (!t x. open_in top t /\ x IN t /\ x IN w
                     ==> ?v. v IN b w /\ x IN v /\ v SUBSET t)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `w:A->bool` THEN
    ASM_CASES_TAC `(w:A->bool) IN u` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[second_countable] THEN STRIP_TAC THEN
    EXISTS_TAC `b:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:A->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `w:A->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:A->bool`; `x:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w INTER t:A->bool`; `x:A`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[IN_INTER; OPEN_IN_SUBTOPOLOGY_INTER_OPEN];
      MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[second_countable] THEN
  EXISTS_TAC `UNIONS (IMAGE (b:(A->bool)->(A->bool)->bool) u)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_IMAGE; FORALL_IN_IMAGE];
    REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`t:A->bool`; `x:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?w:A->bool. w IN u /\ x IN w` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:A->bool`; `x:A`] o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[]]);;

let MOI_GLUE_HOMEOMORPHIC_SECOND_COUNTABLE = prove
 (`!(top:A topology) (top':B topology) f.
        homeomorphic_map (top,top') f /\ second_countable top'
        ==> second_countable top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `g:B->A`) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:B->A`; `top':B topology`; `top:A topology`]
                SECOND_COUNTABLE_OPEN_MAP_IMAGE) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_MAPS_IMP_MAP o
    ONCE_REWRITE_RULE[HOMEOMORPHIC_MAPS_SYM]) THEN
  ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP; HOMEOMORPHIC_IMP_OPEN_MAP;
                HOMEOMORPHIC_IMP_SURJECTIVE_MAP]);;

let MOI_GLUE_PL_ATLAS_COMPACT_SECOND_COUNTABLE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool).
        compact_space top /\ pl_manifold_atlas top atlas
        ==> second_countable top`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_SPACE]) THEN
  DISCH_THEN(MP_TAC o SPEC `{U:A->bool | ?phi:A->real^N. (U,phi) IN atlas}`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_manifold_atlas]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_GLUE_SECOND_COUNTABLE_FINITE_UNION THEN
  EXISTS_TAC `V:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?phi:A->real^N. (w:A->bool,phi) IN (atlas:((A->bool)#(A->real^N))->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (w:A->bool)`;
                 `subtopology euclidean (IMAGE (phi:A->real^N) w)`;
                 `phi:A->real^N`] MOI_GLUE_HOMEOMORPHIC_SECOND_COUNTABLE) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SECOND_COUNTABLE_SUBTOPOLOGY THEN
  REWRITE_TAC[MOI_GLUE_SECOND_COUNTABLE_EUCLIDEAN]);;

let MOI_GLUE_LF_COMPLEX_COMPACT_FINITE = prove
 (`!c:(real^N->bool)->bool.
        lf_simplicial_complex c /\ compact (UNIONS c) ==> FINITE c`,
  GEN_TAC THEN REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real^N->real^N->bool`) THEN
  MP_TAC(ISPEC `UNIONS c:real^N->bool` COMPACT_IMP_HEINE_BOREL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (u:real^N->real^N->bool) (UNIONS c)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
    ASM_MESON_TAC[IN_UNIONS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{} INSERT UNIONS (IMAGE (\v:real^N->bool. {s:real^N->bool | s IN c /\ ~(s INTER v = {})}) f)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_INSERT; FINITE_UNIONS] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `v:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x:real^N. x IN UNIONS (c:(real^N->bool)->bool) /\
                             (v:real^N->bool) = (u:real^N->real^N->bool) x`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(v:real^N->bool) IN f` THEN
      UNDISCH_TAC `(f:(real^N->bool)->bool) SUBSET
                   IMAGE (u:real^N->real^N->bool) (UNIONS c)` THEN
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[];
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; IN_INSERT; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `y:real^N` o
      GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    SUBGOAL_THEN `?v:real^N->bool. v IN f /\ (y:real^N) IN v`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_UNIONS]; ALL_TAC] THEN
    EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_COMPACT_TRIANGULATION = prove
 (`!(u:A->bool) (v:N->bool).
     PL_TRIANGULATION_LF_STATEMENT u v ==> PL_TRIANGULATION_STATEMENT u v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PL_TRIANGULATION_LF_STATEMENT; PL_TRIANGULATION_STATEMENT] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`;
                                `atlas:((A->bool)#(A->real^3))->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                  MOI_GLUE_PL_ATLAS_COMPACT_SECOND_COUNTABLE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:(real^N->bool)->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_GLUE_LF_COMPLEX_COMPACT_FINITE THEN CONJ_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold 3 (c:(real^N->bool)->bool)` THEN
    SIMP_TAC[combinatorial_manifold];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPACT_SPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS c:real^N->bool)`; `top:A topology`]
                HOMEOMORPHIC_COMPACT_SPACE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[homeomorphic_space] THEN ASM_MESON_TAC[HOMEOMORPHIC_MAP_MAPS];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* Image equality: approximations with small error have the same image.     *)

let MOI_GLUE_BALL_COVER = prove
 (`!(g:real^N->real^N) z r.
        &0 < r /\ g continuous_on cball(z,r) /\
        (!y. y IN cball(z,r) ==> dist(g y,y) <= r)
        ==> z IN IMAGE g (cball(z,r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^N. y - g y + z`; `z:real^N`; `r:real`] BROUWER_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
      ASM_REWRITE_TAC[IN_CBALL; dist] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= r ==> a <= r`) THEN
      AP_TERM_TAC THEN VECTOR_ARITH_TAC];
    REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `y - (g:real^N->real^N) y + z = y` THEN VECTOR_ARITH_TAC]);;

let MOI_GLUE_SURJ_LEMMA = prove
 (`!(v:real^N->bool) (g:real^N->real^N) (dd:real^N->real).
        g continuous_on v /\
        (!x y. abs(dd x - dd y) <= dist(x,y)) /\
        (!y. y IN v ==> &0 < dd y /\ cball(y,dd y / &2) SUBSET v) /\
        (!y. y IN v ==> dist(g y,y) < dd y / &5)
        ==> v SUBSET IMAGE g v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (dd:real^N->real) z /\ cball(z,dd z / &2) SUBSET v`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cball(z:real^N,dd z / &4) SUBSET v` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(z:real^N,dd z / &2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^N->real^N`; `z:real^N`; `(dd:real^N->real) z / &4`]
                MOI_GLUE_BALL_COVER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^N) IN v` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `dist((g:real^N->real^N) y,y) < (dd:real^N->real) y / &5`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `abs((dd:real^N->real) y - dd z) <= dist(z,y)` MP_TAC THENL
       [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^N) IN cball(z,dd z / &4)` THEN
      REWRITE_TAC[IN_CBALL] THEN REAL_ARITH_TAC];
    ASM SET_TAC[]]);;

let MOI_GLUE_IMAGE_EQ_CORE = prove
 (`!(top:A topology) (h:A->real^3) (f:A->real^3) (dd:real^3->real).
        embedding_map (top,euclidean) h /\ embedding_map (top,euclidean) f /\
        (!x y. abs(dd x - dd y) <= dist(x,y)) /\
        (!y. y IN IMAGE h (topspace top)
             ==> &0 < dd y /\ cball(y,dd y / &2) SUBSET IMAGE h (topspace top)) /\
        (!x. x IN topspace top ==> dist(f x,h x) < dd(h x) / &5)
        ==> IMAGE f (topspace top) = IMAGE h (topspace top)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 < (dd:real^3->real) (h(x:A)) /\
      cball(h x,dd(h x) / &2) SUBSET IMAGE (h:A->real^3) (topspace top)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < d /\ x < d / &5 ==> x <= d / &2`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ASSUME `embedding_map (top,euclidean) (h:A->real^3)`) THEN
  REWRITE_TAC[embedding_map; HOMEOMORPHIC_MAP_MAPS] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:real^3->A`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
                              INTER_UNIV]) THEN
  SUBGOAL_THEN `continuous_map (top,euclidean) (f:A->real^3)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `embedding_map (top,euclidean) (f:A->real^3)`) THEN
    REWRITE_TAC[embedding_map] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((f:A->real^3) o (k:real^3->A)) continuous_on IMAGE (h:A->real^3) (topspace top)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (h:A->real^3) (topspace top)`;
                 `(f:A->real^3) o (k:real^3->A)`; `dd:real^3->real`]
                MOI_GLUE_SURJ_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(k:real^3->A) (h(x:A)) = x` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[]];
    MATCH_MP_TAC(SET_RULE
     `!(f:A->real^3) (k:real^3->A) (v:real^3->bool) w.
        IMAGE (f o k) v SUBSET w ==> v SUBSET IMAGE (f o k) v ==> v SUBSET w`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(k:real^3->A) (h(x:A))` THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

let MOI_GLUE_DD_LEMMA = prove
 (`!v:real^N->bool.
        open v
        ==> ?dd:real^N->real.
              (!x y. abs(dd x - dd y) <= dist(x,y)) /\
              (!y. y IN v ==> &0 < dd y /\ cball(y,dd y / &2) SUBSET v)`,
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `v = (:real^N)` THENL
   [EXISTS_TAC `\y:real^N. &1` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; REAL_SUB_REFL; REAL_ABS_0; DIST_POS_LE;
                    REAL_LT_01];
    ALL_TAC] THEN
  EXISTS_TAC `\y:real^N. setdist({y},(:real^N) DIFF v)` THEN
  REWRITE_TAC[SETDIST_SING_TRIANGLE] THEN X_GEN_TAC `y:real^N` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < setdist({y:real^N},(:real^N) DIFF v)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE; SETDIST_POS_LE] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    MP_TAC(ISPECL [`(:real^N) DIFF v`; `y:real^N`] SETDIST_EQ_0_CLOSED) THEN
    ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; DE_MORGAN_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `w:real^N` THEN
  DISCH_TAC THEN ASM_CASES_TAC `(w:real^N) IN v` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`{y:real^N}`; `(:real^N) DIFF v`; `y:real^N`; `w:real^N`]
                SETDIST_LE_DIST) THEN
  ASM_REWRITE_TAC[IN_SING; IN_DIFF; IN_UNIV] THEN ASM_REAL_ARITH_TAC);;

let MOI_IMAGE_EQUALITY = prove
 (`!u:A->bool. MOISE_352_OPEN_STATEMENT u ==> MOISE_APPROX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[MOISE_352_OPEN_STATEMENT; MOISE_APPROX_STATEMENT] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `h:A->real^3`; `e:A->real`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (h:A->real^3) (topspace top)` MOI_GLUE_DD_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real^3->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `continuous_map (top,euclidean) (h:A->real^3)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `embedding_map (top,euclidean) (h:A->real^3)`) THEN
    REWRITE_TAC[embedding_map] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (euclidean,euclideanreal) (dd:real^3->real)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(dd:real^3->real) = drop o (lift o dd)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `euclidean:(real^1)topology` THEN
    REWRITE_TAC[CONTINUOUS_MAP_DROP] THEN
    MP_TAC(ISPECL [`lift o (dd:real^3->real)`; `(:real^3)`]
                  CONTINUOUS_MAP_EUCLIDEAN) THEN
    REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^3` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[continuous_at; o_THM; DIST_LIFT] THEN
    ASM_MESON_TAC[REAL_LET_TRANS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `h:A->real^3`;
    `\x:A. min (e x) ((dd:real^3->real) (h x) / &5)`]) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MIN THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
      SUBGOAL_THEN `(\x:A. (dd:real^3->real) (h x)) = dd o h` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `euclidean:(real^3)topology` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LT_MIN] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < d ==> &0 < d / &5`) THEN
      ASM_MESON_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:A->real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x:A. x IN topspace top
          ==> dist((f:A->real^3) x,h x) < e x /\
              dist(f x,h x) < (dd:real^3->real)(h x) / &5`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LT_MIN] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC MOI_GLUE_IMAGE_EQ_CORE THEN
  EXISTS_TAC `dd:real^3->real` THEN ASM_SIMP_TAC[]);;


(* Charts, invariance of domain and embeddings of charted spaces.           *)

let MOI_GLUE_CONTINUOUS_MAP_LIFT = prove
 (`!(f:real^N->real) s.
        continuous_map (subtopology euclidean s,euclideanreal) f
        ==> (lift o f) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `euclideanreal` THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_LIFT]);;

let MOI_GLUE_ATLAS_CHART = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi.
        pl_manifold_atlas top atlas /\ (U,phi) IN atlas
        ==> open_in top U /\ open (IMAGE phi U) /\
            ?q. homeomorphic_maps (subtopology top U,
                                   subtopology euclidean (IMAGE phi U)) (phi,q)`,
  REWRITE_TAC[pl_manifold_atlas; GSYM HOMEOMORPHIC_MAP_MAPS] THEN
  MESON_TAC[]);;

let MOI_GLUE_ATLAS_OPEN_IMAGE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi w.
        pl_manifold_atlas top atlas /\ (U,phi) IN atlas /\ open_in top w
        ==> open (IMAGE phi (w INTER U))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in top (U:A->bool) /\ open (IMAGE (phi:A->real^N) U) /\
    homeomorphic_map (subtopology top U,subtopology euclidean (IMAGE phi U)) phi`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_manifold_atlas]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`phi:A->real^N`; `subtopology top (U:A->bool)`;
                 `subtopology euclidean (IMAGE (phi:A->real^N) U)`;
                 `w INTER U:A->bool`] HOMEOMORPHIC_MAP_OPENNESS) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ANTS_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN]);;

let MOI_GLUE_ATLAS_INJECTIVE_EMBEDDING = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^N).
        pl_manifold_atlas top atlas /\ continuous_map (top,euclidean) f /\
        (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y ==> x = y)
        ==> embedding_map (top,euclidean) f /\ open (IMAGE f (topspace top))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_map (top,euclidean) (f:A->real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[open_map; OPEN_IN_EUCLIDEAN] THEN X_GEN_TAC `w:A->bool` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `IMAGE (f:A->real^N) w =
      UNIONS (IMAGE (\U. IMAGE f (w INTER U))
                    {U:A->bool | ?phi:A->real^N. (U,phi) IN atlas})`
    SUBST1_TAC THENL
     [REWRITE_TAC[UNIONS_IMAGE; EXTENSION; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
         [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
          GEN_REWRITE_RULE I [pl_manifold_atlas]) THEN
        DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_TAC `phi:A->real^N`)) THEN
        EXISTS_TAC `U:A->bool` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER];
        DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `(y:real^N) IN IMAGE f (w INTER U:A->bool)` THEN
        REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `U:A->bool` THEN DISCH_THEN(X_CHOOSE_TAC `phi:A->real^N`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] MOI_GLUE_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `q:real^N->A`))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
                                INTER_UNIV; IN_INTER]) THEN
    SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (f:A->real^N) (w INTER U) =
      IMAGE (f o (q:real^N->A)) (IMAGE (phi:A->real^N) (w INTER U))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
      REWRITE_TAC[o_THM; IN_INTER] THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology top (U:A->bool)` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY];
      MATCH_MP_TAC MOI_GLUE_ATLAS_OPEN_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE;
                  IN_INTER; o_THM] THEN
      X_GEN_TAC `x:A` THEN REPEAT DISCH_TAC THEN
      X_GEN_TAC `y:A` THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `(q:real^N->A) (phi(x:A)) = x /\ q (phi y) = y`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INJECTIVE_OPEN_IMP_EMBEDDING_MAP THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `topspace top:A->bool` o
      GEN_REWRITE_RULE I [open_map]) THEN
    REWRITE_TAC[OPEN_IN_TOPSPACE; OPEN_IN_EUCLIDEAN]]);;

(* Transfer: the core for triangulated sources gives the approximation for  *)
(* PL manifolds.                                                             *)

let MOI_GLUE_TRANSFER_CHART = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
    (c:(real^N->bool)->bool) (t:real^N->A) (s:A->real^N) U phi
    (g:real^N->real^3).
     pl_manifold_atlas top atlas /\ (U,phi) IN atlas /\
     homeomorphic_maps (subtopology euclidean (UNIONS c),top) (t,s) /\
     (?g0. pl_map_on {x | x IN UNIONS c /\ t x IN U} g0 /\
           !x. x IN UNIONS c /\ t x IN U ==> g0 x = phi(t x)) /\
     pl_map_on (UNIONS c) g
     ==> ?g'. pl_map_on (IMAGE phi U) g' /\ !x. x IN U ==> g'(phi x) = g(s x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `g0:real^N->real^3` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] MOI_GLUE_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `q:real^3->A`))) THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps] o
    check (fun th -> free_in `q:real^3->A` (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps] o
    check (fun th -> free_in `t:real^N->A` (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
                              INTER_UNIV; IN_INTER]) THEN
  SUBGOAL_THEN `!z:A. z IN topspace top ==> (s:A->real^N) z IN UNIONS c`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> free_in `s:A->real^N` (concl th) &&
                       is_comb (concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism ({x | x IN UNIONS c /\ (t:real^N->A) x IN U},
                   IMAGE (phi:A->real^3) U)
                  ((g0:real^N->real^3),(s:A->real^N) o (q:real^3->A))`
  ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphism; IN_ELIM_THM; o_THM] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `(t:real^N->A) x` THEN ASM_MESON_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `(s:A->real^N) z` THEN ASM_MESON_TAC[SUBSET]];
      ASM_MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(q:real^3->A) (phi(z:A)) = z /\ (t:real^N->A) (s z) = z /\
                    (s z) IN UNIONS c`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; o_THM] THEN
      X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC
          (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC))) THEN
        ASM_MESON_TAC[SUBSET];
        STRIP_TAC THEN EXISTS_TAC `(phi:A->real^3) ((t:real^N->A) x)` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
        EXISTS_TAC `(t:real^N->A) x` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology top (U:A->bool)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `s:A->real^N` (concl th) &&
                       is_comb (concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (IMAGE (phi:A->real^3) U) ((s:A->real^N) o (q:real^3->A))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
    MAP_EVERY EXISTS_TAC
     [`{x | x IN UNIONS c /\ (t:real^N->A) x IN U}`; `g0:real^N->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(g:real^N->real^3) o (s:A->real^N) o (q:real^3->A)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[SUBSET]]);;

let MOI_TRANSFER = prove
 (`!(u:A->bool) (v:N->bool).
     7 <= dimindex(:N) /\ MOISE_352_COMPLEX_STATEMENT v /\
     PL_TRIANGULATION_LF_STATEMENT u v
     ==> MOISE_352_OPEN_STATEMENT u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MOISE_352_COMPLEX_STATEMENT; PL_TRIANGULATION_LF_STATEMENT;
              MOISE_352_OPEN_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `h:A->real^3`; `e:A->real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`;
                                `atlas:((A->bool)#(A->real^3))->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool`
   (X_CHOOSE_THEN `t:real^N->A` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS] o
    check (fun th -> free_in `t:real^N->A` (concl th) &&
                     fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_map")) THEN
  DISCH_THEN(X_CHOOSE_TAC `s:A->real^N`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps] o
    check (fun th -> free_in `s:A->real^N` (concl th) &&
                     fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_maps")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
                              INTER_UNIV]) THEN
  SUBGOAL_THEN `!z:A. z IN topspace top ==> (s:A->real^N) z IN UNIONS c`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> free_in `s:A->real^N` (concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN UNIONS c ==> (t:real^N->A) x IN topspace top`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> free_in `t:real^N->A` (concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (top,euclidean) (h:A->real^3)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `embedding_map (top,euclidean) (h:A->real^3)`) THEN
    REWRITE_TAC[embedding_map] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:A. x IN topspace top /\ y IN topspace top /\ (h:A->real^3) x = h y ==> x = y`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `embedding_map (top,euclidean) (h:A->real^3)`) THEN
    REWRITE_TAC[embedding_map; homeomorphic_map] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `(h:A->real^3) o (t:real^N->A)`;
    `(e:A->real) o (t:real^N->A)`] o
   check (fun th -> is_forall (concl th) &&
                    can (find_term (fun tm -> try fst(dest_const tm) = "combinatorial_manifold"
                                              with _ -> false)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      MATCH_MP_TAC MOI_GLUE_CONTINUOUS_MAP_LIFT THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(g:real^N->real^3) o (s:A->real^N)` THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real^N->real^3) o (s:A->real^N)`]
                  MOI_GLUE_ATLAS_INJECTIVE_EMBEDDING) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (UNIONS c:real^N->bool)` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
      ASM_MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
      ASM_MESON_TAC[]];
    REWRITE_TAC[pl_in_charts] THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC MOI_GLUE_TRANSFER_CHART THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `c:(real^N->bool)->bool`; `t:real^N->A`] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(t:real^N->A) ((s:A->real^N) x) = x /\ s x IN UNIONS c`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;


(* Chart gluing, part 1: restriction of PL atlases to open subsets.         *)

let MOI_GLUE_RESTRICT_IN = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) w V psi.
        (V,psi) IN {(U INTER w,phi) | U,phi | (U,phi) IN atlas} <=>
        ?U. (U,psi) IN atlas /\ V = U INTER w`,
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let MOI_GLUE_PL_ATLAS_RESTRICT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) w.
        pl_manifold_atlas top atlas /\ open_in top w
        ==> pl_manifold_atlas (subtopology top w)
              {(U INTER w,phi) | U,phi | (U,phi) IN atlas}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_manifold_atlas]) THEN
  REWRITE_TAC[pl_manifold_atlas; MOI_GLUE_RESTRICT_IN] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    SUBGOAL_THEN
     `open_in top (U:A->bool) /\ open (IMAGE (psi:A->real^N) U) /\
      homeomorphic_map (subtopology top U,subtopology euclidean (IMAGE psi U)) psi`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[INTER_COMM] THEN
      ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN];
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      MATCH_MP_TAC MOI_GLUE_ATLAS_OPEN_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      SUBGOAL_THEN `w INTER U INTER w:A->bool = U INTER w` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                     `subtopology euclidean (IMAGE (psi:A->real^N) U)`;
                     `psi:A->real^N`; `U INTER w:A->bool`;
                     `IMAGE (psi:A->real^N) (U INTER w)`]
                    HOMEOMORPHIC_MAP_SUBTOPOLOGIES) THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
                      TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
      ANTS_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
          check (fun th -> concl th = `open_in top (U:A->bool)`)) THEN
        SET_TAC[];
        SUBGOAL_THEN
         `U INTER U INTER w:A->bool = U INTER w /\
          IMAGE (psi:A->real^N) U INTER IMAGE psi (U INTER w) =
          IMAGE psi (U INTER w)`
        (CONJUNCTS_THEN SUBST1_TAC) THENL [SET_TAC[]; REWRITE_TAC[]]]];
    X_GEN_TAC `x:A` THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `topspace (top:A topology)`)) (concl th) &&
      not (can (find_term (fun t -> try fst(dest_const t) = "pl_map_on" with _ -> false)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_TAC `phi:A->real^N`)) THEN
    MAP_EVERY EXISTS_TAC [`U INTER w:A->bool`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`V1:A->bool`; `phi:A->real^N`; `V2:A->bool`; `psi:A->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `U1:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))
      (X_CHOOSE_THEN `U2:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
    SUBGOAL_THEN
     `?g:real^N->real^N. pl_map_on (IMAGE (phi:A->real^N) (U1 INTER U2)) g /\
                         !x. x IN U1 INTER U2 ==> g(phi x) = (psi:A->real^N) x`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `g:real^N->real^N` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) (U1 INTER U2)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_OPEN THEN
      SUBGOAL_THEN `(U1 INTER w) INTER U2 INTER w:A->bool = (U2 INTER w) INTER U1`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_GLUE_ATLAS_OPEN_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[IN_INTER]]]);;

(* Chart gluing, part 2: the glued self-map of Euclidean space.             *)

let MOI_GLUE_GLUED_CONTINUOUS = prove
 (`!(v:real^N->bool) (ff:real^N->real^N) (dd:real^N->real).
        open v /\ ff continuous_on v /\
        (!y. y IN v ==> &0 < dd y /\ cball(y,dd y / &2) SUBSET v) /\
        (!y. y IN v ==> dist(ff y,y) < dd y / &2)
        ==> (\y. if y IN v then ff y else y) continuous_on (:real^N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `z:real^N` THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `(z:real^N) IN v` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    EXISTS_TAC `ff:real^N->real^N` THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def]) THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^N) IN v` (fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`ff:real^N->real^N`; `v:real^N->bool`]
                    CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[continuous_at] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `e / &2` THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `dist((ff:real^N->real^N) y,y) < (dd:real^N->real) y / &2 /\
                    dd y / &2 < dist(y,z)`
      MP_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
        UNDISCH_TAC `~((z:real^N) IN v)` THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "cball"))
              (concl th))) THEN
        ASM_REWRITE_TAC[SUBSET; IN_CBALL] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `dist(y:real^N,z) < e / &2` THEN CONV_TAC NORM_ARITH];
      ASM_REAL_ARITH_TAC]]);;

let MOI_GLUE_GLUED_HOMEOMORPHISM = prove
 (`!(v:real^N->bool) (ff:real^N->real^N) (dd:real^N->real).
        open v /\ ff continuous_on v /\ IMAGE ff v = v /\
        (!x y. x IN v /\ y IN v /\ ff x = ff y ==> x = y) /\
        (!y. y IN v ==> &0 < dd y /\ cball(y,dd y / &2) SUBSET v) /\
        (!y. y IN v ==> dist(ff y,y) < dd y / &2)
        ==> ?G'. homeomorphism ((:real^N),(:real^N))
                               ((\y. if y IN v then ff y else y),G')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. if y IN v then (ff:real^N->real^N) y else y)
                continuous_on (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_GLUE_GLUED_CONTINUOUS THEN
    EXISTS_TAC `dd:real^N->real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. (if x IN v then (ff:real^N->real^N) x else x) =
          (if y IN v then ff y else y) ==> x = y`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN v` THEN ASM_CASES_TAC `(y:real^N) IN v` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_INJECTIVE_OPEN_MAP THEN
  ASM_REWRITE_TAC[IN_UNIV; SUBTOPOLOGY_UNIV; OPEN_IN_EUCLIDEAN] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^N` THEN
    ASM_CASES_TAC `(y:real^N) IN v` THENL
     [UNDISCH_TAC `IMAGE (ff:real^N->real^N) v = v` THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[];
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]]);;

(* Chart gluing, part 3: the new atlas after one gluing step.               *)

let MOI_GLUE_LIPSCHITZ_CONTINUOUS_MAP = prove
 (`!dd:real^N->real.
        (!x y. abs(dd x - dd y) <= dist(x,y))
        ==> continuous_map (euclidean,euclideanreal) dd`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(dd:real^N->real) = drop o (lift o dd)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `euclidean:(real^1)topology` THEN
  REWRITE_TAC[CONTINUOUS_MAP_DROP] THEN
  MP_TAC(ISPECL [`lift o (dd:real^N->real)`; `(:real^N)`]
                CONTINUOUS_MAP_EUCLIDEAN) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `x:real^N` THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[continuous_at; o_THM; DIST_LIFT] THEN
  ASM_MESON_TAC[REAL_LET_TRANS]);;

let MOI_GLUE_INSERT_IN = prove
 (`!(c:(A->bool)#(A->real^N)) atlas V psi.
        (V,psi) IN c INSERT atlas <=> (V,psi) = c \/ (V,psi) IN atlas`,
  REWRITE_TAC[IN_INSERT]);;


(* Chart gluing, part 4: charts and transitions of the glued atlas.          *)

let MOI_GLUE_NEW_CHART = prove
 (`!(top:A topology) u s (h:A->real^3) hinv (G:real^3->real^3) G'.
        open_in top u /\ u SUBSET s /\
        homeomorphic_maps (subtopology top u,euclidean) (h,hinv) /\
        homeomorphism ((:real^3),(:real^3)) (G,G')
        ==> open_in (subtopology top s) u /\
            IMAGE (G o h) u = (:real^3) /\
            homeomorphic_map (subtopology (subtopology top s) u,
                              subtopology euclidean (IMAGE (G o h) u)) (G o h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:A->real^3) u = (:real^3)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_MAPS_IMP_MAP) THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (G:real^3->real^3) (:real^3) = (:real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((G:real^3->real^3) o (h:A->real^3)) u = (:real^3)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; SUBTOPOLOGY_UNIV] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s INTER u:A->bool = u` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
  EXISTS_TAC `euclidean:(real^3)topology` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HOMEOMORPHIC_MAPS_IMP_MAP]; ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAPS_IMP_MAP THEN EXISTS_TAC `G':real^3->real^3` THEN
  MP_TAC(ISPECL [`G:real^3->real^3`; `G':real^3->real^3`; `(:real^3)`; `(:real^3)`]
                HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV]);;

let MOI_GLUE_OLD_CHART = prove
 (`!(top:A topology) V s (phi:A->real^3).
        open_in top V /\ V SUBSET s /\
        homeomorphic_map (subtopology top V,subtopology euclidean (IMAGE phi V)) phi
        ==> open_in (subtopology top s) V /\
            homeomorphic_map (subtopology (subtopology top s) V,
                              subtopology euclidean (IMAGE phi V)) phi`,
  SIMP_TAC[OPEN_IN_SUBSET_TOPSPACE; SUBTOPOLOGY_SUBTOPOLOGY] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s INTER V:A->bool = V` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_REWRITE_TAC[]]);;

let MOI_GLUE_IMAGE_COMPOSE_EQ = prove
 (`!(G:B->C) (h:A->B) f u V.
        (!x. x IN V /\ x IN u ==> G(h x) = f x)
        ==> IMAGE (G o h) (u INTER V) = IMAGE f (V INTER u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM; IN_INTER] THEN
  ASM_MESON_TAC[]);;
let MOI_GLUE_IMAGE_IMAGE_EQ = prove
 (`!(k1:C->B) (psi:A->C) f V u.
          (!x. x IN V /\ x IN u ==> k1(psi x) = f x)
          ==> IMAGE k1 (IMAGE psi (V INTER u)) = IMAGE f (V INTER u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
  ASM_SIMP_TAC[o_THM; IN_INTER]);;
let MOI_GLUE_IMAGE_INV_EQ = prove
 (`!(psi:A->C) (finv:B->A) (f:A->B) V u.
          (!x. x IN V /\ x IN u ==> finv(f x) = x)
          ==> IMAGE (psi o finv) (IMAGE f (V INTER u)) = IMAGE psi (V INTER u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
  ASM_SIMP_TAC[o_THM; IN_INTER]);;

let MOI_GLUE_K2_HOMEOMORPHISM = prove
 (`!(psi:A->real^3) (f:A->real^3) (finv:real^3->A) (k1:real^3->real^3) V u.
        pl_map_on (IMAGE psi (V INTER u)) k1 /\
        (!x. x IN V /\ x IN u ==> k1(psi x) = f x) /\
        (!x. x IN V /\ x IN u ==> finv(f x) = x) /\
        (psi o finv) continuous_on IMAGE f (V INTER u)
        ==> homeomorphism (IMAGE psi (V INTER u),IMAGE f (V INTER u))
                          (k1,psi o finv)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MOI_GLUE_IMAGE_IMAGE_EQ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MOI_GLUE_IMAGE_INV_EQ THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let MOI_GLUE_PSI_FINV_CONTINUOUS = prove
 (`!(top:A topology) (psi:A->real^3) (f:A->real^3) (finv:real^3->A) V u s t.
        continuous_map (subtopology euclidean s,subtopology top t) finv /\
        IMAGE f (V INTER u) SUBSET s /\
        (!x. x IN V /\ x IN u ==> finv(f x) = x) /\
        continuous_map (subtopology top V,euclidean) psi
        ==> (psi o finv) continuous_on IMAGE f (V INTER u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology top (V:A->bool)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `continuous_map (subtopology euclidean s,subtopology top t) (finv:real^3->A)` THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(finv:real^3->A) (f(x:A)) = x` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_GLUE_NEW_OLD = prove
 (`!(top:A topology) w u V (psi:A->real^3) (h:A->real^3) (f:A->real^3) finv
    (G:real^3->real^3) k1.
        V SUBSET w /\ open_in top V /\
        homeomorphic_map (subtopology top V,subtopology euclidean (IMAGE psi V)) psi /\
        homeomorphic_maps (subtopology top (w INTER u),
                           subtopology euclidean (IMAGE h (w INTER u))) (f,finv) /\
        (!x. x IN w /\ x IN u ==> G(h x) = f x) /\
        pl_map_on (IMAGE psi (V INTER u)) k1 /\
        (!x. x IN V INTER u ==> k1(psi x) = f x)
        ==> ?g. pl_map_on (IMAGE (G o h) (u INTER V)) g /\
                !x. x IN u INTER V ==> g((G o h) x) = psi x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `(V:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology top (w INTER u),
                    subtopology euclidean (IMAGE (h:A->real^3) (w INTER u))) f /\
    continuous_map (subtopology euclidean (IMAGE h (w INTER u)),
                    subtopology top (w INTER u)) finv /\
    (!x:A. x IN topspace top /\ x IN w INTER u ==> finv (f x) = x)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `homeomorphic_maps (subtopology top (w INTER u),
                         subtopology euclidean (IMAGE (h:A->real^3) (w INTER u)))
                        ((f:A->real^3),(finv:real^3->A))` THEN
    REWRITE_TAC[homeomorphic_maps; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN V /\ x IN u
          ==> (finv:real^3->A) (f x) = x /\
              (G:real^3->real^3) (h x) = f x /\
              (k1:real^3->real^3) (psi x) = f x /\
              f x IN IMAGE h (w INTER u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top /\ x IN w` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `topspace (top:A topology)`)) (concl th) &&
        can (find_term (fun t -> t = `finv:real^3->A`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `G:real^3->real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `k1:real^3->real^3`)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER];
      FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
        check (fun th -> free_in `f:A->real^3` (concl th) &&
                         fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism (IMAGE (psi:A->real^3) (V INTER u),IMAGE (f:A->real^3) (V INTER u))
                  ((k1:real^3->real^3),psi o (finv:real^3->A))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_GLUE_K2_HOMEOMORPHISM THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC MOI_GLUE_PSI_FINV_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `IMAGE (h:A->real^3) (w INTER u)`;
                          `w INTER u:A->bool`] THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN ASM_SIMP_TAC[];
      UNDISCH_TAC `homeomorphic_map (subtopology top V,
                                     subtopology euclidean (IMAGE (psi:A->real^3) V)) psi` THEN
      DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((G:real^3->real^3) o (h:A->real^3)) (u INTER V) =
    IMAGE (f:A->real^3) (V INTER u)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_GLUE_IMAGE_COMPOSE_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(psi:A->real^3) o (finv:real^3->A)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (psi:A->real^3) (V INTER u)`; `k1:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INTER; o_THM] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[]]);;

(* Chart gluing, part 5: the atlas after one gluing step.                    *)

let MOI_GLUE_SUB_ATLAS_CHART = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) w V phi.
        open_in top w /\ pl_manifold_atlas (subtopology top w) atlas /\
        (V,phi) IN atlas
        ==> open_in top V /\ V SUBSET w /\ open (IMAGE phi V) /\
            homeomorphic_map (subtopology top V,subtopology euclidean (IMAGE phi V))
                             phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology top w) (V:A->bool) /\ open (IMAGE (phi:A->real^N) V) /\
    homeomorphic_map (subtopology (subtopology top w) V,
                      subtopology euclidean (IMAGE phi V)) phi`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pl_manifold_atlas]; ALL_TAC] THEN
  SUBGOAL_THEN `(V:A->bool) SUBSET w` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_TRANS_FULL]; ALL_TAC] THEN
  UNDISCH_TAC `homeomorphic_map (subtopology (subtopology top w) V,
                                 subtopology euclidean (IMAGE (phi:A->real^N) V)) phi` THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `w INTER V:A->bool = V` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[]]);;

let MOI_GLUE_F_CHART = prove
 (`!(atlas:((A->bool)#(A->real^3))->bool) w u (f:A->real^3) V psi.
        pl_in_charts {(U INTER (w INTER u),phi) | U,phi | (U,phi) IN atlas} f /\
        (V,psi) IN atlas /\ V SUBSET w
        ==> ?k1. pl_map_on (IMAGE psi (V INTER u)) k1 /\
                 !x. x IN V INTER u ==> k1(psi x) = f x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_in_charts; MOI_GLUE_RESTRICT_IN] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`V INTER (w INTER u):A->bool`; `psi:A->real^3`]) THEN
  ANTS_TAC THENL [EXISTS_TAC `V:A->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `V INTER (w INTER u):A->bool = V INTER u` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[]]);;

let MOI_GLUE_STEP_ATLAS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) w u
    (h:A->real^3) hinv (f:A->real^3) finv (G:real^3->real^3) G'.
        open_in top w /\ open_in top u /\
        pl_manifold_atlas (subtopology top w) atlas /\
        homeomorphic_maps (subtopology top u,euclidean) (h,hinv) /\
        homeomorphic_maps (subtopology top (w INTER u),
                           subtopology euclidean (IMAGE h (w INTER u))) (f,finv) /\
        pl_in_charts {(U INTER (w INTER u),phi) | U,phi | (U,phi) IN atlas} f /\
        homeomorphism ((:real^3),(:real^3)) (G,G') /\
        (!x. x IN w /\ x IN u ==> G(h x) = f x)
        ==> pl_manifold_atlas (subtopology top (w UNION u))
                              ((u,G o h) INSERT atlas)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `w UNION u:A->bool`;
                 `h:A->real^3`; `hinv:real^3->A`; `G:real^3->real^3`;
                 `G':real^3->real^3`] MOI_GLUE_NEW_CHART) THEN
  ASM_REWRITE_TAC[SUBSET_UNION] THEN STRIP_TAC THEN
  REWRITE_TAC[pl_manifold_atlas; IN_INSERT; PAIR_EQ] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^3`] THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [ASM_REWRITE_TAC[OPEN_UNIV] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
        fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_map")) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `w:A->bool`; `V:A->bool`; `phi:A->real^3`]
                    MOI_GLUE_SUB_ATLAS_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_GLUE_OLD_CHART THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    X_GEN_TAC `x:A` THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_UNION] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `pl_manifold_atlas (subtopology top w)
                     (atlas:((A->bool)#(A->real^3))->bool)` THEN
      REWRITE_TAC[pl_manifold_atlas; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`u:A->bool`; `(G:real^3->real^3) o (h:A->real^3)`] THEN
      ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`V1:A->bool`; `phi1:A->real^3`;
                         `V2:A->bool`; `psi2:A->real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN STRIP_ASSUME_TAC)
                               (DISJ_CASES_THEN STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `\y:real^3. y` THEN ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
      ASM_SIMP_TAC[MOI_PL_MAP_ON_ID_OPEN; OPEN_UNIV];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `w:A->bool`; `V2:A->bool`; `psi2:A->real^3`]
                    MOI_GLUE_SUB_ATLAS_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `w:A->bool`;
                     `u:A->bool`; `f:A->real^3`; `V2:A->bool`; `psi2:A->real^3`]
                    MOI_GLUE_F_CHART) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `k1:real^3->real^3` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_GLUE_NEW_OLD THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `w:A->bool`; `f:A->real^3`;
                            `finv:real^3->A`; `k1:real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `w:A->bool`; `V1:A->bool`; `phi1:A->real^3`]
                    MOI_GLUE_SUB_ATLAS_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `w:A->bool`;
                     `u:A->bool`; `f:A->real^3`; `V1:A->bool`; `phi1:A->real^3`]
                    MOI_GLUE_F_CHART) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `k1:real^3->real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `k1:real^3->real^3` THEN ASM_REWRITE_TAC[o_THM] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN w /\ x IN u` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `pl_manifold_atlas (subtopology top w)
                     (atlas:((A->bool)#(A->real^3))->bool)` THEN
      REWRITE_TAC[pl_manifold_atlas] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[]]]);;


(* Chart gluing, part 6: one gluing step from the approximation theorem.    *)

let MOI_GLUE_CHART_OVERLAP = prove
 (`!(top:A topology) w u (h:A->real^3) hinv.
        open_in top w /\ open_in top u /\
        homeomorphic_maps (subtopology top u,euclidean) (h,hinv)
        ==> homeomorphic_map (subtopology top (w INTER u),
                              subtopology euclidean (IMAGE h (w INTER u))) h /\
            open (IMAGE h (w INTER u)) /\
            (!x. x IN w INTER u ==> hinv(h x) = x) /\
            (!y. h(hinv y) = y) /\
            IMAGE hinv (IMAGE h (w INTER u)) = w INTER u /\
            continuous_map (subtopology euclidean (IMAGE h (w INTER u)),
                            subtopology top (w INTER u)) hinv`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:A->bool) SUBSET topspace top /\ (u:A->bool) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
                              IN_UNIV; IN_INTER]) THEN
  SUBGOAL_THEN `!x:A. x IN w INTER u ==> (hinv:real^3->A) (h x) = x` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (hinv:real^3->A) (IMAGE (h:A->real^3) (w INTER u)) = w INTER u`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM IMAGE_ID] THEN
    MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `homeomorphic_map (subtopology top u,euclidean) (h:A->real^3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[HOMEOMORPHIC_MAPS_IMP_MAP]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (u:A->bool)`; `euclidean:(real^3)topology`;
                   `h:A->real^3`; `w INTER u:A->bool`;
                   `IMAGE (h:A->real^3) (w INTER u)`]
                  HOMEOMORPHIC_MAP_SUBTOPOLOGIES) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV;
                    SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(topspace top INTER u) INTER w INTER u:A->bool = w INTER u /\
                  u INTER w INTER u:A->bool = w INTER u`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM SET_TAC[]; REWRITE_TAC[]];
    MP_TAC(ISPECL [`h:A->real^3`; `subtopology top (u:A->bool)`;
                   `euclidean:(real^3)topology`; `w INTER u:A->bool`]
                  HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; OPEN_IN_EUCLIDEAN] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      UNDISCH_TAC `continuous_map (euclidean,subtopology top u) (hinv:real^3->A)` THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
      ASM SET_TAC[]]]);;

let MOI_GLUE_STEP = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) w u (h:A->real^3).
        MOISE_APPROX_STATEMENT (:A) /\ hausdorff_space top /\
        open_in top w /\ open_in top u /\
        pl_manifold_atlas (subtopology top w) atlas /\
        homeomorphic_map (subtopology top u,euclidean) h
        ==> ?atlas':((A->bool)#(A->real^3))->bool.
              pl_manifold_atlas (subtopology top (w UNION u)) atlas'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "approx") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `hinv:real^3->A` o GEN_REWRITE_RULE I
    [HOMEOMORPHIC_MAP_MAPS] o check (fun th -> is_comb (concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_map")) THEN
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `u:A->bool`; `h:A->real^3`;
                 `hinv:real^3->A`] MOI_GLUE_CHART_OVERLAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `topspace (subtopology top (w INTER u)) = w INTER u:A->bool`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_manifold_atlas (subtopology (top:A topology) (w INTER u))
      {(U INTER (w INTER u),phi) | U,phi |
       (U,phi) IN (atlas:((A->bool)#(A->real^3))->bool)}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (w:A->bool)`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `w INTER u:A->bool`]
                  MOI_GLUE_PL_ATLAS_RESTRICT) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `w INTER w INTER u:A->bool = w INTER u` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (h:A->real^3) (w INTER u)` MOI_GLUE_DD_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real^3->real` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "approx" (MP_TAC o SPECL
   [`subtopology top (w INTER u):A topology`;
    `{(U INTER (w INTER u),phi) | U,phi |
      (U,phi) IN (atlas:((A->bool)#(A->real^3))->bool)}`;
    `h:A->real^3`; `\x:A. (dd:real^3->real) (h x) / &2`] o
   GEN_REWRITE_RULE I [MOISE_APPROX_STATEMENT]) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY];
      MP_TAC(ISPECL [`subtopology top (w INTER u):A topology`;
                     `subtopology euclidean (IMAGE (h:A->real^3) (w INTER u))`;
                     `h:A->real^3`] MOI_GLUE_HOMEOMORPHIC_SECOND_COUNTABLE) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SECOND_COUNTABLE_SUBTOPOLOGY THEN
      REWRITE_TAC[MOI_GLUE_SECOND_COUNTABLE_EUCLIDEAN];
      ASM_REWRITE_TAC[embedding_map];
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
      SUBGOAL_THEN `(\x:A. (dd:real^3->real) (h x)) = dd o h` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_SIMP_TAC[MOI_GLUE_LIPSCHITZ_CONTINUOUS_MAP] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP o
        check (fun th -> is_comb (concl th) &&
          fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_map")) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < d ==> &0 < d / &2`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(h:A->real^3) x` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?finv. homeomorphic_maps (subtopology top (w INTER u),
                              subtopology euclidean (IMAGE (h:A->real^3) (w INTER u)))
                             ((f:A->real^3),finv)`
  (X_CHOOSE_TAC `finv:real^3->A`) THENL
   [REWRITE_TAC[GSYM HOMEOMORPHIC_MAP_MAPS] THEN
    UNDISCH_TAC `embedding_map (subtopology top (w INTER u),euclidean) (f:A->real^3)` THEN
    ASM_REWRITE_TAC[embedding_map];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:A. x IN w INTER u ==> (finv:real^3->A) (f x) = x) /\
    continuous_map (subtopology top (w INTER u),euclidean) (f:A->real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `homeomorphic_maps (subtopology top (w INTER u),
                         subtopology euclidean (IMAGE (h:A->real^3) (w INTER u)))
                        ((f:A->real^3),(finv:real^3->A))` THEN
    ASM_REWRITE_TAC[homeomorphic_maps; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (h:A->real^3) (w INTER u)`;
                 `(f:A->real^3) o (hinv:real^3->A)`; `dd:real^3->real`]
                MOI_GLUE_GLUED_HOMEOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology top (w INTER u:A->bool)` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IMAGE_o];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; o_THM] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `(finv:real^3->A) (f(x:A)) = x /\ finv (f y) = y`
      (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `G':real^3->real^3`) THEN
  EXISTS_TAC `((u:A->bool),
               (\y:real^3. if y IN IMAGE (h:A->real^3) (w INTER u)
                           then ((f:A->real^3) o (hinv:real^3->A)) y else y) o h)
              INSERT (atlas:((A->bool)#(A->real^3))->bool)` THEN
  MATCH_MP_TAC MOI_GLUE_STEP_ATLAS THEN
  MAP_EVERY EXISTS_TAC [`hinv:real^3->A`; `f:A->real^3`; `finv:real^3->A`;
                        `G':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:A->real^3) x IN IMAGE h (w INTER u)` (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term (fun t -> t = `hinv:real^3->A`)) (concl th) &&
    is_forall (concl th) &&
    can (find_term (fun t -> t = `w INTER u:A->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* Chart gluing, part 7: induction over finitely many charts; the theorem.  *)

let MOI_GLUE_FINITE_CHARTS = prove
 (`!(top:A topology) (charts:((A->bool)#(A->real^3))->bool).
        MOISE_APPROX_STATEMENT (:A) /\ hausdorff_space top /\ FINITE charts /\
        (!u h. (u,h) IN charts
               ==> open_in top u /\ homeomorphic_map (subtopology top u,euclidean) h)
        ==> ?atlas:((A->bool)#(A->real^3))->bool.
              pl_manifold_atlas (subtopology top (UNIONS (IMAGE FST charts))) atlas`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0] THEN
    EXISTS_TAC `{}:((A->bool)#(A->real^3))->bool` THEN
    REWRITE_TAC[pl_manifold_atlas; NOT_IN_EMPTY; TOPSPACE_SUBTOPOLOGY; INTER_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A->bool`; `h:A->real^3`;
                       `s:((A->bool)#(A->real^3))->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `atlas:((A->bool)#(A->real^3))->bool`) THEN
  REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN
  ONCE_REWRITE_TAC[UNION_COMM] THEN
  MATCH_MP_TAC MOI_GLUE_STEP THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `h:A->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open_in top (u:A->bool) /\
                homeomorphic_map (subtopology top u,euclidean) (h:A->real^3)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; FST] THEN
  ASM_MESON_TAC[IN_INSERT]);;

let MOI_CHART_GLUING = prove
 (`!u:A->bool. MOISE_APPROX_STATEMENT u ==> MOISE_PL_ATLAS_STATEMENT u`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MOISE_PL_ATLAS_STATEMENT] THEN
  X_GEN_TAC `top:A topology` THEN STRIP_TAC THEN
  SUBGOAL_THEN `MOISE_APPROX_STATEMENT (:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `MOISE_APPROX_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[MOISE_APPROX_STATEMENT];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_SPACE] o
    check (fun th -> concl th = `compact_space (top:A topology)`)) THEN
  DISCH_THEN(MP_TAC o SPEC
   `{U:A->bool | open_in top U /\
                 subtopology top U homeomorphic_space (euclidean:(real^3)topology)}`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN MESON_TAC[OPEN_IN_SUBSET];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      UNDISCH_TAC `locally_euclidean_space (:3) (top:A topology)` THEN
      REWRITE_TAC[locally_euclidean_space] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?hh:(A->bool)->A->real^3.
      !U. U IN V ==> homeomorphic_map (subtopology top U,euclidean) (hh U)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `U:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `subtopology top (U:A->bool) homeomorphic_space (euclidean:(real^3)topology)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[homeomorphic_space] THEN MESON_TAC[HOMEOMORPHIC_MAPS_IMP_MAP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `IMAGE (\U:A->bool. U,(hh:(A->bool)->A->real^3) U) V`]
                MOI_GLUE_FINITE_CHARTS) THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (IMAGE FST (IMAGE (\U:A->bool. U,(hh:(A->bool)->A->real^3) U) V)) =
    topspace top`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF; FST; IMAGE_ID] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBTOPOLOGY_TOPSPACE]]);;


