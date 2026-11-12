(* ========================================================================= *)
(* pc_moi_fnd_surfc: the torus recognition of the Moise PL core (Moise      *)
(* GTM 47, 22.4-22.5 with m = 0 and h = 1, pp.161-163).  Main theorem       *)
(*   SURFACE_EULER_TORUS : |- MOI_FND_SURFACE_TORUS  (pc_moi_fnd_stmt.ml):  *)
(* a finite connected nonempty orientable combinatorial 2-manifold with     *)
(* Euler characteristic 0 is PL homeomorphic to pl_torus_model.             *)
(* Route, in the order of the sections below:                               *)
(*   -   graph lemmas: forest count, spanning forests, cycle extraction;    *)
(*   -   a non-separating polygon in a closed surface with chi < 2         *)
(*       (tree and cotree: MOI_FSA_TREE and MOI_FSA_COTREE);                 *)
(*   -   connectedness of the cut (MOI_FSC_CUT_CONNECTED);                  *)
(*   -   the cut along its bicollar is a PL annulus (STRIP_REMOVE and       *)
(*       SURFACE_EULER_PLANAR);                                              *)
(*   -   the assembly over pl_torus_model (MOI_FSC_TORUS_GLUE);             *)
(*   -   a product structure on the annulus matching the strip at both ends *)
(*       (HOLED_EXT; ORIENT and COLLAR of pc_moi_s33_circ; MOI_FSC_ENDS);    *)
(*   -   the twisted (Klein bottle) matching is impossible, by the bicollar *)
(*       theorem for a curve with a Moebius band neighbourhood              *)
(*       (MOI_FSC_NO_KLEIN);                                                 *)
(*   -   the main theorem.                                                   *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_cbicol.ml";;
needs "src/pc_moi_s28_plane.ml";;
needs "src/pc_moi_s28_tria.ml";;
needs "src/pc_moi_s33_hext.ml";;
needs "src/pc_moi_lt_sphere.ml";;
needs "src/pc_moi_sch3_lev.ml";;
needs "src/pc_moi_s33_circ.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Graph lemmas on abstract vertex sets.                                     *)
(* (a) Forests of a dual graph: a set tr of edges, each in exactly two      *)
(*     triangles of d, such that every nonempty part of tr has a triangle   *)
(*     meeting it in exactly one edge (the form of MOI_FSA_TREE), has at    *)
(*     most CARD d - 1 edges; with exactly CARD d - 1 edges it spans d.     *)
(* (b) A finite graph with at least as many edges as vertices contains a    *)
(*     simple cycle of length at least 3 (remove vertices of degree at      *)
(*     most 1; when all degrees are at least 2, close a longest path).      *)
(* ========================================================================= *)

let MOI_FSC_CARD1_MEMBER = prove
 (`!s:A->bool. CARD s = 1 ==> ?x. x IN s`,
  GEN_TAC THEN REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `CARD({}:A->bool) = 1` THEN REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC);;

let MOI_FSC_CARD_LE1 = prove
 (`!s:A->bool. (!x y. x IN s /\ y IN s ==> x = y) ==> CARD s <= 1`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?z:A. s SUBSET {z}` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `s:A->bool = {}` THENL
     [ASM_REWRITE_TAC[EMPTY_SUBSET];
      FIRST_X_ASSUM(X_CHOOSE_TAC `z:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      EXISTS_TAC `z:A` THEN REWRITE_TAC[SUBSET; IN_SING] THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {z:A}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_SING];
      REWRITE_TAC[CARD_SING; LE_REFL]]]);;

(* (a) Forest count, by removing a leaf triangle and its edge.              *)

let MOI_FSC_FOREST_COUNT_N = prove
 (`!n (d:(A->bool)->bool) tr.
     CARD tr = n /\ FINITE d /\ FINITE tr /\ ~(d = {}) /\
     (!e. e IN tr ==> CARD {t | t IN d /\ e SUBSET t} = 2) /\
     (!xx. xx SUBSET tr /\ ~(xx = {})
           ==> ?t. t IN d /\ CARD {e | e IN xx /\ e SUBSET t} = 1)
     ==> CARD tr + 1 <= CARD d`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `tr:(A->bool)->bool = {}` SUBST1_TAC THENL
     [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[CARD_CLAUSES; ADD_CLAUSES; ARITH_RULE `1 <= n <=> ~(n = 0:num)`] THEN
    ASM_MESON_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "two") (LABEL_TAC "acyc")))))) THEN
  SUBGOAL_THEN `~(tr:(A->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `CARD(tr:(A->bool)->bool) = SUC n` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "acyc" (MP_TAC o SPEC `tr:(A->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?e0:A->bool. {e | e IN tr /\ e SUBSET t0} = {e0}`
    (X_CHOOSE_TAC `e0:A->bool`) THENL
   [REWRITE_TAC[GSYM MOI_FSA_CARD_EQ_1] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `tr:(A->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e0:A->bool) IN tr /\ e0 SUBSET t0 /\
                (!e. e IN tr /\ e SUBSET t0 ==> e = e0)`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uniq"))) THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t1:A->bool. t1 IN d /\ e0 SUBSET t1 /\ ~(t1 = t0)` STRIP_ASSUME_TAC THENL
   [USE_THEN "two" (MP_TAC o SPEC `e0:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `~({t | t IN d /\ (e0:A->bool) SUBSET t} SUBSET {t0})` MP_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`{t | t IN d /\ (e0:A->bool) SUBSET t}`; `{t0:A->bool}`]
        CARD_SUBSET) THEN
      ASM_REWRITE_TAC[FINITE_SING; CARD_SING] THEN ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(d:(A->bool)->bool) DELETE t0`;
                                `(tr:(A->bool)->bool) DELETE e0`]) THEN
  ANTS_TAC THENL
   [SIMP_TAC[CARD_DELETE; FINITE_DELETE; ASSUME `FINITE (d:(A->bool)->bool)`;
             ASSUME `FINITE (tr:(A->bool)->bool)`; ASSUME `(t0:A->bool) IN d`;
             ASSUME `(e0:A->bool) IN tr`] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `CARD(tr:(A->bool)->bool) = SUC n` THEN ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DELETE] THEN
      EXISTS_TAC `t1:A->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `e:A->bool` THEN
      DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IN_DELETE]) THEN
      SUBGOAL_THEN `{t | t IN (d:(A->bool)->bool) DELETE t0 /\ (e:A->bool) SUBSET t} =
                    {t | t IN d /\ e SUBSET t}` SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN
        X_GEN_TAC `t:A->bool` THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((e:A->bool) = e0)` THEN REWRITE_TAC[] THEN
        USE_THEN "uniq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "two" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `xx:(A->bool)->bool` THEN STRIP_TAC THEN
      USE_THEN "acyc" (MP_TAC o SPEC `xx:(A->bool)->bool`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(xx:(A->bool)->bool) SUBSET tr DELETE e0` THEN
        REWRITE_TAC[SUBSET; IN_DELETE] THEN MESON_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      SUBGOAL_THEN `{e | e IN xx /\ (e:A->bool) SUBSET t0} = {}` ASSUME_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        X_GEN_TAC `e:A->bool` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(e:A->bool) IN tr /\ ~(e = e0)` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(e:A->bool) IN xx` THEN
          UNDISCH_TAC `(xx:(A->bool)->bool) SUBSET tr DELETE e0` THEN
          REWRITE_TAC[SUBSET; IN_DELETE] THEN MESON_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `~((e:A->bool) = e0)` THEN REWRITE_TAC[] THEN
        USE_THEN "uniq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `CARD {e | e IN xx /\ (e:A->bool) SUBSET t0} = 1` THEN
        ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC]];
    ALL_TAC] THEN
  SIMP_TAC[CARD_DELETE; ASSUME `FINITE (d:(A->bool)->bool)`;
           ASSUME `FINITE (tr:(A->bool)->bool)`; ASSUME `(t0:A->bool) IN d`;
           ASSUME `(e0:A->bool) IN tr`] THEN
  SUBGOAL_THEN `2 <= CARD(d:(A->bool)->bool)` MP_TAC THENL
   [MATCH_MP_TAC MOI_FSA_TWO THEN
    MAP_EVERY EXISTS_TAC [`t1:A->bool`; `t0:A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `CARD(tr:(A->bool)->bool) = SUC n` THEN ARITH_TAC);;

let MOI_FSC_FOREST_COUNT = prove
 (`!(d:(A->bool)->bool) tr.
     FINITE d /\ FINITE tr /\ ~(d = {}) /\
     (!e. e IN tr ==> CARD {t | t IN d /\ e SUBSET t} = 2) /\
     (!xx. xx SUBSET tr /\ ~(xx = {})
           ==> ?t. t IN d /\ CARD {e | e IN xx /\ e SUBSET t} = 1)
     ==> CARD tr + 1 <= CARD d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSC_FOREST_COUNT_N THEN
  EXISTS_TAC `CARD(tr:(A->bool)->bool)` THEN ASM_REWRITE_TAC[]);;

(* A dual forest with CARD d - 1 edges spans d: a nonempty set of triangles *)
(* closed under adjacency across forest edges is all of d.                  *)

let MOI_FSC_FOREST_SPAN = prove
 (`!(d:(A->bool)->bool) tr X.
     FINITE d /\ FINITE tr /\
     (!e. e IN tr ==> CARD {t | t IN d /\ e SUBSET t} = 2) /\
     (!xx. xx SUBSET tr /\ ~(xx = {})
           ==> ?t. t IN d /\ CARD {e | e IN xx /\ e SUBSET t} = 1) /\
     CARD tr + 1 = CARD d /\
     X SUBSET d /\ ~(X = {}) /\
     (!e t t'. e IN tr /\ t IN X /\ t' IN d /\ e SUBSET t /\ e SUBSET t'
               ==> t' IN X)
     ==> X = d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "two") (CONJUNCTS_THEN2 (LABEL_TAC "acyc")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Xd")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "clos")))))))) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `trx = {e | e IN tr /\ ?t:A->bool. t IN X /\ e SUBSET t}` THEN
  ABBREV_TAC `try = (tr:(A->bool)->bool) DIFF trx` THEN
  SUBGOAL_THEN
   `(!e:A->bool. e IN trx <=> e IN tr /\ ?t. t IN X /\ e SUBSET t) /\
    (!e:A->bool. e IN try <=> e IN tr /\ ~(?t. t IN X /\ e SUBSET t))`
  (CONJUNCTS_THEN2 (LABEL_TAC "mx") (LABEL_TAC "my")) THENL
   [MAP_EVERY EXPAND_TAC ["try"; "trx"] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(trx:(A->bool)->bool) SUBSET tr /\ (try:(A->bool)->bool) SUBSET tr`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(trx:(A->bool)->bool) /\ FINITE(try:(A->bool)->bool) /\
                FINITE(X:(A->bool)->bool) /\ FINITE((d:(A->bool)->bool) DIFF X)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THENL
     [EXISTS_TAC `tr:(A->bool)->bool`; EXISTS_TAC `tr:(A->bool)->bool`;
      EXISTS_TAC `d:(A->bool)->bool`; EXISTS_TAC `d:(A->bool)->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_DIFF];
    ALL_TAC] THEN
  (* both triangles of an edge of trx lie in X; none of an edge of try does *)
  SUBGOAL_THEN `!e t. e IN trx /\ t IN d /\ e SUBSET t ==> (t:A->bool) IN X`
  (LABEL_TAC "c1") THENL
   [USE_THEN "mx" (fun th -> REWRITE_TAC[th]) THEN REPEAT STRIP_TAC THEN
    USE_THEN "clos" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`e:A->bool`; `t':A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e t. e IN try /\ t IN X ==> ~((e:A->bool) SUBSET t)`
  (LABEL_TAC "c2") THENL
   [USE_THEN "my" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "mx" (K ALL_TAC) THEN REMOVE_THEN "my" (K ALL_TAC) THEN
  MP_TAC(ISPECL [`X:(A->bool)->bool`; `trx:(A->bool)->bool`] MOI_FSC_FOREST_COUNT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `e:A->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `{t | t IN X /\ (e:A->bool) SUBSET t} = {t | t IN d /\ e SUBSET t}`
      SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        X_GEN_TAC `t:A->bool` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
         [USE_THEN "Xd" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN ASM_REWRITE_TAC[];
          USE_THEN "c1" MATCH_MP_TAC THEN EXISTS_TAC `e:A->bool` THEN
          ASM_REWRITE_TAC[]];
        USE_THEN "two" MATCH_MP_TAC THEN
        UNDISCH_TAC `(trx:(A->bool)->bool) SUBSET tr` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `xx:(A->bool)->bool` THEN STRIP_TAC THEN
      USE_THEN "acyc" (MP_TAC o SPEC `xx:(A->bool)->bool`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `trx:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FSC_CARD1_MEMBER) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e1:A->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "c1" MATCH_MP_TAC THEN EXISTS_TAC `e1:A->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(xx:(A->bool)->bool) SUBSET trx` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(d:(A->bool)->bool) DIFF X`; `try:(A->bool)->bool`]
    MOI_FSC_FOREST_COUNT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~((X:(A->bool)->bool) = d)` THEN
      UNDISCH_TAC `(X:(A->bool)->bool) SUBSET d` THEN SET_TAC[];
      X_GEN_TAC `e:A->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `{t | t IN d DIFF X /\ (e:A->bool) SUBSET t} =
                    {t | t IN d /\ e SUBSET t}`
      SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
        X_GEN_TAC `t:A->bool` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN USE_THEN "c2" (MP_TAC o SPECL [`e:A->bool`; `t:A->bool`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
        USE_THEN "two" MATCH_MP_TAC THEN
        UNDISCH_TAC `(try:(A->bool)->bool) SUBSET tr` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `xx:(A->bool)->bool` THEN STRIP_TAC THEN
      USE_THEN "acyc" (MP_TAC o SPEC `xx:(A->bool)->bool`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `try:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FSC_CARD1_MEMBER) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e1:A->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(e1:A->bool) IN try` ASSUME_TAC THENL
       [UNDISCH_TAC `(xx:(A->bool)->bool) SUBSET try` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN USE_THEN "c2" (MP_TAC o SPECL [`e1:A->bool`; `t:A->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `CARD(trx:(A->bool)->bool) + CARD(try:(A->bool)->bool) =
                CARD(tr:(A->bool)->bool)` MP_TAC THENL
   [MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "try" THEN
    UNDISCH_TAC `(trx:(A->bool)->bool) SUBSET tr` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(X:(A->bool)->bool) + CARD((d:(A->bool)->bool) DIFF X) =
                CARD d` MP_TAC THENL
   [MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(X:(A->bool)->bool) SUBSET d` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `CARD(tr:(A->bool)->bool) + 1 = CARD(d:(A->bool)->bool)` THEN
  UNDISCH_TAC `CARD(trx:(A->bool)->bool) + 1 <= CARD(X:(A->bool)->bool)` THEN
  UNDISCH_TAC `CARD(try:(A->bool)->bool) + 1 <= CARD((d:(A->bool)->bool) DIFF X)` THEN
  ARITH_TAC);;

(* (b) Paths and cycles in a graph with vertex set w and edge set l.         *)

let moi_fsc_path = new_definition
 `moi_fsc_path (w:A->bool) (l:(A->bool)->bool) k (P:num->A) <=>
    (!i. i <= k ==> P i IN w) /\
    (!i j. i <= k /\ j <= k /\ P i = P j ==> i = j) /\
    (!i. i < k ==> {P i, P(SUC i)} IN l)`;;

let MOI_FSC_PATH_CARD = prove
 (`!(w:A->bool) l k P. FINITE w /\ moi_fsc_path w l k P ==> k + 1 <= CARD w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsc_path] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:num->A`; `{i:num | i <= k}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[CARD_NUMSEG_LE] THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]);;

let MOI_FSC_EDGE_OTHER = prove
 (`!e (v:A). e HAS_SIZE 2 /\ v IN e ==> ?x. ~(x = v) /\ e = {v,x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?x:A. x IN e /\ ~(x = v)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM;
      TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
    SUBGOAL_THEN `e SUBSET {v:A}` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_SUBSET o C CONJ (SPEC `v:A` FINITE_SING)) THEN
    REWRITE_TAC[CARD_SING] THEN RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSA_PAIR THEN
    ASM_MESON_TAC[]]);;

let MOI_FSC_EDGE_TWO = prove
 (`!e:A->bool. e HAS_SIZE 2 ==> ?a b. ~(a = b) /\ e = {a,b}`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?a:A. a IN e` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `(e:A->bool) HAS_SIZE 2` THEN
    ASM_REWRITE_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_EMPTY] THEN ARITH_TAC;
    MP_TAC(ISPECL [`e:A->bool`; `a:A`] MOI_FSC_EDGE_OTHER) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[]]);;

let MOI_FSC_SUC_MOD = prove
 (`!i n. 0 < n
         ==> (SUC i) MOD n = if i MOD n + 1 = n then 0 else i MOD n + 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((n:num) = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`i:num`; `n:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i DIV n + 1` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `i MOD n + 1 = n` THEN UNDISCH_TAC `i = i DIV n * n + i MOD n` THEN
    ARITH_TAC;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i DIV n` THEN
    UNDISCH_TAC `~(i MOD n + 1 = n)` THEN UNDISCH_TAC `i MOD n < n` THEN
    UNDISCH_TAC `i = i DIV n * n + i MOD n` THEN ARITH_TAC]);;

(* All degrees at least 2: close a longest path into a cycle.                *)

let MOI_FSC_MINDEG_CYCLE = prove
 (`!(w:A->bool) l.
     FINITE w /\ ~(w = {}) /\ (!e. e IN l ==> e HAS_SIZE 2 /\ e SUBSET w) /\
     (!v. v IN w ==> ?e1 e2. e1 IN l /\ e2 IN l /\ ~(e1 = e2) /\ v IN e1 /\ v IN e2)
     ==> ?n S. 3 <= n /\ (!i. S(i + n) = S i) /\
               (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
               (!i. {S i, S(SUC i)} IN l)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "edge") (LABEL_TAC "deg")))) THEN
  SUBGOAL_THEN
   `?k. (?P:num->A. moi_fsc_path w l k P) /\
        (!k'. (?P:num->A. moi_fsc_path w l k' P) ==> k' <= k)`
  (X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2
     (X_CHOOSE_TAC `P:num->A`) (LABEL_TAC "max"))) THENL
   [MP_TAC(ISPEC `\k. ?P:num->A. moi_fsc_path (w:A->bool) l k P` num_MAX) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `0:num` THEN
      FIRST_X_ASSUM(X_CHOOSE_TAC `v:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      EXISTS_TAC `\i:num. (v:A)` THEN
      REWRITE_TAC[moi_fsc_path; LE; LT] THEN ASM_MESON_TAC[];
      EXISTS_TAC `CARD(w:A->bool)` THEN X_GEN_TAC `k:num` THEN
      DISCH_THEN(X_CHOOSE_TAC `P:num->A`) THEN
      MP_TAC(ISPECL [`w:A->bool`; `l:(A->bool)->bool`; `k:num`; `P:num->A`]
        MOI_FSC_PATH_CARD) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_fsc_path (w:A->bool) l k (P:num->A)` THEN
  REWRITE_TAC[moi_fsc_path] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pw")
    (CONJUNCTS_THEN2 (LABEL_TAC "pinj") (LABEL_TAC "pe"))) THEN
  SUBGOAL_THEN `(P:num->A) 0 IN w` ASSUME_TAC THENL
   [USE_THEN "pw" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  (* an edge at P 0 other than the path edge *)
  SUBGOAL_THEN `?u:A. {(P:num->A) 0, u} IN l /\ ~(u = P 0) /\ (0 < (k:num) ==> ~(u = P 1))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "deg" (MP_TAC o SPEC `(P:num->A) 0`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:A->bool` (X_CHOOSE_THEN `e2:A->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`e1:A->bool`; `(P:num->A) 0`] MOI_FSC_EDGE_OTHER) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`e2:A->bool`; `(P:num->A) 0`] MOI_FSC_EDGE_OTHER) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x2:A` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `0 < (k:num) /\ (x1:A) = (P:num->A) 1` THENL
     [EXISTS_TAC `x2:A` THEN
      SUBGOAL_THEN `~((x2:A) = x1)` MP_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~((e1:A->bool) = e2)` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `x1:A` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `?j. j <= k /\ (P:num->A) j = u` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `2 <= (j:num)` ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `~(j = 0) /\ ~(j = 1) ==> 2 <= j:num`) THEN CONJ_TAC THEN
      DISCH_THEN SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[];
        SUBGOAL_THEN `0 < (k:num)` ASSUME_TAC THENL
         [UNDISCH_TAC `1 <= (k:num)` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `(j:num) + 1` THEN EXISTS_TAC `\i. (P:num->A)(i MOD (j + 1))` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `2 <= (j:num)` THEN ARITH_TAC;
      GEN_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[ARITH_RULE `i + j + 1 = 1 * (j + 1) + i:num`] THEN
      REWRITE_TAC[MOD_MULT_ADD];
      MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `i MOD (j + 1) = i /\ i' MOD (j + 1) = i'` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(P:num->A)(i MOD (j + 1)) = P(i' MOD (j + 1))` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(i:num) < j + 1` THEN UNDISCH_TAC `(i':num) < j + 1` THEN
      UNDISCH_TAC `(j:num) <= k` THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN
      MP_TAC(SPECL [`i:num`; `(j:num) + 1`] MOI_FSC_SUC_MOD) THEN
      ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `i MOD (j + 1) < j + 1` ASSUME_TAC THENL
       [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THENL
       [SUBGOAL_THEN `i MOD (j + 1) = j` SUBST1_TAC THENL
         [UNDISCH_TAC `i MOD (j + 1) + 1 = j + 1` THEN ARITH_TAC; ALL_TAC] THEN
        ONCE_REWRITE_TAC[INSERT_COMM] THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `i MOD (j + 1) + 1 = SUC(i MOD (j + 1))` SUBST1_TAC THENL
         [ARITH_TAC; ALL_TAC] THEN
        USE_THEN "pe" MATCH_MP_TAC THEN
        UNDISCH_TAC `i MOD (j + 1) < j + 1` THEN
        UNDISCH_TAC `~(i MOD (j + 1) + 1 = j + 1)` THEN
        UNDISCH_TAC `(j:num) <= k` THEN ARITH_TAC]];
    ALL_TAC] THEN
  (* u is new: the longer path u, P 0, ..., P k contradicts maximality *)
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  USE_THEN "max" (MP_TAC o SPEC `SUC k`) THEN
  REWRITE_TAC[ARITH_RULE `~(SUC k <= k)`] THEN
  EXISTS_TAC `\i:num. if i = 0 then (u:A) else (P:num->A)(i - 1)` THEN
  REWRITE_TAC[moi_fsc_path] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [USE_THEN "edge" (MP_TAC o SPEC `{(P:num->A) 0, u}`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SET_TAC[];
      USE_THEN "pw" MATCH_MP_TAC THEN
      UNDISCH_TAC `i <= SUC k` THEN UNDISCH_TAC `~((i:num) = 0)` THEN ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN
    ASM_CASES_TAC `(i:num) = 0` THEN ASM_CASES_TAC `(i':num) = 0` THEN ASM_REWRITE_TAC[] THENL
     [STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~(?j. j <= k /\ (P:num->A) j = u)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `(i':num) - 1` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `i' <= SUC k` THEN ARITH_TAC;
      STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~(?j. j <= k /\ (P:num->A) j = u)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `(i:num) - 1` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `i <= SUC k` THEN ARITH_TAC;
      STRIP_TAC THEN
      SUBGOAL_THEN `(i:num) - 1 = i' - 1` MP_TAC THENL
       [USE_THEN "pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `i <= SUC k` THEN UNDISCH_TAC `i' <= SUC k` THEN ARITH_TAC;
        UNDISCH_TAC `~((i:num) = 0)` THEN UNDISCH_TAC `~((i':num) = 0)` THEN ARITH_TAC]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
    COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INSERT_COMM] THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(P:num->A) i = P(SUC(i - 1))` SUBST1_TAC THENL
       [AP_TERM_TAC THEN UNDISCH_TAC `~((i:num) = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      USE_THEN "pe" MATCH_MP_TAC THEN
      UNDISCH_TAC `i < SUC k` THEN UNDISCH_TAC `~((i:num) = 0)` THEN ARITH_TAC]]);;

(* The cycle lemma, by induction on the number of vertices.                  *)

let MOI_FSC_GRAPH_CYCLE = prove
 (`!(w:A->bool) l.
     FINITE w /\ (!e. e IN l ==> e HAS_SIZE 2 /\ e SUBSET w) /\ ~(l = {}) /\
     CARD w <= CARD l
     ==> ?n S. 3 <= n /\ (!i. S(i + n) = S i) /\
               (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
               (!i. {S i, S(SUC i)} IN l)`,
  SUBGOAL_THEN
   `!m (w:A->bool) l.
      CARD w = m /\ FINITE w /\ (!e. e IN l ==> e HAS_SIZE 2 /\ e SUBSET w) /\
      ~(l = {}) /\ CARD w <= CARD l
      ==> ?n S. 3 <= n /\ (!i. S(i + n) = S i) /\
                (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
                (!i. {S i, S(SUC i)} IN l)`
  (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN
             MAP_EVERY EXISTS_TAC [`CARD(w:A->bool)`; `w:A->bool`] THEN
             ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`w:A->bool`; `l:(A->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "edge") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  SUBGOAL_THEN `FINITE(l:(A->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{e:A->bool | e SUBSET w}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `!v:A. v IN w ==> ?e1 e2. e1 IN l /\ e2 IN l /\ ~(e1 = e2) /\ v IN e1 /\ v IN e2`
  THENL
   [MATCH_MP_TAC MOI_FSC_MINDEG_CYCLE THEN EXISTS_TAC `w:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `e:A->bool` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    USE_THEN "edge" (MP_TAC o SPEC `e:A->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MOI_FSC_EDGE_TWO) ASSUME_TAC) THEN
    STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  ABBREV_TAC `l' = {e | e IN l /\ ~((v:A) IN e)}` THEN
  SUBGOAL_THEN `CARD {e | e IN l /\ (v:A) IN e} <= 1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSC_CARD_LE1 THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(l:(A->bool)->bool) <= CARD(l':(A->bool)->bool) + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(l':(A->bool)->bool) + CARD {e | e IN l /\ (v:A) IN e}` THEN
    ASM_REWRITE_TAC[LE_ADD_LCANCEL] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD((l':(A->bool)->bool) UNION {e | e IN l /\ (v:A) IN e})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
       [EXPAND_TAC "l'" THEN SET_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(A->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "l'" THEN SET_TAC[]];
      MATCH_MP_TAC CARD_UNION_LE THEN CONJ_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(A->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "l'" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(l':(A->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `CARD(l:(A->bool)->bool) <= CARD(l':(A->bool)->bool) + 1` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES; ADD_CLAUSES] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `e:A->bool` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    USE_THEN "edge" (MP_TAC o SPEC `e:A->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MOI_FSC_EDGE_TWO) ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `2 <= CARD(w:A->bool)` MP_TAC THENL
     [MATCH_MP_TAC MOI_FSA_TWO THEN MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      UNDISCH_TAC `CARD(w:A->bool) <= CARD(l:(A->bool)->bool)` THEN
      UNDISCH_TAC `CARD(l:(A->bool)->bool) <= 1` THEN ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPEC `CARD((w:A->bool) DELETE v)`) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[CARD_DELETE] THEN
    SUBGOAL_THEN `~(CARD(w:A->bool) = 0)` MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `CARD(w:A->bool) = m` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(w:A->bool) DELETE v`; `l':(A->bool)->bool`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN CONJ_TAC THENL
     [EXPAND_TAC "l'" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `e:A->bool` THEN
      STRIP_TAC THEN USE_THEN "edge" (MP_TAC o SPEC `e:A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM SET_TAC[];
      UNDISCH_TAC `CARD(w:A->bool) <= CARD(l:(A->bool)->bool)` THEN
      UNDISCH_TAC `CARD(l:(A->bool)->bool) <= CARD(l':(A->bool)->bool) + 1` THEN
      UNDISCH_TAC `CARD(w:A->bool) = m` THEN ARITH_TAC];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  EXPAND_TAC "l'" THEN SIMP_TAC[IN_ELIM_THM]);;

(* ========================================================================= *)
(* A non-separating polygon in a closed surface with chi < 2 (Moise 22.4,    *)
(* closed case; tree and cotree). For d = moi_fsa_abs c take a dual spanning *)
(* tree tr (MOI_FSA_TREE, spanning by the forest count). chi < 2 leaves at   *)
(* least V cotree edges, so the cotree contains a cycle (the cycle lemma);   *)
(* its edges form a 2-regular graph, i.e. a 1-complex whose components are   *)
(* PL circles (MOI_S4L_CM1_CIRCLES). The open triangles and the open tree    *)
(* edges miss the cycle and connect the complement.                          *)
(* ========================================================================= *)

(* Periodic sequences and the cycle as a 2-regular edge set.                 *)

let MOI_FSC_PERIODIC_MOD = prove
 (`!(S:num->A) n. (!i. S(i + n) = S i) ==> !i. S i = S(i MOD n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!q r. (S:num->A)(q * n + r) = S r` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `(a + n) + r = (a + r) + n:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(n:num) = 0` THEN ASM_REWRITE_TAC[MOD_ZERO] THEN
  MP_TAC(SPECL [`i:num`; `n:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CONJUNCT1 th]) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FSC_CYCLE_SUC = prove
 (`!(S:num->A) n k. (!i. S(i + n) = S i) /\ k < n
                    ==> S(SUC k) = S(if k + 1 = n then 0 else k + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0:num`) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    UNDISCH_TAC `(k:num) + 1 = n` THEN ARITH_TAC;
    REWRITE_TAC[ADD1]]);;

let MOI_FSC_CYCLE_2REG = prove
 (`!(S:num->A) n.
     3 <= n /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j)
     ==> ~({{S i, S(SUC i)} | i < n} = {}) /\
         !v. v IN UNIONS {{S i, S(SUC i)} | i < n}
             ==> CARD {e | e IN {{S i, S(SUC i)} | i < n} /\ v IN e} = 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "per")
    (LABEL_TAC "inj"))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `{(S:num->A) 0, S(SUC 0)}` THEN EXISTS_TAC `0:num` THEN
    REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < n ==> (S:num->A)(SUC k) = S(if k + 1 = n then 0 else k + 1) /\
                  (if k + 1 = n then 0 else k + 1) < n`
  (LABEL_TAC "suc") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSC_CYCLE_SUC THEN ASM_REWRITE_TAC[];
      COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(k:num) < n` THEN UNDISCH_TAC `~((k:num) + 1 = n)` THEN ARITH_TAC];
    ALL_TAC] THEN
  (* every vertex is some S k with k < n *)
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `v:A` THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:A->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `i0:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k. k < n /\ v = (S:num->A) k` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [EXISTS_TAC `i0:num` THEN ASM_REWRITE_TAC[];
      USE_THEN "suc" (MP_TAC o SPEC `i0:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ABBREV_TAC `p = if (k:num) = 0 then (n:num) - 1 else k - 1` THEN
  SUBGOAL_THEN `p < n /\ (S:num->A)(SUC p) = S k /\
                (!i. i < n /\ S(SUC i) = S k ==> i = p)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "p" THEN UNDISCH_TAC `3 <= (n:num)` THEN UNDISCH_TAC `(k:num) < n` THEN
      ARITH_TAC;
      EXPAND_TAC "p" THEN COND_CASES_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "per" (MP_TAC o SPEC `0:num`) THEN REWRITE_TAC[ADD_CLAUSES] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
        UNDISCH_TAC `3 <= (n:num)` THEN ARITH_TAC;
        AP_TERM_TAC THEN UNDISCH_TAC `~((k:num) = 0)` THEN ARITH_TAC];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      USE_THEN "suc" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(if (i:num) + 1 = n then 0 else i + 1) = k` MP_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "p" THEN
      UNDISCH_TAC `3 <= (n:num)` THEN UNDISCH_TAC `(k:num) < n` THEN
      UNDISCH_TAC `(i:num) < n` THEN
      REPEAT(COND_CASES_TAC THEN POP_ASSUM MP_TAC) THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{e | (?i. i < n /\ e = {S i, S(SUC i)}) /\ (S:num->A) k IN e} =
    {{S k, S(SUC k)}, {S p, S(SUC p)}}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
       [DISJ1_TAC THEN SUBGOAL_THEN `k:num = i` (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN SUBGOAL_THEN `i:num = p` SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
           [FIRST_ASSUM ACCEPT_TAC;
            CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC];
          REWRITE_TAC[ASSUME `(S:num->A)(SUC p) = S k`]]];
      STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT] THENL
       [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the two edges are different *)
  SUBGOAL_THEN `~({(S:num->A) k, S(SUC k)} = {S p, S(SUC p)})` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(S:num->A)(SUC k) = S p \/ S(SUC k) = S k` MP_TAC THENL
     [UNDISCH_TAC `{(S:num->A) k, S(SUC k)} = {S p, S k}` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "suc" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `(if (k:num) + 1 = n then 0 else k + 1) = p` MP_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "p" THEN UNDISCH_TAC `3 <= (n:num)` THEN UNDISCH_TAC `(k:num) < n` THEN
      ARITH_TAC;
      SUBGOAL_THEN `(if (k:num) + 1 = n then 0 else k + 1) = k` MP_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `3 <= (n:num)` THEN UNDISCH_TAC `(k:num) < n` THEN ARITH_TAC];
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY;
           ASSUME `~({(S:num->A) k, S(SUC k)} = {S p, S(SUC p)})`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MOI_FSC_GRAPH_2REG = prove
 (`!(w:A->bool) l.
     FINITE w /\ (!e. e IN l ==> e HAS_SIZE 2 /\ e SUBSET w) /\ ~(l = {}) /\
     CARD w <= CARD l
     ==> ?Y. Y SUBSET l /\ ~(Y = {}) /\
             !v. v IN UNIONS Y ==> CARD {e | e IN Y /\ v IN e} = 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FSC_GRAPH_CYCLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `S:num->A` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`S:num->A`; `n:num`] MOI_FSC_CYCLE_2REG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{{(S:num->A) i, S(SUC i)} | i < n}` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* Geometry of the abstract surface of a closed combinatorial surface.       *)

let MOI_FSC_ABS_FACTS = prove
 (`!c:(real^N->bool)->bool t.
     FINITE c /\ combinatorial_manifold 2 c /\ t IN moi_fsa_abs c
     ==> ~affine_dependent t /\ t HAS_SIZE 3 /\ convex hull t IN c /\
         aff_dim(convex hull t) = &2 /\
         !s. s SUBSET t ==> convex hull s IN c /\ ~affine_dependent s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  UNDISCH_TAC `(t:real^N->bool) IN moi_fsa_abs c` THEN
  REWRITE_TAC[moi_fsa_abs; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `T0:real^N->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) HAS_SIZE 3` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s SUBSET moi_fsa_vs (T0:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      EXISTS_TAC `moi_fsa_vs (T0:real^N->bool)` THEN ASM_REWRITE_TAC[]]]);;

let MOI_FSC_ABS_EDGE_FACTS = prove
 (`!c:(real^N->bool)->bool e.
     FINITE c /\ combinatorial_manifold 2 c /\ e IN moi_fsa_edges (moi_fsa_abs c)
     ==> e HAS_SIZE 2 /\ ~affine_dependent e /\ convex hull e IN c /\
         aff_dim(convex hull e) = &1 /\
         !s. s SUBSET e ==> convex hull s IN c /\ ~affine_dependent s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSC_ABS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent (e:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_REFL];
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ASM_MESON_TAC[SUBSET_TRANS]]);;

(* The segments of a 2-regular set of edges contain a PL circle.             *)

let MOI_FSC_SEG_CIRCLE = prove
 (`!c:(real^N->bool)->bool Y.
     FINITE c /\ combinatorial_manifold 2 c /\
     Y SUBSET moi_fsa_edges (moi_fsa_abs c) /\ ~(Y = {}) /\
     (!v. v IN UNIONS Y ==> CARD {e | e IN Y /\ v IN e} = 2)
     ==> ?J. pl_sphere 1 J /\ J SUBSET moi_fsa_poly Y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "deg"))))) THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN Y
        ==> e HAS_SIZE 2 /\ ~affine_dependent e /\ convex hull e IN c /\
            aff_dim(convex hull e) = &1 /\
            !s. s SUBSET e ==> convex hull s IN c /\ ~affine_dependent (s:real^N->bool)`
  (LABEL_TAC "ef") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FSC_ABS_EDGE_FACTS THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Y:(real^N->bool)->bool) SUBSET moi_fsa_edges (moi_fsa_abs c)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_geom (moi_fsa_abs (c:(real^N->bool)->bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_ABS_GEOM]; ALL_TAC] THEN
  ABBREV_TAC `K = {convex hull s | s | ?e. e IN Y /\ s SUBSET (e:real^N->bool)}` THEN
  SUBGOAL_THEN `(K:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `f:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) SUBST1_TAC)) THEN
    USE_THEN "ef" (MP_TAC o SPEC `e:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o last o CONJUNCTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* K is a simplicial complex *)
  SUBGOAL_THEN `simplicial_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET];
      UNDISCH_TAC `(K:(real^N->bool)->bool) SUBSET c` THEN REWRITE_TAC[SUBSET] THEN
      ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `s:real^N->bool`] THEN
      EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s0:real^N->bool`
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC)) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~affine_dependent (s0:real^N->bool)` ASSUME_TAC THENL
       [USE_THEN "ef" (MP_TAC o SPEC `e:real^N->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `s0:real^N->bool` o last o CONJUNCTS) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s0:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(K:(real^N->bool)->bool) SUBSET c` THEN REWRITE_TAC[SUBSET] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* dimensions and degrees *)
  SUBGOAL_THEN `!f:real^N->bool. f IN K ==> aff_dim f <= &1` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `f:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) SUBST1_TAC)) THEN
    USE_THEN "ef" (MP_TAC o SPEC `e:real^N->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    TRANS_TAC INT_LE_TRANS `aff_dim(convex hull (e:real^N->bool))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC AFF_DIM_SUBSET THEN MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[INT_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. {v} IN K ==> CARD {f | f IN K /\ aff_dim f = &1 /\ v IN f} = 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `e0:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `(v:real^N) IN e0` ASSUME_TAC THENL
     [SUBGOAL_THEN `(v:real^N) IN convex hull s` MP_TAC THENL
       [UNDISCH_TAC `{v:real^N} = convex hull s` THEN SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `s SUBSET {v:real^N}` MP_TAC THENL
       [UNDISCH_TAC `{v:real^N} = convex hull s` THEN
        MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `s:real^N->bool`] HULL_SUBSET) THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `s:real^N->bool = {}` THENL
       [ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
        UNDISCH_TAC `s SUBSET (e0:real^N->bool)` THEN
        UNDISCH_TAC `~(s:real^N->bool = {})` THEN SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `{v:real^N} = convex hull s`)) THEN
    SUBGOAL_THEN
     `{f | (?s. (?e. e IN Y /\ s SUBSET e) /\ f = convex hull s) /\
           aff_dim f = &1 /\ (v:real^N) IN f} =
      IMAGE (\e. convex hull e) {e | e IN Y /\ v IN e}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:real^N->bool` THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
       [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s1:real^N->bool`
          (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)
          ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `f:real^N->bool`)) THEN
        USE_THEN "ef" (MP_TAC o SPEC `e:real^N->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `s1:real^N->bool = e` SUBST_ALL_TAC THENL
         [MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `~affine_dependent (s1:real^N->bool)` ASSUME_TAC THENL
           [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `e:real^N->bool` THEN
            ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          UNDISCH_TAC `aff_dim(convex hull (s1:real^N->bool)) = &1` THEN
          ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
          REWRITE_TAC[INT_ARITH `a - &1:int = &1 <=> a = &2`; INT_OF_NUM_EQ];
          ALL_TAC] THEN
        EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        (* a vertex in a segment of the complex is an end *)
        UNDISCH_TAC `moi_fsa_geom (moi_fsa_abs (c:(real^N->bool)->bool))` THEN
        REWRITE_TAC[moi_fsa_geom] THEN
        DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `e:real^N->bool`] o CONJUNCT2) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [UNDISCH_TAC `(e0:real^N->bool) IN Y` THEN
            UNDISCH_TAC `(Y:(real^N->bool)->bool) SUBSET
                         moi_fsa_edges (moi_fsa_abs c)` THEN
            GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
            DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
            REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN
            DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
            EXISTS_TAC `t:real^N->bool` THEN CONJ_TAC THENL
             [ASM_REWRITE_TAC[];
              UNDISCH_TAC `(v:real^N) IN e0` THEN
              UNDISCH_TAC `(e0:real^N->bool) SUBSET t` THEN SET_TAC[]];
            UNDISCH_TAC `(e:real^N->bool) IN Y` THEN
            UNDISCH_TAC `(Y:(real^N->bool)->bool) SUBSET
                         moi_fsa_edges (moi_fsa_abs c)` THEN
            GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
            DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
            REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN MESON_TAC[]];
          ALL_TAC] THEN
        REWRITE_TAC[CONVEX_HULL_SING] THEN
        ASM_CASES_TAC `(v:real^N) IN e` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `{v:real^N} INTER e = {}` SUBST1_TAC THENL
         [UNDISCH_TAC `~((v:real^N) IN e)` THEN SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[CONVEX_HULL_EMPTY] THEN
        UNDISCH_TAC `(v:real^N) IN convex hull e` THEN SET_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 SUBST1_TAC
          STRIP_ASSUME_TAC)) THEN
        USE_THEN "ef" (MP_TAC o SPEC `e:real^N->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [EXISTS_TAC `e:real^N->bool` THEN REWRITE_TAC[] THEN
          EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
          MATCH_MP_TAC(SET_RULE `!s t (v:real^N). s SUBSET t /\ v IN s ==> v IN t`) THEN
          EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[HULL_SUBSET]]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `CARD {e | e IN Y /\ (v:real^N) IN e}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN
        MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN STRIP_TAC THEN
        USE_THEN "ef" (MP_TAC o SPEC `e1:real^N->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN
        USE_THEN "ef" (MP_TAC o SPEC `e2:real^N->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN
        MP_TAC(ISPEC `e1:real^N->bool` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
        MP_TAC(ISPEC `e2:real^N->bool` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `Y:(real^N->bool)->bool` THEN
        CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `moi_fsa_edges (moi_fsa_abs (c:(real^N->bool)->bool))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSA_EDGES_FINITE THEN
        MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSA_ABS_SURF) THEN
        ASM_REWRITE_TAC[moi_fsa_surf] THEN MESON_TAC[HAS_SIZE]];
      USE_THEN "deg" MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the components of |K| are PL circles *)
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `e:real^N->bool` o GEN_REWRITE_RULE I
      [GSYM MEMBER_NOT_EMPTY] o check (fun th -> concl th = `~(Y:(real^N->bool)->bool = {})`)) THEN
    USE_THEN "ef" (MP_TAC o SPEC `e:real^N->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `(e:real^N->bool) IN Y` THEN
    UNDISCH_TAC `(Y:(real^N->bool)->bool) SUBSET moi_fsa_edges (moi_fsa_abs c)` THEN
    REWRITE_TAC[SUBSET; moi_fsa_edges; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSC_ABS_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `convex hull (t:real^N->bool)` AFF_DIM_LE_UNIV) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN
    REWRITE_TAC[INT_ARITH `&2:int <= &n <=> &2 <= &n`; INT_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `K:(real^N->bool)->bool` MOI_S4L_CM1_CIRCLES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(UNIONS (K:(real^N->bool)->bool) = {})` MP_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `e:real^N->bool` o GEN_REWRITE_RULE I
      [GSYM MEMBER_NOT_EMPTY] o check (fun th -> concl th = `~(Y:(real^N->bool)->bool = {})`)) THEN
    SUBGOAL_THEN `convex hull (e:real^N->bool) IN K` MP_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `e:real^N->bool` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    USE_THEN "ef" (MP_TAC o SPEC `e:real^N->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REWRITE_TAC[HAS_SIZE] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(convex hull (e:real^N->bool) = {})` MP_TAC THENL
     [REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN DISCH_TAC THEN
      UNDISCH_TAC `CARD(e:real^N->bool) = 2` THEN ASM_REWRITE_TAC[CARD_CLAUSES] THEN
      ARITH_TAC;
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPONENTS_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `J:real^N->bool`) THEN EXISTS_TAC `J:real^N->bool` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (K:(real^N->bool)->bool)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  EXPAND_TAC "K" THEN REWRITE_TAC[moi_fsa_poly; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `f:real^N->bool`)) THEN
  EXISTS_TAC `convex hull (e:real^N->bool)` THEN CONJ_TAC THENL
   [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `s:real^N->bool`; `e:real^N->bool`]
      HULL_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN convex hull s` THEN REWRITE_TAC[SUBSET] THEN
    MESON_TAC[]]);;

(* The complement of a set inside the cotree segments is connected.         *)

let MOI_FSC_RELINT_MISS = prove
 (`!d (t:real^N->bool) e.
     moi_fsa_geom d /\ t IN d /\ t HAS_SIZE 3 /\ e HAS_SIZE 2 /\
     (?t'. t' IN d /\ e SUBSET t')
     ==> relative_interior(convex hull t) INTER convex hull e = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_geom] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent (t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull t INTER convex hull e =
                convex hull (t INTER e:real^N->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (t INTER e:real^N->bool) face_of convex hull t /\
                ~(convex hull (t INTER e) = convex hull t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `t INTER e:real^N->bool` THEN REWRITE_TAC[INTER_SUBSET];
      DISCH_TAC THEN
      MP_TAC(ISPEC `t:real^N->bool` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      MP_TAC(ISPEC `t INTER e:real^N->bool` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
        ASM_REWRITE_TAC[INTER_SUBSET];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `CARD(t:real^N->bool) <= CARD(e:real^N->bool)` MP_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN
        RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex hull (t INTER e:real^N->bool)`; `convex hull t:real^N->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `convex hull t INTER convex hull e =
               convex hull (t INTER e:real^N->bool)` THEN
  MP_TAC(ISPEC `convex hull t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  SET_TAC[]);;

(* A union of connected sets is connected if the sets meet along a relation *)
(* that connects the index set.                                              *)

let MOI_FSC_CONNECTED_UNIONS_SPAN = prove
 (`!(P:B->real^N->bool) d R.
     (!t. t IN d ==> connected (P t)) /\
     (!t t'. t IN d /\ t' IN d /\ R t t' ==> ~(P t INTER P t' = {})) /\
     (!X. X SUBSET d /\ ~(X = {}) /\ (!t t'. t IN X /\ t' IN d /\ R t t' ==> t' IN X)
          ==> X = d)
     ==> connected (UNIONS (IMAGE P d))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "conn") (CONJUNCTS_THEN2 (LABEL_TAC "meet")
    (LABEL_TAC "span"))) THEN
  GEN_REWRITE_TAC I [connected] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t:B. t IN d ==> e1 INTER P t = {} \/ e2 INTER (P:B->real^N->bool) t = {}`
  (LABEL_TAC "side") THENL
   [X_GEN_TAC `t:B` THEN DISCH_TAC THEN
    USE_THEN "conn" (MP_TAC o SPEC `t:B`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [connected] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(P:B->real^N->bool) t SUBSET UNIONS (IMAGE P d)` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `UNIONS (IMAGE (P:B->real^N->bool) d) SUBSET e1 UNION e2` THEN
    UNDISCH_TAC `e1 INTER e2 INTER UNIONS (IMAGE (P:B->real^N->bool) d) = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "span" (MP_TAC o SPEC `{t:B | t IN d /\ e2 INTER (P:B->real^N->bool) t = {}}`) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SET_TAC[];
      UNDISCH_TAC `~(e1 INTER UNIONS (IMAGE (P:B->real^N->bool) d) = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `g:real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `t:B` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
      EXISTS_TAC `t:B` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "side" (MP_TAC o SPEC `t:B`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^N) IN g` THEN UNDISCH_TAC `(y:real^N) IN e1` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`t:B`; `t':B`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "meet" (MP_TAC o SPECL [`t:B`; `t':B`]) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "side" (MP_TAC o SPEC `t':B`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(P:B->real^N->bool) t SUBSET e1` MP_TAC THENL
       [SUBGOAL_THEN `(P:B->real^N->bool) t SUBSET UNIONS (IMAGE P d)` MP_TAC THENL
         [REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `UNIONS (IMAGE (P:B->real^N->bool) d) SUBSET e1 UNION e2` THEN
        UNDISCH_TAC `e2 INTER (P:B->real^N->bool) t = {}` THEN SET_TAC[];
        SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `g:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t:B` STRIP_ASSUME_TAC) ASSUME_TAC))) o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS; IN_IMAGE] o
    check (fun th -> concl th =
      `~(e2 INTER UNIONS (IMAGE (P:B->real^N->bool) d) = {})`)) THEN
  SUBGOAL_THEN `e2 INTER (P:B->real^N->bool) t = {}` MP_TAC THENL
   [UNDISCH_TAC `{t:B | t IN d /\ e2 INTER (P:B->real^N->bool) t = {}} = d` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `t:B`) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(y:real^N) IN g` THEN UNDISCH_TAC `(y:real^N) IN e2` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_FSC_COMPLEMENT_CONN = prove
 (`!c:(real^N->bool)->bool tr Y J.
     FINITE c /\ combinatorial_manifold 2 c /\
     tr SUBSET moi_fsa_edges (moi_fsa_abs c) /\ FINITE tr /\
     CARD tr + 1 = CARD (moi_fsa_abs c) /\
     (!e. e IN tr ==> CARD {t | t IN moi_fsa_abs c /\ e SUBSET t} = 2) /\
     (!xx. xx SUBSET tr /\ ~(xx = {})
           ==> ?t. t IN moi_fsa_abs c /\ CARD {e | e IN xx /\ e SUBSET t} = 1) /\
     Y SUBSET moi_fsa_edges (moi_fsa_abs c) DIFF tr /\ J SUBSET moi_fsa_poly Y
     ==> connected (UNIONS c DIFF J)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "two")
    (CONJUNCTS_THEN2 (LABEL_TAC "acyc") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
  ABBREV_TAC `d = moi_fsa_abs (c:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `moi_fsa_surf (d:(real^N->bool)->bool) /\ moi_fsa_geom d /\
                moi_fsa_poly d = UNIONS c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    ASM_SIMP_TAC[MOI_FSA_ABS_SURF; MOI_FSA_ABS_GEOM; MOI_FSA_ABS_POLY];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (d:(real^N->bool)->bool) /\ (!t. t IN d ==> t HAS_SIZE 3)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_fsa_surf]; ALL_TAC] THEN
  (* the pieces P t = conv t DIFF J *)
  SUBGOAL_THEN
   `!t:real^N->bool. t IN d ==> relative_interior(convex hull t) INTER J = {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `!P. r INTER P = {} /\ (J:real^N->bool) SUBSET P ==> r INTER J = {}`) THEN
    EXISTS_TAC `moi_fsa_poly (Y:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_fsa_poly; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FSC_RELINT_MISS THEN EXISTS_TAC `d:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(e:real^N->bool) IN Y` THEN
    UNDISCH_TAC `(Y:(real^N->bool)->bool) SUBSET moi_fsa_edges d DIFF tr` THEN
    REWRITE_TAC[SUBSET; IN_DIFF; moi_fsa_edges; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^N->bool. t IN d ==> connected (convex hull t DIFF J) /\
                                ~(convex hull t DIFF J = {})`
  (LABEL_TAC "pconn") THENL
   [X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(relative_interior(convex hull (t:real^N->bool)) = {})`
    ASSUME_TAC THENL
     [SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_CONVEX_HULL;
               CONVEX_HULL_EQ_EMPTY] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) HAS_SIZE 3` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_EMPTY] THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
      EXISTS_TAC `relative_interior(convex hull (t:real^N->bool))` THEN
      SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR; CONVEX_CONVEX_HULL] THEN
      SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CONVEX_CONVEX_HULL] THEN
      SUBGOAL_THEN `closure(convex hull t) = convex hull (t:real^N->bool)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN ASM_MESON_TAC[HAS_SIZE];
        ALL_TAC] THEN
      MP_TAC(ISPEC `convex hull t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      MP_TAC(ISPEC `convex hull t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* adjacent triangles across a tree edge share a point off J *)
  SUBGOAL_THEN
   `!e t t':real^N->bool.
      e IN tr /\ t IN d /\ t' IN d /\ e SUBSET t /\ e SUBSET t'
      ==> ~((convex hull t DIFF J) INTER (convex hull t' DIFF J) = {})`
  (LABEL_TAC "adj") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:real^N->bool) HAS_SIZE 2` MP_TAC THENL
     [UNDISCH_TAC `(e:real^N->bool) IN tr` THEN
      UNDISCH_TAC `(tr:(real^N->bool)->bool) SUBSET moi_fsa_edges d` THEN
      REWRITE_TAC[SUBSET; moi_fsa_edges; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC) o MATCH_MP MOI_FSC_EDGE_TWO) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `midpoint(a:real^N,b)` THEN
    SUBGOAL_THEN `midpoint(a:real^N,b) IN convex hull e /\
                  ~(midpoint(a,b) IN e)` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; MIDPOINT_IN_SEGMENT] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; MIDPOINT_EQ_ENDPOINT] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(midpoint(a:real^N,b) IN J)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `midpoint(a:real^N,b) IN moi_fsa_poly Y` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[moi_fsa_poly; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      SUBGOAL_THEN `(f:real^N->bool) IN moi_fsa_edges d /\ ~(f IN tr)`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `f:real^N->bool`; `e:real^N->bool`]
        MOI_FSA_OPEN_EDGE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(f:real^N->bool) IN moi_fsa_edges d` THEN
        REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSA_PAIR_SIZE THEN ASM_REWRITE_TAC[];
          ASM_MESON_TAC[];
          ASM_MESON_TAC[];
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `!s. (x:real^N) IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `convex hull e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_MONO THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* a separation would split the spanning tree *)
  SUBGOAL_THEN
   `UNIONS c DIFF J = UNIONS (IMAGE (\t:real^N->bool. convex hull t DIFF J) d)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `moi_fsa_poly (d:(real^N->bool)->bool) = UNIONS c` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[moi_fsa_poly] THEN
    REWRITE_TAC[UNIONS_GSPEC; UNIONS_IMAGE; EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSC_CONNECTED_UNIONS_SPAN THEN
  EXISTS_TAC `\t t':real^N->bool. ?e. e IN tr /\ e SUBSET t /\ e SUBSET t'` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "pconn" (MP_TAC o SPEC `t:real^N->bool`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `t':real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC))) THEN
    USE_THEN "adj" MATCH_MP_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `X:(real^N->bool)->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FSC_FOREST_SPAN THEN
    EXISTS_TAC `tr:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

(* PL circles are nonempty.                                                  *)

let MOI_FSC_SPHERE1_NE = prove
 (`!j:real^N->bool. pl_sphere 1 j ==> ~(j = {})`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_FSTR_PL_SPHERE1_HOMEO) THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC `(j:real^N->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC);;

(* The non-separating polygon.                                               *)

let MOI_FSC_NONSEP_CLOSED = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {}) /\ complex_euler c < &2
     ==> ?l:(real^N->bool)->bool.
           FINITE l /\ combinatorial_manifold 1 l /\ connected (UNIONS l) /\
           ~(UNIONS l = {}) /\ pl_sphere 1 (UNIONS l) /\ UNIONS l SUBSET UNIONS c /\
           connected (UNIONS c DIFF UNIONS l)`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = moi_fsa_abs (c:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `moi_fsa_surf (d:(real^N->bool)->bool) /\ moi_fsa_geom d /\
                moi_fsa_dconn d /\ moi_fsa_poly d = UNIONS c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    ASM_SIMP_TAC[MOI_FSA_ABS_SURF; MOI_FSA_ABS_GEOM; MOI_FSA_ABS_DCONN;
                 MOI_FSA_ABS_POLY];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (d:(real^N->bool)->bool) /\ (!t. t IN d ==> t HAS_SIZE 3) /\
                (!e. e IN moi_fsa_edges d ==> CARD {t | t IN d /\ e SUBSET t} = 2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_fsa_surf]; ALL_TAC] THEN
  SUBGOAL_THEN `~(d:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `moi_fsa_poly (d:(real^N->bool)->bool) = UNIONS c` THEN
    ASM_REWRITE_TAC[MOI_FSA_POLY_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `d:(real^N->bool)->bool` MOI_FSA_TREE) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tr:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* counting: at least V cotree edges *)
  SUBGOAL_THEN `FINITE (moi_fsa_edges (d:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_EDGES_FINITE THEN ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(UNIONS (d:(real^N->bool)->bool)) <= CARD(moi_fsa_edges d DIFF tr)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_DIFF] THEN
    MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSA_ABS_COUNTS) THEN
    MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSA_CM_EULER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
      (ASSUME_TAC o SYM))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&(CARD {v:real^N | {v} IN c}) -
                 &(CARD {e:real^N->bool | e IN c /\ aff_dim e = &1}) +
                 &(CARD {t:real^N->bool | t IN c /\ aff_dim t = &2}) < &2` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `CARD(tr:(real^N->bool)->bool) <= CARD(moi_fsa_edges (d:(real^N->bool)->bool))`
    MP_TAC THENL [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `CARD(tr:(real^N->bool)->bool) + 1 = CARD(d:(real^N->bool)->bool)` THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_ARITH `a - b + c < &2 <=> a + c < b + &2`;
                REAL_OF_NUM_LT] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (d:(real^N->bool)->bool)`; `moi_fsa_edges (d:(real^N->bool)->bool) DIFF tr`]
    MOI_FSC_GRAPH_2REG) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_UNIONS] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[HAS_SIZE];
      REWRITE_TAC[IN_DIFF; moi_fsa_edges; IN_ELIM_THM] THEN SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `CARD(UNIONS (d:(real^N->bool)->bool)) = 0` MP_TAC THENL
       [UNDISCH_TAC `CARD(UNIONS (d:(real^N->bool)->bool)) <=
                     CARD(moi_fsa_edges d DIFF tr)` THEN
        ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `FINITE(UNIONS (d:(real^N->bool)->bool))` ASSUME_TAC THENL
       [ASM_SIMP_TAC[FINITE_UNIONS] THEN ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_EQ_0; EMPTY_UNIONS] THEN
      UNDISCH_TAC `~(d:(real^N->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t:real^N->bool`) THEN
      DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) HAS_SIZE 3` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_EMPTY] THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `Y:(real^N->bool)->bool`]
    MOI_FSC_SEG_CIRCLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP POLYGON_COMPLEX) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:(real^N->bool)->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FSC_SPHERE1_NE];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_fsa_poly (Y:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_fsa_poly (d:(real^N->bool)->bool) = UNIONS c` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[moi_fsa_poly] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `?t:real^N->bool. t IN d /\ e SUBSET t` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(e:real^N->bool) IN Y` THEN
      UNDISCH_TAC `(Y:(real^N->bool)->bool) SUBSET moi_fsa_edges d DIFF tr` THEN
      REWRITE_TAC[SUBSET; IN_DIFF; moi_fsa_edges; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `convex hull t:real^N->bool` THEN CONJ_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `e:real^N->bool`; `t:real^N->bool`]
      HULL_MONO) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC MOI_FSC_COMPLEMENT_CONN THEN
    MAP_EVERY EXISTS_TAC [`tr:(real^N->bool)->bool`; `Y:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Connectedness of the cut, MOI_FSC_CUT_CONNECTED. If s DIFF m is connected *)
(* and w SUBSET s for a bicollar p of the compact set m, then the rest of s  *)
(* after removing the open strip of levels -1/2 < t < 1/2 is connected.      *)
(* Proof: the retraction r of s DIFF m onto the rest is the identity there   *)
(* and sends p(x,t) with 0 < abs t < 1/2 to the level of the sign of t; it   *)
(* is continuous on the three closed pieces (the rest, and s DIFF m meeting  *)
(* the two closed half strips), and the rest is its image                    *)
(* (CONNECTED_CONTINUOUS_IMAGE).                                             *)
(* ========================================================================= *)

(* Membership in an image of the bicollar, through the coordinate q.        *)

let MOI_FSC_CC_COORD = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q (tt:real^1->bool) y.
     moi_s26_bicollar m w p q /\ tt SUBSET interval[--vec 1,vec 1]
     ==> (y IN IMAGE p (m PCROSS tt) <=> y IN w /\ sndcart(q y) IN tt)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `pastecart (x:real^N) (t:real^1) IN m PCROSS interval[--vec 1,vec 1]`
    ASSUME_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(t:real^1) IN tt` THEN
      UNDISCH_TAC `(tt:real^1->bool) SUBSET interval[--vec 1,vec 1]` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SNDCART_PASTECART] THEN
    UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                       (m PCROSS interval[--vec 1,vec 1]) = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(q:real^N->real^(N,1)finite_sum) y` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(q:real^N->real^(N,1)finite_sum) y IN m PCROSS interval[--vec 1,vec 1]`
    MP_TAC THENL
     [UNDISCH_TAC `IMAGE (q:real^N->real^(N,1)finite_sum) w =
                   m PCROSS interval[--vec 1,vec 1]` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM_SIMP_TAC[]]);;

(* The inverse q on w, and p on m x [-1,1].                                 *)

let MOI_FSC_CC_WFACTS = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q.
     moi_s26_bicollar m w p q
     ==> (!y. y IN w ==> fstcart(q y) IN m /\
                         p(pastecart (fstcart(q y)) (sndcart(q y))) = y) /\
         (!x t. x IN m /\ t IN interval[--vec 1,vec 1]
                ==> p(pastecart x t) IN w /\ q(p(pastecart x t)) = pastecart x t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [REWRITE_TAC[PASTECART_FST_SND] THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(q:real^N->real^(N,1)finite_sum) y IN m PCROSS interval[--vec 1,vec 1]`
    MP_TAC THENL
     [UNDISCH_TAC `IMAGE (q:real^N->real^(N,1)finite_sum) w =
                   m PCROSS interval[--vec 1,vec 1]` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      SIMP_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART]];
    SUBGOAL_THEN `pastecart (x:real^N) (t:real^1) IN m PCROSS interval[--vec 1,vec 1]`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `IMAGE (p:real^(N,1)finite_sum->real^N)
                       (m PCROSS interval[--vec 1,vec 1]) = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* m is the level 0, through q.                                             *)

let MOI_FSC_CC_IN_M = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q.
     moi_s26_bicollar m w p q
     ==> !y. y IN m <=> y IN w /\ drop(sndcart(q y)) = &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN
  SUBGOAL_THEN `m = IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS {vec 0:real^1})`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [moi_s26_bicollar]) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`; `{vec 0:real^1}`; `y:real^N`]
    MOI_FSC_CC_COORD) THEN
  ASM_REWRITE_TAC[SING_SUBSET; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_SING; GSYM DROP_EQ; DROP_VEC]);;

(* The open strip and the two closed half strips, through q.                *)

let MOI_FSC_CC_LEVELS = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q.
     moi_s26_bicollar m w p q
     ==> (!y. y IN moi_s26_strip m p (--(&1 / &2)) (&1 / &2) <=>
              y IN w /\ --(&1 / &2) < drop(sndcart(q y)) /\ drop(sndcart(q y)) < &1 / &2) /\
         (!y. y IN IMAGE p (m PCROSS interval[lift(&0),lift(&1 / &2)]) <=>
              y IN w /\ &0 <= drop(sndcart(q y)) /\ drop(sndcart(q y)) <= &1 / &2) /\
         (!y. y IN IMAGE p (m PCROSS interval[lift(--(&1 / &2)),lift(&0)]) <=>
              y IN w /\ --(&1 / &2) <= drop(sndcart(q y)) /\ drop(sndcart(q y)) <= &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_s26_strip] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `y:real^N` THENL
   [MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`;
                   `{x:real^1 | --(&1 / &2) < drop x /\ drop x < &1 / &2}`; `y:real^N`]
      MOI_FSC_CC_COORD);
    MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`;
                   `interval[lift(&0),lift(&1 / &2)]`; `y:real^N`]
      MOI_FSC_CC_COORD);
    MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`;
                   `interval[lift(--(&1 / &2)),lift(&0)]`; `y:real^N`]
      MOI_FSC_CC_COORD)] THEN
  (ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
   ANTS_TAC THENL [GEN_TAC THEN REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]));;

(* A closed half strip is compact.                                           *)

let MOI_FSC_CC_COMPACT = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q a b.
     moi_s26_bicollar m w p q /\ compact m /\ --(&1) <= a /\ b <= &1
     ==> compact (IMAGE p (m PCROSS interval[lift a,lift b]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `(m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG;
              DROP_VEC; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The push to a level c is continuous on any subset of w.                  *)

let MOI_FSC_CC_SIDE_CONT = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q u c.
     moi_s26_bicollar m w p q /\ u SUBSET w /\ --(&1) <= c /\ c <= &1
     ==> (\y. p(pastecart (fstcart(q y)) (lift c))) continuous_on u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_FSC_CC_WFACTS) THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q` THEN
  REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. (p:real^(N,1)finite_sum->real^N) (pastecart (fstcart(q y)) (lift c))) =
    p o (\y. pastecart (fstcart((q:real^N->real^(N,1)finite_sum) y)) (lift c))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    SUBGOAL_THEN `(\y. fstcart((q:real^N->real^(N,1)finite_sum) y)) = fstcart o q`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                    DROP_NEG; DROP_VEC; LIFT_DROP] THEN
    ASM_MESON_TAC[SUBSET]]);;

(* The levels -1/2 and 1/2 miss the open strip.                              *)

let MOI_FSC_CC_LEVEL_OUT = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q x c.
     moi_s26_bicollar m w p q /\ x IN m /\ (c = &1 / &2 \/ c = --(&1 / &2))
     ==> p(pastecart x (lift c)) IN w /\
         ~(p(pastecart x (lift c)) IN moi_s26_strip m p (--(&1 / &2)) (&1 / &2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `lift c IN interval[--vec 1:real^1,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:real^N`; `lift c`] (CONJUNCT2 (MATCH_MP MOI_FSC_CC_WFACTS
    (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `(p:real^(N,1)finite_sum->real^N) (pastecart x (lift c))`
    (CONJUNCT1 (MATCH_MP MOI_FSC_CC_LEVELS
    (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`)))) THEN
  ASM_REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC);;

(* On the two closed half strips (off m) the retraction is the push to the  *)
(* level 1/2, respectively -1/2.                                             *)

let MOI_FSC_CC_SIDE_EQ = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q y.
     moi_s26_bicollar m w p q /\ y IN w /\ ~(y IN m)
     ==> (&0 <= drop(sndcart(q y)) /\ drop(sndcart(q y)) <= &1 / &2
          ==> p(pastecart (fstcart(q y)) (lift(&1 / &2))) =
              (if y IN moi_s26_strip m p (--(&1 / &2)) (&1 / &2)
               then p(pastecart (fstcart(q y))
                        (lift(if &0 < drop(sndcart(q y)) then &1 / &2 else --(&1 / &2))))
               else y)) /\
         (--(&1 / &2) <= drop(sndcart(q y)) /\ drop(sndcart(q y)) <= &0
          ==> p(pastecart (fstcart(q y)) (lift(--(&1 / &2)))) =
              (if y IN moi_s26_strip m p (--(&1 / &2)) (&1 / &2)
               then p(pastecart (fstcart(q y))
                        (lift(if &0 < drop(sndcart(q y)) then &1 / &2 else --(&1 / &2))))
               else y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `y:real^N` (MATCH_MP MOI_FSC_CC_IN_M
    (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`))) THEN
  MP_TAC(SPEC `y:real^N` (CONJUNCT1 (MATCH_MP MOI_FSC_CC_LEVELS
    (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`)))) THEN
  MP_TAC(SPEC `y:real^N` (CONJUNCT1 (MATCH_MP MOI_FSC_CC_WFACTS
    (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  CONJ_TAC THEN STRIP_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `&0 < drop(sndcart((q:real^N->real^(N,1)finite_sum) y))`
      (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `lift(&1 / &2) = sndcart((q:real^N->real^(N,1)finite_sum) y)`
      SUBST1_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `~(&0 < drop(sndcart((q:real^N->real^(N,1)finite_sum) y)))`
      (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `lift(--(&1 / &2)) = sndcart((q:real^N->real^(N,1)finite_sum) y)`
      SUBST1_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

(* Pasting a function continuous on three closed pieces.                    *)

let MOI_FSC_CC_PASTE3 = prove
 (`!(f:real^M->real^N) u a b c.
     u = a UNION b UNION c /\
     closed_in (subtopology euclidean u) a /\ closed_in (subtopology euclidean u) b /\
     closed_in (subtopology euclidean u) c /\
     f continuous_on a /\ f continuous_on b /\ f continuous_on c
     ==> f continuous_on u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_UNION THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
    EXISTS_TAC `a UNION b UNION c:real^M->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* The topological core, with the bicollar coordinate tau as a parameter.  *)

let MOI_FSC_CC_TOPO = prove
 (`!(s:real^N->bool) m w st kp km (tau:real^N->real) (r:real^N->real^N).
     w SUBSET s /\
     (!y. y IN m <=> y IN w /\ tau y = &0) /\
     (!y. y IN st <=> y IN w /\ --(&1 / &2) < tau y /\ tau y < &1 / &2) /\
     (!y. y IN kp <=> y IN w /\ &0 <= tau y /\ tau y <= &1 / &2) /\
     (!y. y IN km <=> y IN w /\ --(&1 / &2) <= tau y /\ tau y <= &0) /\
     closed kp /\ closed km /\ closed (s DIFF st) /\
     (!y. y IN s DIFF st ==> r y = y) /\
     r continuous_on ((s DIFF m) INTER kp) /\ r continuous_on ((s DIFF m) INTER km) /\
     IMAGE r (s DIFF m) SUBSET s DIFF st /\
     connected (s DIFF m)
     ==> connected (s DIFF st)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(m:real^N->bool) SUBSET st` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->real^N) continuous_on (s DIFF m)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSC_CC_PASTE3 THEN
    MAP_EVERY EXISTS_TAC [`s DIFF st:real^N->bool`; `(s DIFF m) INTER kp:real^N->bool`;
                          `(s DIFF m) INTER km:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN
      ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `(y:real^N) IN w` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:real^N) IN s` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `(w:real^N->bool) SUBSET s` THEN UNDISCH_TAC `(y:real^N) IN w` THEN
        SET_TAC[];
        REAL_ARITH_TAC];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(m:real^N->bool) SUBSET st` THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `\y:real^N. y` THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (r:real^N->real^N) (s DIFF m) = s DIFF st` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `y:real^N` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN s DIFF st` THEN UNDISCH_TAC `(m:real^N->bool) SUBSET st` THEN
    SET_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]]);;

let MOI_FSC_CUT_CONNECTED = prove
 (`!(s:real^N->bool) m w (p:real^(N,1)finite_sum->real^N) q.
     moi_s26_bicollar m w p q /\ w SUBSET s /\ compact m /\
     connected (s DIFF m) /\
     closed (s DIFF moi_s26_strip m p (--(&1 / &2)) (&1 / &2))
     ==> connected (s DIFF moi_s26_strip m p (--(&1 / &2)) (&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FSC_CC_TOPO THEN
  MAP_EVERY EXISTS_TAC
   [`m:real^N->bool`; `w:real^N->bool`;
    `IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS interval[lift(&0),lift(&1 / &2)])`;
    `IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS interval[lift(--(&1 / &2)),lift(&0)])`;
    `\y:real^N. drop(sndcart((q:real^N->real^(N,1)finite_sum) y))`;
    `\y:real^N. if y IN moi_s26_strip m p (--(&1 / &2)) (&1 / &2)
                then (p:real^(N,1)finite_sum->real^N)
                       (pastecart (fstcart((q:real^N->real^(N,1)finite_sum) y))
                          (lift(if &0 < drop(sndcart(q y)) then &1 / &2 else --(&1 / &2))))
                else y`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_FSC_CC_IN_M);
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o MATCH_MP MOI_FSC_CC_LEVELS);
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP MOI_FSC_CC_LEVELS);
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT2 o CONJUNCT2 o MATCH_MP MOI_FSC_CC_LEVELS);
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_FSC_CC_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`w:real^N->bool`; `q:real^N->real^(N,1)finite_sum`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_FSC_CC_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`w:real^N->bool`; `q:real^N->real^(N,1)finite_sum`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\y:real^N. (p:real^(N,1)finite_sum->real^N)
                  (pastecart (fstcart((q:real^N->real^(N,1)finite_sum) y)) (lift(&1 / &2)))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
      MP_TAC(SPEC `y:real^N` (CONJUNCT1 (CONJUNCT2 (MATCH_MP MOI_FSC_CC_LEVELS
        (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`))))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                    `q:real^N->real^(N,1)finite_sum`; `y:real^N`] MOI_FSC_CC_SIDE_EQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[];
      MATCH_MP_TAC MOI_FSC_CC_SIDE_CONT THEN
      MAP_EVERY EXISTS_TAC [`m:real^N->bool`; `w:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(CONJUNCT1 (CONJUNCT2 (MATCH_MP MOI_FSC_CC_LEVELS
          (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`)))) THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF] THEN MESON_TAC[];
        CONV_TAC REAL_RAT_REDUCE_CONV]];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\y:real^N. (p:real^(N,1)finite_sum->real^N)
                  (pastecart (fstcart((q:real^N->real^(N,1)finite_sum) y))
                    (lift(--(&1 / &2))))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
      MP_TAC(SPEC `y:real^N` (CONJUNCT2 (CONJUNCT2 (MATCH_MP MOI_FSC_CC_LEVELS
        (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`))))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                    `q:real^N->real^(N,1)finite_sum`; `y:real^N`] MOI_FSC_CC_SIDE_EQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[];
      MATCH_MP_TAC MOI_FSC_CC_SIDE_CONT THEN
      MAP_EVERY EXISTS_TAC [`m:real^N->bool`; `w:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(CONJUNCT2 (CONJUNCT2 (MATCH_MP MOI_FSC_CC_LEVELS
          (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`)))) THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF] THEN MESON_TAC[];
        CONV_TAC REAL_RAT_REDUCE_CONV]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `y:real^N` (CONJUNCT1 (MATCH_MP MOI_FSC_CC_LEVELS
      (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `y:real^N` (CONJUNCT1 (MATCH_MP MOI_FSC_CC_WFACTS
      (ASSUME `moi_s26_bicollar (m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q`)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`;
                   `fstcart((q:real^N->real^(N,1)finite_sum) y)`;
                   `if &0 < drop(sndcart((q:real^N->real^(N,1)finite_sum) y))
                    then &1 / &2 else --(&1 / &2)`]
      MOI_FSC_CC_LEVEL_OUT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(w:real^N->bool) SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The cut.  For a closed orientable surface c and a polygon                *)
(* |l| with connected complement: the bicollar of |l|                       *)
(* (CURVE_BICOLLAR_ORIENTABLE), the removal of the open strip between the   *)
(* levels -1/2 and 1/2 (STRIP_REMOVE), connectedness of the rest (a         *)
(* retraction of |c| minus |l| onto it), the two boundary circles, and the  *)
(* chart from the holed disk model with one hole (SURFACE_EULER_PLANAR,     *)
(* k = 1) when chi c = 0.                                                    *)
(* ========================================================================= *)

let MOI_FSC_CM2_CMWB = prove
 (`!c:(real^N->bool)->bool.
     combinatorial_manifold 2 c ==> combinatorial_manifold_with_boundary 2 c`,
  SIMP_TAC[combinatorial_manifold; combinatorial_manifold_with_boundary]);;

let MOI_FSC_CM2_BOUNDARY = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 2 c ==> surface_boundary c = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[surface_boundary; EMPTY_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSA_CM_EDGE2) THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(1 = 2:num)`]);;

let MOI_FSC_BICOLLAR = prove
 (`!c:(real^N->bool)->bool l.
     FINITE c /\ combinatorial_manifold 2 c /\ orientable_surface_complex c /\
     FINITE l /\ combinatorial_manifold 1 l /\ UNIONS l SUBSET UNIONS c
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           moi_s26_bicollar (UNIONS l) w p q /\ w SUBSET UNIONS c /\
           UNIONS l SUBSET (subtopology euclidean (UNIONS c)) interior_of w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `UNIONS c:real^N->bool`] CURVE_BICOLLAR_ORIENTABLE) THEN
  ASM_SIMP_TAC[MOI_FSC_CM2_CMWB; MOI_FSC_CM2_BOUNDARY; DIFF_EMPTY; OPEN_IN_REFL] THEN
  REWRITE_TAC[moi_s26_bicollar] THEN MESON_TAC[]);;

(* STRIP_REMOVE with its input SURF_INVARIANT discharged (SURF_CHARTS and    *)
(* SURF_LOCAL of pc_moi_s28_tria and pc_moi_s28_trib).                       *)

let MOI_FSC_STRIP_REMOVE =
  MP STRIP_REMOVE (MP (INST_TYPE [`:N`,`:M`] SURF_INVARIANT)
                      (CONJ (INST_TYPE [`:N`,`:M`] SURF_CHARTS) SURF_LOCAL));;

(* Facts on the levels of a bicollar.                                        *)

let MOI_FSC_LEVEL_FACTS = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q t.
     moi_s26_bicollar m w p q /\ compact m /\ connected m /\ ~(m = {}) /\
     --(&1) <= t /\ t <= &1
     ==> compact (moi_s26_level m p t) /\ connected (moi_s26_level m p t) /\
         ~(moi_s26_level m p t = {}) /\ moi_s26_level m p t SUBSET w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; moi_s26_level] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(m:real^N->bool) PCROSS {lift t} SUBSET m PCROSS interval[--vec 1,vec 1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SING_SUBSET] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_SING] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONNECTED_PCROSS; CONNECTED_SING] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; PCROSS_EQ_EMPTY; NOT_INSERT_EMPTY];
    ASM SET_TAC[]]);;

(* The rest of the surface is a retract of the complement of the polygon.   *)
(* Coordinates (x,t) of the bicollar: the polygon is t = 0, the open strip  *)
(* is |t| < 1/2; the retraction pushes 0 < |t| < 1/2 to the level of sign t *)
(* and fixes the rest E; it is continuous on the three closed pieces E,     *)
(* Ap (0 < t <= 1/2) and Am (-1/2 <= t < 0).                                *)

let MOI_FSC_BICOLLAR_COORDS = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q.
     moi_s26_bicollar m w p q
     ==> (!y. y IN w <=> ?x t. x IN m /\ --(&1) <= drop t /\ drop t <= &1 /\
                               y = p(pastecart x t)) /\
         (!x t. x IN m /\ --(&1) <= drop t /\ drop t <= &1
                ==> q(p(pastecart x t)) = pastecart x t) /\
         (!x t x' t'. x IN m /\ --(&1) <= drop t /\ drop t <= &1 /\
                      x' IN m /\ --(&1) <= drop t' /\ drop t' <= &1 /\
                      p(pastecart x t) = p(pastecart x' t')
                      ==> x = x' /\ t = t') /\
         (!x. x IN m ==> p(pastecart x (vec 0)) = x) /\
         (!y. y IN w ==> q y IN m PCROSS interval[--vec 1,vec 1] /\ p(q y) = y) /\
         p continuous_on (m PCROSS interval[--vec 1,vec 1]) /\ q continuous_on w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!x t. x IN m /\ --(&1) <= drop t /\ drop t <= &1
          ==> (q:real^N->real^(N,1)finite_sum)(p(pastecart x t)) = pastecart x t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "w" THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                DROP_NEG; DROP_VEC] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `pastecart (x:real^N) (t:real^1) = pastecart x' t'` MP_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[PASTECART_INJ]];
    ASM SET_TAC[]]);;

(* The cut along the polygon: a holed disk with one hole.                    *)

let MOI_FSC_CUT_CHART = prove
 (`!c:(real^N->bool)->bool l w (p:real^(N,1)finite_sum->real^N) q.
     FINITE c /\ combinatorial_manifold 2 c /\ complex_euler c = &0 /\
     FINITE l /\ combinatorial_manifold 1 l /\ connected (UNIONS l) /\
     ~(UNIONS l = {}) /\ connected (UNIONS c DIFF UNIONS l) /\
     moi_s26_bicollar (UNIONS l) w p q /\ w SUBSET UNIONS c /\
     UNIONS l SUBSET (subtopology euclidean (UNIONS c)) interior_of w
     ==> ?(f:real^2->real^N) g.
           pl_homeomorphism
             (holed_disk_model 1,
              UNIONS c DIFF moi_s26_strip (UNIONS l) p (--(&1 / &2)) (&1 / &2)) (f,g) /\
           IMAGE f (frontier (holed_disk_model 1)) =
           moi_s26_level (UNIONS l) p (--(&1 / &2)) UNION
           moi_s26_level (UNIONS l) p (&1 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`;
                 `--(&1 / &2)`; `&1 / &2`] MOI_FSC_STRIP_REMOVE) THEN
  ASM_SIMP_TAC[MOI_FSC_CM2_CMWB; MOI_FSC_CM2_BOUNDARY; DIFF_EMPTY; UNION_EMPTY] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact (UNIONS l:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `combinatorial_manifold 1 (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold; lf_simplicial_complex] THEN
    MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS e:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 2 (e:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
    MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS l:real^N->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`]
    MOI_FSC_LEVEL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `--(&1 / &2)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 / &2`) THEN
  REWRITE_TAC[REAL_ARITH `--(&1) <= --(&1 / &2) /\ --(&1 / &2) <= &1`;
              REAL_ARITH `--(&1) <= &1 / &2 /\ &1 / &2 <= &1`] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Lm = moi_s26_level (UNIONS l) (p:real^(N,1)finite_sum->real^N) (--(&1 / &2))` THEN
  ABBREV_TAC `Lp = moi_s26_level (UNIONS l) (p:real^(N,1)finite_sum->real^N) (&1 / &2)` THEN
  SUBGOAL_THEN `DISJOINT (Lm:real^N->bool) Lp` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Lm"; "Lp"] THEN REWRITE_TAC[moi_s26_level] THEN
    MP_TAC(ISPECL [`UNIONS l:real^N->bool`; `w:real^N->bool`;
                   `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`;
                   `{lift(--(&1 / &2))}`; `{lift(&1 / &2)}`] MOI_S8CU_BICOLLAR_SETS) THEN
    ASM_REWRITE_TAC[SING_SUBSET; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[DISJOINT] THEN
    SUBGOAL_THEN `{lift(--(&1 / &2))} INTER {lift(&1 / &2)} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY] THEN
      GEN_TAC THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN REAL_ARITH_TAC;
      REWRITE_TAC[PCROSS_EMPTY; IMAGE_CLAUSES]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `e:(real^N->bool)->bool` SURFACE_EULER_PLANAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSC_CUT_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`w:real^N->bool`; `q:real^N->real^(N,1)finite_sum`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `UNIONS e = UNIONS c DIFF
                   moi_s26_strip (UNIONS l) (p:real^(N,1)finite_sum->real^N)
                                 (--(&1 / &2)) (&1 / &2)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      SUBGOAL_THEN `(Lp:real^N->bool) SUBSET UNIONS e` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `surface_boundary (e:(real^N->bool)->bool)` THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[surface_boundary] THEN SET_TAC[];
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `1:num` o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `components (Lm UNION Lp:real^N->bool) = {Lm,Lp}` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPONENTS_UNIQUE_2 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONNECTED_CLOSED] THEN
    MAP_EVERY EXISTS_TAC [`Lm:real^N->bool`; `Lp:real^N->bool`] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `~(Lm:real^N->bool = Lp)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `UNIONS e = UNIONS c DIFF
               moi_s26_strip (UNIONS l) (p:real^(N,1)finite_sum->real^N)
                             (--(&1 / &2)) (&1 / &2)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* The torus assembly MOI_FSC_TORUS_GLUE.  The surface |c| is              *)
(* E UNION S with E = |c| minus the open strip -1/2 < t < 1/2 of the        *)
(* bicollar p of the circle m and S = p(m x [-1/2,1/2]).  With              *)
(* Z = Bd std_triangle = A1 UNION A2, A1 = [0,e1], A2 = [e1,e2] UNION        *)
(* [e2,0], the affine maps alpha1: A1 -> [1,2] and alpha2: A2 -> [-1/2,1/2]  *)
(* give PL homeomorphisms Z x A1 -> E (through G) and Z x A2 -> S (through   *)
(* sigma and p) that agree on Z x {0,e1}; their union Z x Z -> |c| composed *)
(* with sq x sq -> Z x Z is the claim.                                       *)
(* ========================================================================= *)

(* The two arcs of the boundary of the standard triangle. *)

let MOI_FSC_TG_Z = prove
 (`relative_frontier std_triangle =
     segment[vec 0:real^2,basis 1] UNION (segment[basis 1,basis 2] UNION segment[basis 2,vec 0]) /\
   segment[vec 0:real^2,basis 1] INTER (segment[basis 1,basis 2] UNION segment[basis 2,vec 0]) =
     {vec 0, basis 1} /\
   pl_polyhedron (relative_frontier std_triangle) /\
   pl_polyhedron (segment[vec 0:real^2,basis 1]) /\
   pl_polyhedron (segment[basis 1:real^2,basis 2] UNION segment[basis 2,vec 0]) /\
   compact (relative_frontier std_triangle) /\
   compact (segment[vec 0:real^2,basis 1]) /\
   compact (segment[basis 1:real^2,basis 2] UNION segment[basis 2,vec 0]) /\
   pl_sphere 1 (relative_frontier std_triangle)`,
  SUBGOAL_THEN `~collinear {vec 0:real^2, basis 1, basis 2}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SS2_STD_NONCOLLINEAR THEN REWRITE_TAC[DIMINDEX_2; LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (relative_frontier std_triangle) /\
                pl_sphere 1 (relative_frontier std_triangle)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
      REWRITE_TAC[std_triangle] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      MATCH_MP_TAC(REWRITE_RULE[ARITH] (SPEC `1` PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX)) THEN
      REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier std_triangle =
     segment[vec 0:real^2,basis 1] UNION (segment[basis 1,basis 2] UNION segment[basis 2,vec 0])`
  ASSUME_TAC THENL
   [REWRITE_TAC[std_triangle] THEN MATCH_MP_TAC RELATIVE_FRONTIER_OF_TRIANGLE THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (segment[vec 0:real^2,basis 1]) /\
                pl_polyhedron (segment[basis 1:real^2,basis 2] UNION segment[basis 2,vec 0])`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC PL_POLYHEDRON_UNION THEN CONJ_TAC] THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[vec 0:real^2,basis 1] INTER (segment[basis 1,basis 2] UNION segment[basis 2,vec 0]) =
     {vec 0, basis 1}`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNION_OVER_INTER] THEN
    SUBGOAL_THEN `segment[vec 0:real^2,basis 1] INTER segment[basis 1,basis 2] = {basis 1} /\
                  segment[vec 0:real^2,basis 1] INTER segment[basis 2,vec 0] = {vec 0}`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC INTER_SEGMENT THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[INTER_COMM] THEN
        MATCH_MP_TAC INTER_SEGMENT THEN DISJ2_TAC THEN
        UNDISCH_TAC `~collinear {vec 0:real^2, basis 1, basis 2}` THEN
        REWRITE_TAC[INSERT_AC]];
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPACT_UNION; COMPACT_SEGMENT]);;

(* The affine parametrisations of the two arcs. *)

let MOI_FSC_TG_ALPHA1 = prove
 (`?g. pl_homeomorphism (segment[vec 0:real^2,basis 1],interval[lift(&1),lift(&2)])
                          ((\y:real^2. lift(y$1) + lift(&1)),g)`,
  MP_TAC(ISPECL [`segment[vec 0:real^2,basis 1]`; `\y:real^2. lift(y$1) + lift(&1)`]
    MOI_FCL_PLH_COMPACT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_SEGMENT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_AFFINE THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_SEGMENT];
      MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN
      REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ] THEN STRIP_TAC THEN
      MP_TAC(SPEC `a:real^2` (CONJUNCT1 MOI_LSP_STD_EDGES)) THEN
      MP_TAC(SPEC `b:real^2` (CONJUNCT1 MOI_LSP_STD_EDGES)) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
      UNDISCH_TAC `(a:real^2)$1 + &1 = (b:real^2)$1 + &1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\y:real^2. lift(y$1) + lift(&1)) (segment[vec 0,basis 1]) =
                interval[lift(&1),lift(&2)]` (fun th -> REWRITE_TAC[th]) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^1` THEN
  REWRITE_TAC[IN_IMAGE; IN_INTERVAL_1; LIFT_DROP] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN
    MP_TAC(SPEC `y:real^2` (CONJUNCT1 MOI_LSP_STD_EDGES)) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `(drop t - &1) % basis 1:real^2` THEN CONJ_TAC THENL
     [SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
      REWRITE_TAC[GSYM LIFT_ADD; REAL_ARITH `(x - &1) + &1 = x`; LIFT_DROP];
      REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `drop t - &1` THEN
      REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]]]);;

let MOI_FSC_TG_ALPHA2 = prove
 (`?g. pl_homeomorphism (segment[basis 1:real^2,basis 2] UNION segment[basis 2,vec 0],
                         interval[lift(--(&1 / &2)),lift(&1 / &2)])
                        ((\y:real^2. (lift(y$1) + inv(&2) % lift(y$2)) + lift(--inv(&2))),g)`,
  ABBREV_TAC `f = \y:real^2. (lift(y$1) + inv(&2) % lift(y$2)) + lift(--inv(&2))` THEN
  SUBGOAL_THEN `!y:real^2. drop(f y) = y$1 + inv(&2) * y$2 - inv(&2)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[basis 1:real^2,basis 2] UNION segment[basis 2,vec 0]`;
                 `f:real^2->real^1`] MOI_FCL_PLH_COMPACT) THEN
  ANTS_TAC THENL
   [SIMP_TAC[COMPACT_UNION; COMPACT_SEGMENT] THEN CONJ_TAC THENL
     [EXPAND_TAC "f" THEN MATCH_MP_TAC PL_MAP_ON_AFFINE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
        MATCH_MP_TAC PL_POLYHEDRON_UNION THEN CONJ_TAC THEN
        MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_SEGMENT];
        MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT] THEN
        MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT]];
      MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN
      ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REWRITE_TAC[IN_UNION] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
        MATCH_MP (CONJUNCT1(CONJUNCT2 MOI_LSP_STD_EDGES)))) THEN
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
        MATCH_MP (CONJUNCT2(CONJUNCT2 MOI_LSP_STD_EDGES)))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^1)
                  (segment[basis 1,basis 2] UNION segment[basis 2,vec 0]) =
                interval[lift(--(&1 / &2)),lift(&1 / &2)]` (fun th -> REWRITE_TAC[th]) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^1` THEN
  REWRITE_TAC[IN_IMAGE; IN_INTERVAL_1; LIFT_DROP; IN_UNION] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC) THENL
     [MP_TAC(SPEC `y:real^2` (CONJUNCT1(CONJUNCT2 MOI_LSP_STD_EDGES)));
      MP_TAC(SPEC `y:real^2` (CONJUNCT2(CONJUNCT2 MOI_LSP_STD_EDGES)))] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    STRIP_TAC THEN ASM_CASES_TAC `&0 <= drop t` THENL
     [EXISTS_TAC `(&2 * drop t) % basis 1 + (&1 - &2 * drop t) % basis 2:real^2` THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2;
                 ARITH] THEN REAL_ARITH_TAC;
        DISJ1_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `&1 - &2 * drop t` THEN
        REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]];
      EXISTS_TAC `(&2 * drop t + &1) % basis 2:real^2` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
        REAL_ARITH_TAC;
        DISJ2_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `--(&2 * drop t)` THEN
        REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]]]]);;

(* The two halves: Z x A1 onto E through G, Z x A2 onto the closed strip    *)
(* through sigma and p.                                                      *)

let MOI_FSC_TG_PHIE = prove
 (`!(G:real^(2,1)finite_sum->real^N) G' E.
     pl_homeomorphism
       (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)],E) (G,G')
     ==> ?g. pl_homeomorphism
               (relative_frontier std_triangle PCROSS segment[vec 0:real^2,basis 1],E)
               ((\z. G(pastecart (fstcart z) (lift(sndcart z$1) + lift(&1)))),g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC MOI_FSC_TG_Z THEN
  X_CHOOSE_TAC `b1:real^1->real^2` MOI_FSC_TG_ALPHA1 THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier std_triangle,relative_frontier std_triangle)
                     ((\x:real^2. x),(\x:real^2. x))`
  ASSUME_TAC THENL
   [SIMP_TAC[pl_homeomorphism; HOMEOMORPHISM_ID; GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier std_triangle`; `relative_frontier std_triangle`;
                 `segment[vec 0:real^2,basis 1]`; `interval[lift(&1),lift(&2)]`;
                 `\x:real^2. x`; `\x:real^2. x`; `\y:real^2. lift(y$1) + lift(&1)`;
                 `b1:real^1->real^2`] MOI_S8PL_PLH_PCROSS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP PL_HOMEOMORPHISM_COMPOSE
    (CONJ th (ASSUME `pl_homeomorphism
       (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)],E)
       (G:real^(2,1)finite_sum->real^N,G')`)))) THEN
  DISCH_TAC THEN EXISTS_TAC
   `(\z:real^(2,1)finite_sum. pastecart ((\x:real^2. x)(fstcart z))
                                        ((b1:real^1->real^2)(sndcart z))) o
    (G':real^N->real^(2,1)finite_sum)` THEN
  SUBGOAL_THEN
   `(\z:real^(2,2)finite_sum. (G:real^(2,1)finite_sum->real^N)
        (pastecart (fstcart z) (lift(sndcart z$1) + lift(&1)))) =
    G o (\z. pastecart ((\x:real^2. x)(fstcart z))
                       ((\y:real^2. lift(y$1) + lift(&1))(sndcart z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; FIRST_ASSUM ACCEPT_TAC]);;

let MOI_FSC_TG_PHIS = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q (sigma:real^2->real^N) sigma'.
     moi_s26_bicollar m w p q /\ pl_polyhedron m /\
     pl_homeomorphism (relative_frontier std_triangle,m) (sigma,sigma')
     ==> ?g. pl_homeomorphism
               (relative_frontier std_triangle PCROSS
                (segment[basis 1:real^2,basis 2] UNION segment[basis 2,vec 0]),
                IMAGE p (m PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)]))
               ((\z. p(pastecart (sigma(fstcart z))
                         ((lift(sndcart z$1) + inv(&2) % lift(sndcart z$2)) +
                          lift(--inv(&2))))),g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC MOI_FSC_TG_Z THEN
  X_CHOOSE_TAC `b2:real^1->real^2` MOI_FSC_TG_ALPHA2 THEN
  MP_TAC(ISPECL [`relative_frontier std_triangle`; `m:real^N->bool`;
                 `segment[basis 1:real^2,basis 2] UNION segment[basis 2,vec 0]`;
                 `interval[lift(--(&1 / &2)),lift(&1 / &2)]`;
                 `sigma:real^2->real^N`; `sigma':real^N->real^2`;
                 `\y:real^2. (lift(y$1) + inv(&2) % lift(y$2)) + lift(--inv(&2))`;
                 `b2:real^1->real^2`] MOI_S8PL_PLH_PCROSS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s26_bicollar]) THEN
  MP_TAC(ISPECL [`(m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`;
                 `(m:real^N->bool) PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)]`]
    MOI_FPS_PLH_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET_INTERVAL_1] THEN
      REWRITE_TAC[LIFT_DROP; DROP_NEG; DROP_VEC] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_INTERVAL]];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP PL_HOMEOMORPHISM_COMPOSE (CONJ
    (ASSUME `pl_homeomorphism
       (relative_frontier std_triangle PCROSS
        (segment[basis 1:real^2,basis 2] UNION segment[basis 2,vec 0]),
        m PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)])
       ((\z. pastecart ((sigma:real^2->real^N)(fstcart z))
              ((\y:real^2. (lift(y$1) + inv(&2) % lift(y$2)) + lift(--inv(&2)))(sndcart z))),
        (\z. pastecart ((sigma':real^N->real^2)(fstcart z)) ((b2:real^1->real^2)(sndcart z))))`)
    th))) THEN
  DISCH_TAC THEN EXISTS_TAC
   `(\z:real^(N,1)finite_sum. pastecart ((sigma':real^N->real^2)(fstcart z))
                                      ((b2:real^1->real^2)(sndcart z))) o
    (q:real^N->real^(N,1)finite_sum)` THEN
  SUBGOAL_THEN
   `(\z:real^(2,2)finite_sum. (p:real^(N,1)finite_sum->real^N)
        (pastecart ((sigma:real^2->real^N)(fstcart z))
           ((lift(sndcart z$1) + inv(&2) % lift(sndcart z$2)) + lift(--inv(&2))))) =
    p o (\z. pastecart (sigma(fstcart z))
               ((\y:real^2. (lift(y$1) + inv(&2) % lift(y$2)) + lift(--inv(&2)))(sndcart z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; FIRST_ASSUM ACCEPT_TAC]);;

(* The assembly. *)

let MOI_FSC_TORUS_GLUE = prove
 (`!c:(real^N->bool)->bool m w (p:real^(N,1)finite_sum->real^N) q sigma sigma' G G'.
     FINITE c /\ combinatorial_manifold 2 c /\
     moi_s26_bicollar m w p q /\ w SUBSET UNIONS c /\ pl_polyhedron m /\
     pl_homeomorphism (relative_frontier std_triangle,m) (sigma,sigma') /\
     pl_homeomorphism
       (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)],
        UNIONS c DIFF moi_s26_strip m p (--(&1 / &2)) (&1 / &2)) (G,G') /\
     (!x. x IN relative_frontier std_triangle
          ==> G(pastecart x (lift(&1))) = p(pastecart (sigma x) (lift(--(&1 / &2))))) /\
     (!x. x IN relative_frontier std_triangle
          ==> G(pastecart x (lift(&2))) = p(pastecart (sigma x) (lift(&1 / &2))))
     ==> ?(f:real^(2,2)finite_sum->real^N) g.
           pl_homeomorphism (pl_torus_model,UNIONS c) (f,g)`,

  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Z = relative_frontier std_triangle` THEN
  ABBREV_TAC `E = UNIONS c DIFF
                  moi_s26_strip m (p:real^(N,1)finite_sum->real^N) (--(&1 / &2)) (&1 / &2)` THEN
  ABBREV_TAC `S = IMAGE (p:real^(N,1)finite_sum->real^N)
                        (m PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)])` THEN
  MP_TAC MOI_FSC_TG_Z THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:real^(2,1)finite_sum->real^N`; `G':real^N->real^(2,1)finite_sum`;
                 `E:real^N->bool`] MOI_FSC_TG_PHIE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `gE:real^N->real^(2,2)finite_sum`) THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`; `sigma:real^2->real^N`;
                 `sigma':real^N->real^2`] MOI_FSC_TG_PHIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `gS:real^N->real^(2,2)finite_sum`) THEN
  (* sigma maps Z onto m *)
  SUBGOAL_THEN
   `(!x:real^2. x IN Z ==> (sigma:real^2->real^N) x IN m) /\
    (!u:real^N. u IN m ==> (sigma':real^N->real^2) u IN Z /\ sigma(sigma' u) = u)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (Z:real^2->bool,m:real^N->bool)
                                   (sigma:real^2->real^N,sigma')` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the strip, E and S *)
  SUBGOAL_THEN
   `E INTER S = IMAGE (p:real^(N,1)finite_sum->real^N)
                      (m PCROSS {lift(--(&1 / &2)), lift(&1 / &2)}) /\
    E UNION S = UNIONS c`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E"; "S"] THEN REWRITE_TAC[moi_s26_strip] THEN
    MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`;
                   `interval[lift(--(&1 / &2)),lift(&1 / &2)]`;
                   `{x:real^1 | --(&1 / &2) < drop x /\ drop x < &1 / &2}`]
      MOI_S8CU_BICOLLAR_SETS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `interval[lift(--(&1 / &2)),lift(&1 / &2)] DIFF
      {x:real^1 | --(&1 / &2) < drop x /\ drop x < &1 / &2} =
      {lift(--(&1 / &2)), lift(&1 / &2)} /\
      {x:real^1 | --(&1 / &2) < drop x /\ drop x < &1 / &2} SUBSET
      interval[lift(--(&1 / &2)),lift(&1 / &2)]`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^1` THEN
        REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY; LIFT_DROP] THEN
        REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC))) THEN
    SUBGOAL_THEN
     `IMAGE (p:real^(N,1)finite_sum->real^N)
        (m PCROSS {x:real^1 | --(&1 / &2) < drop x /\ drop x < &1 / &2}) SUBSET
      IMAGE p (m PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)])`
    ASSUME_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC PCROSS_MONO THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`(w:real^N->bool) SUBSET UNIONS c`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  (* closedness *)
  SUBGOAL_THEN
   `closed ((Z:real^2->bool) PCROSS segment[vec 0:real^2,basis 1]) /\
    closed ((Z:real^2->bool) PCROSS (segment[basis 1:real^2,basis 2] UNION segment[basis 2,vec 0])) /\
    closed (E:real^N->bool) /\ closed (S:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `((Z:real^2->bool) PCROSS interval[lift(&1),lift(&2)]) homeomorphic (E:real^N->bool)`
      MP_TAC THENL
       [REWRITE_TAC[homeomorphic] THEN
        MAP_EVERY EXISTS_TAC [`G:real^(2,1)finite_sum->real^N`;
                              `G':real^N->real^(2,1)finite_sum`] THEN
        ASM_MESON_TAC[pl_homeomorphism];
        DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
        MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[COMPACT_INTERVAL]];
      SUBGOAL_THEN `((Z:real^2->bool) PCROSS (segment[basis 1:real^2,basis 2] UNION segment[basis 2,vec 0]))
                    homeomorphic (S:real^N->bool)`
      MP_TAC THENL
       [REWRITE_TAC[homeomorphic] THEN
        MAP_EVERY EXISTS_TAC
         [`\z:real^(2,2)finite_sum. (p:real^(N,1)finite_sum->real^N)(pastecart ((sigma:real^2->real^N)(fstcart z))
                 ((lift(sndcart z$1) + inv(&2) % lift(sndcart z$2)) + lift(--inv(&2))))`;
          `gS:real^N->real^(2,2)finite_sum`] THEN
        ASM_MESON_TAC[pl_homeomorphism];
        DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
        MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the values of the two parametrisations at the two ends *)
  SUBGOAL_THEN
   `lift((vec 0:real^2)$1) + lift(&1) = lift(&1) /\
    lift((basis 1:real^2)$1) + lift(&1) = lift(&2) /\
    (lift((vec 0:real^2)$1) + inv(&2) % lift((vec 0:real^2)$2)) + lift(--inv(&2)) =
    lift(--(&1 / &2)) /\
    (lift((basis 1:real^2)$1) + inv(&2) % lift((basis 1:real^2)$2)) + lift(--inv(&2)) =
    lift(&1 / &2)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* agreement on Z x {0,e1} *)
  SUBGOAL_THEN
   `!z. z IN ((Z:real^2->bool) PCROSS segment[vec 0:real^2,basis 1]) INTER
             ((Z:real^2->bool) PCROSS (segment[basis 1,basis 2] UNION segment[basis 2,vec 0]))
        ==> (G:real^(2,1)finite_sum->real^N)
              (pastecart (fstcart z) (lift(sndcart z$1) + lift(&1))) =
            (p:real^(N,1)finite_sum->real^N)
              (pastecart ((sigma:real^2->real^N)(fstcart z))
                 ((lift(sndcart z$1) + inv(&2) % lift(sndcart z$2)) + lift(--inv(&2))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTER_PCROSS; INTER_IDEMPOT] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INSERT; NOT_IN_EMPTY;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST1_TAC)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the image of Z x {0,e1} *)
  SUBGOAL_THEN
   `IMAGE (\z. (G:real^(2,1)finite_sum->real^N)
                 (pastecart (fstcart z) (lift(sndcart z$1) + lift(&1))))
      (((Z:real^2->bool) PCROSS segment[vec 0:real^2,basis 1]) INTER
       ((Z:real^2->bool) PCROSS (segment[basis 1,basis 2] UNION segment[basis 2,vec 0]))) = E INTER S`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INTER_PCROSS; INTER_IDEMPOT] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_INSERT;
                NOT_IN_EMPTY; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    X_GEN_TAC `v:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `y:real^2`
        (CONJUNCTS_THEN2 SUBST1_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST1_TAC))))) THEN
      ASM_SIMP_TAC[] THEN EXISTS_TAC `(sigma:real^2->real^N) x` THENL
       [EXISTS_TAC `lift(--(&1 / &2))`; EXISTS_TAC `lift(&1 / &2)`] THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `s:real^1`
        (CONJUNCTS_THEN2 SUBST1_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST1_TAC))))) THEN
      EXISTS_TAC `(sigma':real^N->real^2) u` THENL
       [EXISTS_TAC `vec 0:real^2`; EXISTS_TAC `basis 1:real^2`] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the union over Z x Z *)
  MP_TAC(ISPECL
   [`(Z:real^2->bool) PCROSS segment[vec 0:real^2,basis 1]`;
    `(Z:real^2->bool) PCROSS (segment[basis 1:real^2,basis 2] UNION segment[basis 2,vec 0])`;
    `E:real^N->bool`; `S:real^N->bool`;
    `\z:real^(2,2)finite_sum. (G:real^(2,1)finite_sum->real^N)
           (pastecart (fstcart z) (lift(sndcart z$1) + lift(&1)))`;
    `gE:real^N->real^(2,2)finite_sum`;
    `\z:real^(2,2)finite_sum. (p:real^(N,1)finite_sum->real^N)
           (pastecart ((sigma:real^2->real^N)(fstcart z))
              ((lift(sndcart z$1) + inv(&2) % lift(sndcart z$2)) + lift(--inv(&2))))`;
    `gS:real^N->real^(2,2)finite_sum`] MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM PCROSS_UNION] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "U") THEN
  (* the square onto Z, and the product *)
  MP_TAC(ISPECL [`moi_fps_sq`; `Z:real^2->bool`] MOI_S8PL_SPHERE1_PLH) THEN
  ASM_REWRITE_TAC[MOI_FPS_SQ_PL_SPHERE] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_TAC `h':real^2->real^2`)) THEN
  MP_TAC(ISPECL [`moi_fps_sq`; `Z:real^2->bool`; `moi_fps_sq`; `Z:real^2->bool`;
                 `h:real^2->real^2`; `h':real^2->real^2`; `h:real^2->real^2`;
                 `h':real^2->real^2`] MOI_S8PL_PLH_PCROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_fps_sq] THEN
    MATCH_MP_TAC MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER THEN REWRITE_TAC[POLYTOPE_INTERVAL];
    DISCH_THEN(LABEL_TAC "H")] THEN
  REWRITE_TAC[pl_torus_model; GSYM moi_fps_sq] THEN
  USE_THEN "H" (fun th1 -> USE_THEN "U" (fun th2 ->
    MP_TAC(MATCH_MP PL_HOMEOMORPHISM_COMPOSE (CONJ th1 th2)))) THEN
  MESON_TAC[]);;

(* ========================================================================= *)
(* MOI_FSC_ENDS: a product structure G on the cut annulus E matching the     *)
(* strip of the bicollar at both ends. The model Z x [1,2] (Z =              *)
(* relative_frontier std_triangle) is a holed disk with one hole             *)
(* (MOI_FSC_EN_MODEL_CHART); HOLED_EXT gives a PLH G0 from it onto E that    *)
(* agrees with the strip at level -1/2 on Z x {1} and carries Z x {2} onto   *)
(* the level 1/2 (MOI_FSC_EN_G0). The two parametrisations of the level 1/2  *)
(* differ by a PL self-homeomorphism of Z, which preserves or reverses the   *)
(* cyclic order (MOI_S3CI_DICHOT); MOI_S3CI_COLLAR_DEF, composed with the    *)
(* reflection rho in the reversing case, gives a PL self-homeomorphism g of  *)
(* E fixing the level -1/2 (MOI_FSC_EN_ADJUST), and G = g o G0. The MOI_S3CI *)
(* lemmas are those of pc_moi_s33_circ.ml.                                   *)
(* ========================================================================= *)

let MOI_FSC_EN_PLH_EQ = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g f' g'.
     pl_homeomorphism (s,t) (f,g) /\
     (!x. x IN s ==> f' x = f x) /\ (!y. y IN t ==> g' y = g y)
     ==> pl_homeomorphism (s,t) (f',g')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_EQ THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `f:real^M->real^N` THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `g:real^N->real^M` THEN
    ASM_MESON_TAC[]]);;

let MOI_FSC_EN_Z_BASIC = prove
 (`compact (relative_frontier std_triangle) /\
   pl_polyhedron (relative_frontier std_triangle) /\
   locally_polyhedral (relative_frontier std_triangle) /\
   pl_sphere 1 (relative_frontier std_triangle) /\
   connected (relative_frontier std_triangle) /\
   ~(relative_frontier std_triangle = {})`,
  SUBGOAL_THEN `pl_polyhedron (relative_frontier std_triangle)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LTD_STD_TRIANGLE_FRONTIER; pl_polyhedron] THEN
    EXISTS_TAC `{segment[vec 0:real^2,basis 1], segment[basis 1,basis 2],
                 segment[basis 2,vec 0]}` THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                UNIONS_INSERT; UNIONS_0; UNION_EMPTY] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SIMP_TAC[POLYTOPE_CONVEX_HULL; FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `locally_polyhedral (relative_frontier std_triangle)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE] THEN CONJ_TAC THENL
   [REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
    MAP_EVERY EXISTS_TAC [`std_triangle`; `\x:real^2. x`; `\x:real^2. x`] THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX] THEN MATCH_MP_TAC MOI_FGB_PLH_ID THEN
    ASM_REWRITE_TAC[];
    MESON_TAC[PATH_CONNECTED_IMP_CONNECTED; MOI_LTD_FRONTIER_SUBSET_TRIANGLE]]);;

(* The model holed disk Z x [1,2] with its two boundary circles.            *)

let MOI_FSC_EN_MODEL_CHART = prove
 (`?h h'. pl_homeomorphism
            (holed_disk_model 1,
             relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]) (h,h') /\
          IMAGE h (frontier (holed_disk_model 1)) =
          relative_frontier std_triangle PCROSS {lift(&1)} UNION
          relative_frontier std_triangle PCROSS {lift(&2)}`,
  X_CHOOSE_THEN `gh:real^2->real^2` STRIP_ASSUME_TAC MOI_S8PL_HD1_FRONTIER THEN
  X_CHOOSE_TAC `psi':real^(2,1)finite_sum->real^2` MOI_FPS_PSI_PLH THEN
  MP_TAC(ISPECL [`moi_fps_sq`; `relative_frontier std_triangle`] MOI_S8PL_SPHERE1_PLH) THEN
  REWRITE_TAC[MOI_FPS_SQ_PL_SPHERE; MOI_FSC_EN_Z_BASIC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2->real^2` (X_CHOOSE_TAC `z':real^2->real^2`)) THEN
  ABBREV_TAC `zi = \u:real^(2,1)finite_sum. pastecart ((z:real^2->real^2)(fstcart u))
                                                     ((\t:real^1. t)(sndcart u))` THEN
  ABBREV_TAC `zi' = \u:real^(2,1)finite_sum. pastecart ((z':real^2->real^2)(fstcart u))
                                                      ((\t:real^1. t)(sndcart u))` THEN
  SUBGOAL_THEN
   `pl_homeomorphism (moi_fps_sq PCROSS interval[lift(&1),lift(&2)],
                      relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)])
                     (zi,zi')`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["zi"; "zi'"] THEN MATCH_MP_TAC MOI_S8PL_PLH_PCROSS THEN
    ASM_REWRITE_TAC[MOI_FPS_SQ_PL_POLYHEDRON] THEN
    SIMP_TAC[POLYTOPE_INTERVAL; POLYTOPE_IMP_PL_POLYHEDRON] THEN
    MATCH_MP_TAC MOI_FGB_PLH_ID THEN
    SIMP_TAC[POLYTOPE_INTERVAL; POLYTOPE_IMP_PL_POLYHEDRON;
             LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  EXISTS_TAC `(zi:real^(2,1)finite_sum->real^(2,1)finite_sum) o
              (moi_fps_psi o moi_feu_hd1_map)` THEN
  EXISTS_TAC `((gh:real^2->real^2) o (psi':real^(2,1)finite_sum->real^2)) o
              (zi':real^(2,1)finite_sum->real^(2,1)finite_sum)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `moi_fps_sq PCROSS interval[lift(&1),lift(&2)]` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `moi_fps_ann` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMAGE_UNION; MOI_S8PL_RF12] THEN
  SIMP_TAC[MOI_S8PL_PSI_LEVEL; REAL_LE_REFL; REAL_OF_NUM_LE; ARITH] THEN
  EXPAND_TAC "zi" THEN REWRITE_TAC[MOI_S8PL_IMAGE_PCROSS_MAP; IMAGE_ID] THEN
  SUBGOAL_THEN `IMAGE (z:real^2->real^2) moi_fps_sq = relative_frontier std_triangle`
    (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `pl_homeomorphism (moi_fps_sq,relative_frontier std_triangle)
                                (z:real^2->real^2,z')` THEN
  SIMP_TAC[pl_homeomorphism; homeomorphism]);;

(* Slices and the parametrisations of the levels of a bicollar.              *)

let MOI_FSC_EN_SLICE_PLH = prove
 (`!(s:real^M->bool) (b:real^N).
     locally_polyhedral s
     ==> pl_homeomorphism (s,s PCROSS {b}) ((\x. pastecart x b),fstcart)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism; FSTCART_PASTECART] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; PCROSS; IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
      MP_TAC(ISPECL [`\x:real^M. x`; `\x:real^M. (b:real^N)`; `s:real^M->bool`]
        CONTINUOUS_ON_PASTECART) THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      REWRITE_TAC[FORALL_IN_PCROSS; IN_SING; FSTCART_PASTECART] THEN SIMP_TAC[];
      REWRITE_TAC[EXTENSION; IN_IMAGE; PCROSS; IN_ELIM_THM; IN_SING] THEN
      MESON_TAC[FSTCART_PASTECART];
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART]];
    MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. x`; `\x:real^M. (b:real^N)`]
      PL_MAP_ON_PASTECART) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PL_MAP_ON_CONST; GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID]]);;

let MOI_FSC_EN_LEVEL_PLH = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q sigma sigma' t.
     moi_s26_bicollar m w p q /\ pl_polyhedron m /\
     pl_homeomorphism (relative_frontier std_triangle,m) (sigma,sigma') /\
     --(&1) <= t /\ t <= &1
     ==> pl_homeomorphism (relative_frontier std_triangle,moi_s26_level m p t)
           ((\x. p(pastecart (sigma x) (lift t))),(\y. sigma'(fstcart(q y))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; moi_s26_level] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `lift t`] MOI_FSC_EN_SLICE_PLH) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism ((m:real^N->bool) PCROSS {lift t},
                      IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS {lift t})) (p,q)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FPS_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`(m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]`;
                          `w:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SING_SUBSET] THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_SING]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier std_triangle`; `m:real^N->bool`;
                 `(m:real^N->bool) PCROSS {lift t}`;
                 `sigma:real^2->real^N`; `sigma':real^N->real^2`;
                 `\x:real^N. pastecart x (lift t)`;
                 `fstcart:real^(N,1)finite_sum->real^N`] PL_HOMEOMORPHISM_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`relative_frontier std_triangle`; `(m:real^N->bool) PCROSS {lift t}`;
                 `IMAGE (p:real^(N,1)finite_sum->real^N) (m PCROSS {lift t})`;
                 `(\x:real^N. pastecart x (lift t)) o (sigma:real^2->real^N)`;
                 `(sigma':real^N->real^2) o (fstcart:real^(N,1)finite_sum->real^N)`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`]
    PL_HOMEOMORPHISM_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF]);;

(* The reflection rho x = vector[x$2; x$1] of Z: a PL involution of Z that  *)
(* reverses the cyclic order (it swaps basis 1 and basis 2, fixes vec 0).   *)

let MOI_FSC_EN_RHO_LINEAR = prove
 (`linear (\x:real^2. vector[x$2; x$1]:real^2)`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT]);;

let MOI_FSC_EN_RHO_Z = prove
 (`(!x:real^2. vector[(vector[x$2; x$1]:real^2)$2; (vector[x$2; x$1]:real^2)$1] = x) /\
   IMAGE (\x:real^2. vector[x$2; x$1]:real^2) (relative_frontier std_triangle) =
   relative_frontier std_triangle /\
   (!x. x IN relative_frontier std_triangle
        ==> vector[x$2; x$1]:real^2 IN relative_frontier std_triangle)`,
  SUBGOAL_THEN `!x:real^2. vector[(vector[x$2; x$1]:real^2)$2; (vector[x$2; x$1]:real^2)$1] = x`
  ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^2. vector[x$2; x$1]:real^2) (relative_frontier std_triangle) =
    relative_frontier std_triangle`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `vector[(vec 0:real^2)$2; (vec 0:real^2)$1]:real^2 = vec 0 /\
                  vector[(basis 1:real^2)$2; (basis 1:real^2)$1]:real^2 = basis 2 /\
                  vector[(basis 2:real^2)$2; (basis 2:real^2)$1]:real^2 = basis 1`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH];
      ALL_TAC] THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_FRONTIER; IMAGE_UNION] THEN
    REWRITE_TAC[GSYM(MATCH_MP CLOSED_SEGMENT_LINEAR_IMAGE MOI_FSC_EN_RHO_LINEAR)] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IMAGE (\x:real^2. vector[x$2; x$1]:real^2) (relative_frontier std_triangle) =
               relative_frontier std_triangle` THEN
  SET_TAC[]);;

let MOI_FSC_EN_RHO_PLH = prove
 (`pl_homeomorphism (relative_frontier std_triangle,relative_frontier std_triangle)
                    ((\x:real^2. vector[x$2; x$1]:real^2),(\x:real^2. vector[x$2; x$1]:real^2))`,
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism; MOI_FSC_EN_RHO_Z] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_FSC_EN_RHO_LINEAR];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^2. (\x:real^2. vector[x$2; x$1]:real^2) x + vec 0` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID];
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
      REWRITE_TAC[MOI_FSC_EN_Z_BASIC; MOI_FSC_EN_RHO_LINEAR]]]);;

let MOI_FSC_EN_RHO_REV = prove
 (`moi_s3ci_cycrev (\x:real^2. vector[x$2; x$1]:real^2)`,
  MP_TAC(ISPEC `\x:real^2. vector[x$2; x$1]:real^2` MOI_S3CI_DICHOT) THEN ANTS_TAC THENL
   [MP_TAC MOI_FSC_EN_RHO_PLH THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
  REWRITE_TAC[moi_s3ci_cycpres] THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^2`; `basis 1:real^2`; `basis 2:real^2`]) THEN
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_FRONTIER; IN_UNION; ENDS_IN_SEGMENT] THEN
  REWRITE_TAC[moi_s3ci_cyc; moi_s3ci_cyc3; moi_lsp_tau; VEC_COMPONENT; VECTOR_2] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* PL circles: images of Z under PL homeomorphisms; the slices of Z x [1,2] *)
(* and the levels of the bicollar.                                          *)

let MOI_FSC_EN_IMAGE_CONN = prove
 (`!(s:real^N->bool) f g.
     pl_homeomorphism (relative_frontier std_triangle,s) (f,g)
     ==> connected s /\ ~(s = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `s:real^N->bool`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_FSC_EN_Z_BASIC];
    REWRITE_TAC[IMAGE_EQ_EMPTY; MOI_FSC_EN_Z_BASIC]]);;

let MOI_FSC_EN_SLICE_SPHERE = prove
 (`!b:real^1.
     pl_sphere 1 (relative_frontier std_triangle PCROSS {b}) /\
     pl_homeomorphism (relative_frontier std_triangle,relative_frontier std_triangle PCROSS {b})
                      ((\x. pastecart x b),fstcart)`,
  GEN_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier std_triangle,
                                  relative_frontier std_triangle PCROSS {b:real^1})
                                 ((\x. pastecart x b),fstcart)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSC_EN_SLICE_PLH THEN REWRITE_TAC[MOI_FSC_EN_Z_BASIC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`1`; `relative_frontier std_triangle`;
                 `relative_frontier std_triangle PCROSS {b:real^1}`;
                 `\x:real^2. pastecart x (b:real^1)`;
                 `fstcart:real^(2,1)finite_sum->real^2`] MOI_CMB_PL_SPHERE_TRANSFER) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[MOI_FSC_EN_Z_BASIC; DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2] THEN
  ARITH_TAC);;

let MOI_FSC_EN_LEVELS = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q sigma sigma'.
     moi_s26_bicollar m w p q /\ pl_polyhedron m /\ pl_sphere 1 m /\
     pl_homeomorphism (relative_frontier std_triangle,m) (sigma,sigma')
     ==> (!t. --(&1) <= t /\ t <= &1
              ==> pl_sphere 1 (moi_s26_level m p t) /\ connected (moi_s26_level m p t) /\
                  ~(moi_s26_level m p t = {})) /\
         DISJOINT (moi_s26_level m p (--(&1 / &2))) (moi_s26_level m p (&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                   `q:real^N->real^(N,1)finite_sum`; `sigma:real^2->real^N`;
                   `sigma':real^N->real^2`; `t:real`] MOI_FSC_EN_LEVEL_PLH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FSC_EN_IMAGE_CONN) THEN SIMP_TAC[] THEN
    DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
    MAP_EVERY EXISTS_TAC
     [`m:real^N->bool`;
      `(\x. (p:real^(N,1)finite_sum->real^N)(pastecart ((sigma:real^2->real^N) x) (lift t))) o
       (sigma':real^N->real^2)`;
      `(sigma:real^2->real^N) o
       (\y. (sigma':real^N->real^2)(fstcart((q:real^N->real^(N,1)finite_sum) y)))`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier std_triangle` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s26_bicollar m w (p:real^(N,1)finite_sum->real^N) q` THEN
  REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s26_level; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x1:real^N` (X_CHOOSE_THEN `t1:real^1` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `x2:real^N` (X_CHOOSE_THEN `t2:real^1` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pastecart (x1:real^N) (t1:real^1) = pastecart x2 t2` MP_TAC THENL
   [SUBGOAL_THEN
     `(q:real^N->real^(N,1)finite_sum) ((p:real^(N,1)finite_sum->real^N)
         (pastecart (x1:real^N) (t1:real^1))) = pastecart x1 t1 /\
      q (p (pastecart (x2:real^N) (t2:real^1))) = pastecart x2 t2 /\
      p (pastecart x1 t1) = p (pastecart x2 t2)`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
           can (term_match [] `!x. x IN (m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]
                                   ==> (q:real^N->real^(N,1)finite_sum)
                                         ((p:real^(N,1)finite_sum->real^N) x) = x`) (concl th)
          then MATCH_MP_TAC th else failwith "") THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
           can (term_match [] `!x. x IN (m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]
                                   ==> (q:real^N->real^(N,1)finite_sum)
                                         ((p:real^(N,1)finite_sum->real^N) x) = x`) (concl th)
          then MATCH_MP_TAC th else failwith "") THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        UNDISCH_TAC `(y:real^N) = (p:real^(N,1)finite_sum->real^N) (pastecart x1 t1)` THEN
        UNDISCH_TAC `(y:real^N) = (p:real^(N,1)finite_sum->real^N) (pastecart x2 t2)` THEN
        MESON_TAC[]];
      MESON_TAC[]];
    ASM_REWRITE_TAC[PASTECART_INJ; LIFT_EQ] THEN REAL_ARITH_TAC]);;

let MOI_FSC_EN_UNIONS2 = prove
 (`!(a:A->bool) b. UNIONS {(if i = 0 then a else b) | i <= 1} = a UNION b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNION] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(x:A) IN s` THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN SIMP_TAC[];
    STRIP_TAC THENL
     [EXISTS_TAC `a:A->bool` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN ARITH_TAC;
      EXISTS_TAC `b:A->bool` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `1` THEN ARITH_TAC]]);;

(* Distinct slices of a product are disjoint; a point of a bicollar level.  *)

let MOI_FSC_EN_SLICES_DISJ = prove
 (`!(s:real^M->bool) (a:real^N) b.
     ~(a = b) ==> DISJOINT (s PCROSS {a}) (s PCROSS {b})`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; FORALL_PASTECART;
              PASTECART_IN_PCROSS; IN_SING] THEN
  MESON_TAC[]);;

let MOI_FSC_EN_LEVEL_MEM = prove
 (`!(m:real^N->bool) (p:real^(N,1)finite_sum->real^N) sigma sigma' x t.
     pl_homeomorphism (relative_frontier std_triangle,m) (sigma,sigma') /\
     x IN relative_frontier std_triangle
     ==> p(pastecart (sigma x) (lift t)) IN moi_s26_level m p t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism; moi_s26_level] THEN
  STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING] THEN ASM SET_TAC[]);;

(* The PLH G0 from Z x [1,2] onto E given by HOLED_EXT: it agrees with the  *)
(* strip at level -1/2 on Z x {1} and carries Z x {2} onto the level 1/2.   *)

let MOI_FSC_EN_G0 = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q sigma sigma' E
    (f:real^2->real^N) f'.
     moi_s26_bicollar m w p q /\ pl_polyhedron m /\ pl_sphere 1 m /\
     pl_homeomorphism (relative_frontier std_triangle,m) (sigma,sigma') /\
     pl_homeomorphism (holed_disk_model 1,E) (f,f') /\
     IMAGE f (frontier (holed_disk_model 1)) =
     moi_s26_level m p (--(&1 / &2)) UNION moi_s26_level m p (&1 / &2)
     ==> ?G0 G0'. pl_homeomorphism
                    (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)],E)
                    (G0,G0') /\
                  (!x. x IN relative_frontier std_triangle
                       ==> G0(pastecart x (lift(&1))) =
                           p(pastecart (sigma x) (lift(--(&1 / &2))))) /\
                  IMAGE G0 (relative_frontier std_triangle PCROSS {lift(&2)}) =
                  moi_s26_level m p (&1 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `h:real^2->real^(2,1)finite_sum`
    (X_CHOOSE_THEN `h':real^(2,1)finite_sum->real^2` STRIP_ASSUME_TAC)
    MOI_FSC_EN_MODEL_CHART THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`; `sigma:real^2->real^N`;
                 `sigma':real^N->real^2`] MOI_FSC_EN_LEVELS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lev") ASSUME_TAC) THEN
  SUBGOAL_THEN
   `pl_sphere 1 (moi_s26_level (m:real^N->bool) (p:real^(N,1)finite_sum->real^N)
                   (--(&1 / &2))) /\
    pl_sphere 1 (moi_s26_level m p (&1 / &2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "lev" (MP_TAC o SPEC `--(&1 / &2)`);
      USE_THEN "lev" (MP_TAC o SPEC `&1 / &2`)] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (relative_frontier std_triangle PCROSS {lift(&1)})
             (relative_frontier std_triangle PCROSS {lift(&2)})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSC_EN_SLICES_DISJ THEN REWRITE_TAC[LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`; `sigma:real^2->real^N`;
                 `sigma':real^N->real^2`; `--(&1 / &2)`] MOI_FSC_EN_LEVEL_PLH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism
      (relative_frontier std_triangle PCROSS {lift(&1)},
       moi_s26_level (m:real^N->bool) (p:real^(N,1)finite_sum->real^N) (--(&1 / &2)))
      ((\x. p(pastecart ((sigma:real^2->real^N) x) (lift(--(&1 / &2))))) o
       (fstcart:real^(2,1)finite_sum->real^2),
       (\x:real^2. pastecart x (lift(&1))) o
       (\y. (sigma':real^N->real^2)(fstcart((q:real^N->real^(N,1)finite_sum) y))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier std_triangle` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN REWRITE_TAC[MOI_FSC_EN_SLICE_SPHERE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`1`; `relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]`;
    `E:real^N->bool`; `h:real^2->real^(2,1)finite_sum`; `h':real^(2,1)finite_sum->real^2`;
    `f:real^2->real^N`; `f':real^N->real^2`;
    `\i. if i = 0 then relative_frontier std_triangle PCROSS {lift(&1)}
         else relative_frontier std_triangle PCROSS {lift(&2)}`;
    `\i. if i = 0
         then moi_s26_level (m:real^N->bool) (p:real^(N,1)finite_sum->real^N) (--(&1 / &2))
         else moi_s26_level m p (&1 / &2)`;
    `0`;
    `(\x. (p:real^(N,1)finite_sum->real^N)(pastecart ((sigma:real^2->real^N) x)
                                                     (lift(--(&1 / &2))))) o
     (fstcart:real^(2,1)finite_sum->real^2)`;
    `(\x:real^2. pastecart x (lift(&1))) o
     (\y. (sigma':real^N->real^2)(fstcart((q:real^N->real^(N,1)finite_sum) y)))`]
   HOLED_EXT) THEN
  REWRITE_TAC[MOI_FSC_EN_UNIONS2; LE_0] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[MOI_FSC_EN_SLICE_SPHERE];
      REWRITE_TAC[ARITH_RULE `i <= 1 /\ i' <= 1 /\ ~(i = i') <=>
                              i = 0 /\ i' = 1 \/ i = 1 /\ i' = 0`] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G0:real^(2,1)finite_sum->real^N`
    (X_CHOOSE_THEN `G0':real^N->real^(2,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`G0:real^(2,1)finite_sum->real^N`;
                        `G0':real^N->real^(2,1)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pastecart (x:real^2) (lift(&1)) IN
                  relative_frontier std_triangle PCROSS {lift(&1)}` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING]; ALL_TAC] THEN
    ASM_SIMP_TAC[o_THM; FSTCART_PASTECART];
    FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN REWRITE_TAC[ARITH_EQ; LE_REFL]]);;

(* The top slice of a PLH from Z x [1,2]: a PL parametrisation of its image. *)

let MOI_FSC_EN_TOP_SLICE = prove
 (`!(E:real^N->bool) L G0 G0'.
     pl_homeomorphism
       (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)],E) (G0,G0') /\
     IMAGE G0 (relative_frontier std_triangle PCROSS {lift(&2)}) = L
     ==> pl_homeomorphism (relative_frontier std_triangle,L)
           ((\x. G0(pastecart x (lift(&2)))),(\y. fstcart(G0' y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(CONJUNCT2(SPEC `lift(&2)` MOI_FSC_EN_SLICE_SPHERE)) THEN DISCH_TAC THEN
  SUBGOAL_THEN `locally_polyhedral (relative_frontier std_triangle PCROSS {lift(&2)})`
  ASSUME_TAC THENL
   [MP_TAC(CONJUNCT2(SPEC `lift(&2)` MOI_FSC_EN_SLICE_SPHERE)) THEN
    REWRITE_TAC[pl_homeomorphism] THEN MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]`;
                 `E:real^N->bool`; `G0:real^(2,1)finite_sum->real^N`;
                 `G0':real^N->real^(2,1)finite_sum`;
                 `relative_frontier std_triangle PCROSS {lift(&2)}`]
                MOI_FPS_PLH_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SING_SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MATCH_MP_TAC MOI_FSC_EN_PLH_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(G0:real^(2,1)finite_sum->real^N) o (\x:real^2. pastecart x (lift(&2)))`;
    `(fstcart:real^(2,1)finite_sum->real^2) o (G0':real^N->real^(2,1)finite_sum)`] THEN
  REWRITE_TAC[o_THM] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier std_triangle PCROSS {lift(&2)}` THEN ASM_REWRITE_TAC[]);;

(* A PL self-homeomorphism of Z preserves or reverses the cyclic order.     *)

let MOI_FSC_EN_DICHOT_PLH = prove
 (`!q q'. pl_homeomorphism (relative_frontier std_triangle,relative_frontier std_triangle)
                           (q,q')
          ==> moi_s3ci_cycpres q \/ moi_s3ci_cycrev q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S3CI_DICHOT THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Two PL parametrisations bp, ap of one end j0 of an annulus k: a PL        *)
(* self-homeomorphism of k fixing the other end j1 carries bp to ap, or to   *)
(* ap composed with the reflection rho (MOI_S3CI_DICHOT and _COLLAR_DEF).   *)

let MOI_FSC_EN_ADJUST = prove
 (`!(k:real^N->bool) j0 j1 bp bp' ap ap'.
     pl_annulus_with_ends k j0 j1 /\
     pl_homeomorphism (relative_frontier std_triangle,j0) (bp,bp') /\
     pl_homeomorphism (relative_frontier std_triangle,j0) (ap,ap')
     ==> ?g g'. pl_homeomorphism (k,k) (g,g') /\
                (!x. x IN j1 ==> g x = x) /\
                ((!x. x IN relative_frontier std_triangle ==> g(bp x) = ap x) \/
                 (!x. x IN relative_frontier std_triangle
                      ==> g(bp x) = ap(vector[x$2; x$1])))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN relative_frontier std_triangle
        ==> (bp':real^N->real^2) ((bp:real^2->real^N) x) = x /\ bp x IN (j0:real^N->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`relative_frontier std_triangle`; `j0:real^N->bool`; `bp:real^2->real^N`;
                   `bp':real^N->real^2`] MOI_PL2_PL_HOMEO_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PL2_PL_HOMEO_LINV THEN
      MAP_EVERY EXISTS_TAC [`relative_frontier std_triangle`; `j0:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      SUBST1_TAC(SYM(ASSUME `IMAGE (bp:real^2->real^N) (relative_frontier std_triangle) =
                             j0`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (j0:real^N->bool,relative_frontier std_triangle)
                     ((bp':real^N->real^2),(bp:real^2->real^N))`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s3ci_cycpres ((bp':real^N->real^2) o (ap:real^2->real^N)) \/
    moi_s3ci_cycrev (bp' o ap)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSC_EN_DICHOT_PLH THEN
    EXISTS_TAC `(ap':real^N->real^2) o (bp:real^2->real^N)` THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `j0:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`k:real^N->bool`; `j0:real^N->bool`; `j1:real^N->bool`;
                   `bp:real^2->real^N`; `bp':real^N->real^2`;
                   `(ap:real^2->real^N) o (bp':real^N->real^2)`;
                   `(bp:real^2->real^N) o (ap':real^N->real^2)`] MOI_S3CI_COLLAR_DEF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
        EXISTS_TAC `relative_frontier std_triangle` THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`(bp':real^N->real^2) o ((ap:real^2->real^N) o bp') o
                        (bp:real^2->real^N)`;
                       `(bp':real^N->real^2) o (ap:real^2->real^N)`] MOI_S3CI_PTWISE) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[o_THM];
          DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN ASM_REWRITE_TAC[]]];
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` (X_CHOOSE_THEN `g':real^N->real^N`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`g:real^N->real^N`; `g':real^N->real^N`] THEN
      ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[o_THM]];
    MP_TAC(ISPECL [`k:real^N->bool`; `j0:real^N->bool`; `j1:real^N->bool`;
                   `bp:real^2->real^N`; `bp':real^N->real^2`;
                   `(ap:real^2->real^N) o (\x:real^2. vector[x$2; x$1]:real^2) o
                    (bp':real^N->real^2)`;
                   `((bp:real^2->real^N) o (\x:real^2. vector[x$2; x$1]:real^2)) o
                    (ap':real^N->real^2)`] MOI_S3CI_COLLAR_DEF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
        EXISTS_TAC `relative_frontier std_triangle` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
        EXISTS_TAC `relative_frontier std_triangle` THEN
        ASM_REWRITE_TAC[MOI_FSC_EN_RHO_PLH];
        MP_TAC(ISPECL [`(bp':real^N->real^2) o
                        ((ap:real^2->real^N) o (\x:real^2. vector[x$2; x$1]:real^2) o bp') o
                        (bp:real^2->real^N)`;
                       `((bp':real^N->real^2) o (ap:real^2->real^N)) o
                        (\x:real^2. vector[x$2; x$1]:real^2)`] MOI_S3CI_PTWISE) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[o_THM];
          DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])] THEN
        MP_TAC(ISPECL [`\x:real^2. vector[x$2; x$1]:real^2`;
                       `(bp':real^N->real^2) o (ap:real^2->real^N)`] MOI_S3CI_COMPOSE) THEN
        ANTS_TAC THENL [REWRITE_TAC[MOI_FSC_EN_RHO_Z]; ALL_TAC] THEN
        DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
        ASM_REWRITE_TAC[MOI_FSC_EN_RHO_REV]];
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` (X_CHOOSE_THEN `g':real^N->real^N`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`g:real^N->real^N`; `g':real^N->real^N`] THEN
      ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[o_THM]]]);;

(* The theorem: G = g o G0, with g from MOI_FSC_EN_ADJUST on the annulus E  *)
(* (ends the levels 1/2 and -1/2), matching the top slice of G0 with the    *)
(* strip at level 1/2, untwisted or twisted, and fixing the level -1/2.     *)

let MOI_FSC_ENDS = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q sigma sigma' E
    (f:real^2->real^N) f'.
     moi_s26_bicollar m w p q /\ pl_polyhedron m /\ pl_sphere 1 m /\
     pl_homeomorphism (relative_frontier std_triangle,m) (sigma,sigma') /\
     pl_homeomorphism (holed_disk_model 1,E) (f,f') /\
     IMAGE f (frontier (holed_disk_model 1)) =
     moi_s26_level m p (--(&1 / &2)) UNION moi_s26_level m p (&1 / &2)
     ==> ?G G'. pl_homeomorphism
                  (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)],E)
                  (G,G') /\
                (!x. x IN relative_frontier std_triangle
                     ==> G(pastecart x (lift(&1))) =
                         p(pastecart (sigma x) (lift(--(&1 / &2))))) /\
                ((!x. x IN relative_frontier std_triangle
                      ==> G(pastecart x (lift(&2))) =
                          p(pastecart (sigma x) (lift(&1 / &2)))) \/
                 (!x. x IN relative_frontier std_triangle
                      ==> G(pastecart x (lift(&2))) =
                          p(pastecart (sigma(vector[x$2; x$1])) (lift(&1 / &2)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`; `sigma:real^2->real^N`;
                 `sigma':real^N->real^2`; `E:real^N->bool`; `f:real^2->real^N`;
                 `f':real^N->real^2`] MOI_FSC_EN_G0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G0:real^(2,1)finite_sum->real^N`
    (X_CHOOSE_THEN `G0':real^N->real^(2,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`E:real^N->bool`;
                 `moi_s26_level (m:real^N->bool) (p:real^(N,1)finite_sum->real^N) (&1 / &2)`;
                 `G0:real^(2,1)finite_sum->real^N`; `G0':real^N->real^(2,1)finite_sum`]
                MOI_FSC_EN_TOP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`; `sigma:real^2->real^N`;
                 `sigma':real^N->real^2`; `&1 / &2`] MOI_FSC_EN_LEVEL_PLH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                 `q:real^N->real^(N,1)finite_sum`; `sigma:real^2->real^N`;
                 `sigma':real^N->real^2`] MOI_FSC_EN_LEVELS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lev") ASSUME_TAC) THEN
  SUBGOAL_THEN
   `pl_annulus_with_ends (E:real^N->bool)
      (moi_s26_level (m:real^N->bool) (p:real^(N,1)finite_sum->real^N) (&1 / &2))
      (moi_s26_level m p (--(&1 / &2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ANNULUS_FROM_HOLED THEN
    MAP_EVERY EXISTS_TAC [`f:real^2->real^N`; `f':real^N->real^2`] THEN
    ONCE_REWRITE_TAC[UNION_COMM] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "lev" (MP_TAC o SPEC `&1 / &2`) THEN
    USE_THEN "lev" (MP_TAC o SPEC `--(&1 / &2)`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`E:real^N->bool`;
    `moi_s26_level (m:real^N->bool) (p:real^(N,1)finite_sum->real^N) (&1 / &2)`;
    `moi_s26_level (m:real^N->bool) (p:real^(N,1)finite_sum->real^N) (--(&1 / &2))`;
    `\x. (G0:real^(2,1)finite_sum->real^N)(pastecart x (lift(&2)))`;
    `\y. fstcart((G0':real^N->real^(2,1)finite_sum) y)`;
    `\x. (p:real^(N,1)finite_sum->real^N)(pastecart ((sigma:real^2->real^N) x) (lift(&1 / &2)))`;
    `\y. (sigma':real^N->real^2)(fstcart((q:real^N->real^(N,1)finite_sum) y))`]
   MOI_FSC_EN_ADJUST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` (X_CHOOSE_THEN `g':real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dis"))))) THEN
  MAP_EVERY EXISTS_TAC [`(g:real^N->real^N) o (G0:real^(2,1)finite_sum->real^N)`;
                        `(G0':real^N->real^(2,1)finite_sum) o (g':real^N->real^N)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `E:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(p:real^(N,1)finite_sum->real^N)(pastecart ((sigma:real^2->real^N) x)
                                                 (lift(--(&1 / &2)))) IN
      moi_s26_level (m:real^N->bool) p (--(&1 / &2))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FSC_EN_LEVEL_MEM THEN EXISTS_TAC `sigma':real^N->real^2` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    USE_THEN "dis" ACCEPT_TAC]);;

(* ========================================================================= *)
(* MOI_FSC_NO_KLEIN: the twisted matching G(x,2) = p(sigma(rho x),1/2),     *)
(* rho x = vector[x$2; x$1], contradicts orientability.  Route: the curve J' *)
(* through the fibres over the rho-fixed point vec 0 is a PL circle (two PL  *)
(* arcs with common ends), so it has a bicollar (CURVE_BICOLLAR_ORIENTABLE); *)
(* a thin neighbourhood N of J' over a small arc I of Z around vec 0 lies in *)
(* that bicollar (uniform continuity) and N minus J' is connected (rho       *)
(* exchanges the two halves of I: a Moebius band), while a neighbourhood of  *)
(* a point of J' in UNIONS c lies in N (the rest of UNIONS c is covered by   *)
(* compact images avoiding the point); the bicollar coordinate then has a    *)
(* constant sign on N minus J' and both signs next to J'. The lemmas:        *)
(* MOI_FSC_NK_CONNECTED_SIGN, MOI_FSC_NK_BICOLLAR_COORDS and                 *)
(* MOI_FSC_NK_NOT_TWO_SIDED (the last one stated for one point y0 of the     *)
(* curve), then MOI_FSC_NK_JCIRCLE (two PL arcs give a bicollar) and         *)
(* likewise ZFACTS (facts about Z), THIN (uniform continuity), AVOID,        *)
(* HALF_EDGES, CONN (N minus J' is connected), NBHD (a neighbourhood of      *)
(* P(vec 0,0) inside N), FIBRE_ARC (fibres of PL maps are PL arcs), CORE     *)
(* (the abstract contradiction) and the theorem, with P = p o (sigma x id)   *)
(* and S the open strip.                                                     *)
(* ========================================================================= *)

let MOI_FSC_NK_CONNECTED_SIGN = prove
 (`!(f:real^N->real) s a b.
     connected s /\ (\x. lift(f x)) continuous_on s /\ (!x. x IN s ==> ~(f x = &0)) /\
     a IN s /\ b IN s /\ f a < &0 /\ &0 < f b
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `connected (IMAGE (\x. lift(f x)) (s:real^N->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lift(f(a:real^N)) IN IMAGE (\x. lift(f x)) s /\
                lift(f(b:real^N)) IN IMAGE (\x. lift(f x)) s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THENL
     [EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `f(a:real^N) <= &0 /\ &0 <= f(b:real^N)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\x. lift(f x)) (s:real^N->bool)`; `lift(f(a:real^N))`;
                 `lift(f(b:real^N))`; `&0`; `1`] CONNECTED_IVT_COMPONENT) THEN
  ASM_REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop; LIFT_DROP] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; GSYM drop; LIFT_DROP] THEN ASM_MESON_TAC[]);;

let MOI_FSC_NK_BICOLLAR_COORDS = prove
 (`!(m:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q.
     moi_s26_bicollar m w p q
     ==> (!y. y IN w <=> ?x t. x IN m /\ --(&1) <= drop t /\ drop t <= &1 /\
                               y = p(pastecart x t)) /\
         (!x t. x IN m /\ --(&1) <= drop t /\ drop t <= &1
                ==> q(p(pastecart x t)) = pastecart x t) /\
         (!x t x' t'. x IN m /\ --(&1) <= drop t /\ drop t <= &1 /\
                      x' IN m /\ --(&1) <= drop t' /\ drop t' <= &1 /\
                      p(pastecart x t) = p(pastecart x' t')
                      ==> x = x' /\ t = t') /\
         (!x. x IN m ==> p(pastecart x (vec 0)) = x) /\
         (!y. y IN w ==> q y IN m PCROSS interval[--vec 1,vec 1] /\ p(q y) = y) /\
         p continuous_on (m PCROSS interval[--vec 1,vec 1]) /\ q continuous_on w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!x t. x IN m /\ --(&1) <= drop t /\ drop t <= &1
          ==> (q:real^N->real^(N,1)finite_sum)(p(pastecart x t)) = pastecart x t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "w" THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                DROP_NEG; DROP_VEC] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `pastecart (x:real^N) (t:real^1) = pastecart x' t'` MP_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[PASTECART_INJ]];
    ASM SET_TAC[]]);;

let MOI_FSC_NK_NOT_TWO_SIDED = prove
 (`!(s:real^N->bool) j w (p:real^(N,1)finite_sum->real^N) q N u y0.
     moi_s26_bicollar j w p q /\ w SUBSET s /\ y0 IN j /\
     N SUBSET w /\ connected (N DIFF j) /\ open u /\ y0 IN u /\
     u INTER s SUBSET N
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FSC_NK_BICOLLAR_COORDS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "wco") (CONJUNCTS_THEN2 (LABEL_TAC "qp")
    (CONJUNCTS_THEN2 (LABEL_TAC "pinj") (CONJUNCTS_THEN2 (LABEL_TAC "p0")
    (CONJUNCTS_THEN2 (LABEL_TAC "qw") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
  (* points of the bicollar near y0 on both sides *)
  SUBGOAL_THEN `?r. &0 < r /\ ball(y0:real^N,r) SUBSET u` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^(N,1)finite_sum->real^N)(pastecart y0 (vec 0)) = y0` ASSUME_TAC THENL
   [USE_THEN "p0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ d <= &1 /\
        !t. abs t <= d
            ==> (p:real^(N,1)finite_sum->real^N)(pastecart y0 (lift t)) IN u`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^(N,1)finite_sum->real^N) continuous_on
                 (j PCROSS interval[--vec 1,vec 1])` THEN
    REWRITE_TAC[continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (y0:real^N) (vec 0:real^1)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min (e / &2) (&1)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (y0:real^N) (lift t)`) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP;
                DIST_PASTECART_CANCEL; DIST_0; NORM_LIFT] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^(N,1)finite_sum->real^N)(pastecart y0 (lift t)) IN ball(y0,r)`
    MP_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the bicollar coordinate *)
  ABBREV_TAC `phi = \y:real^N. drop(sndcart((q:real^N->real^(N,1)finite_sum) y))` THEN
  SUBGOAL_THEN
   `!t. abs t <= &1
        ==> (phi:real^N->real) ((p:real^(N,1)finite_sum->real^N)(pastecart y0 (lift t))) = t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXPAND_TAC "phi" THEN
    REWRITE_TAC[] THEN
    USE_THEN "qp" (MP_TAC o SPECL [`y0:real^N`; `lift t`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN N DIFF j ==> ~(phi y = &0)` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((y:real^N) IN j)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^N) IN w` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `drop(sndcart((q:real^N->real^(N,1)finite_sum) y)) = &0` THEN
    USE_THEN "qw" (MP_TAC o SPEC `y:real^N`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`(q:real^N->real^(N,1)finite_sum) y`,`z:real^(N,1)finite_sum`) THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^1`] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM DROP_VEC; DROP_EQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(p:real^(N,1)finite_sum->real^N)(pastecart x (vec 0)) = y` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN USE_THEN "p0" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. abs t <= d /\ ~(t = &0)
        ==> (p:real^(N,1)finite_sum->real^N)(pastecart y0 (lift t)) IN N DIFF j`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!u s. x IN u /\ x IN s /\ u INTER s SUBSET N
                                   ==> (x:real^N) IN N`) THEN
      MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `s:real^N->bool`] THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!w. x IN w /\ w SUBSET s ==> (x:real^N) IN s`) THEN
      EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "wco" (fun th -> REWRITE_TAC[th]) THEN
      MAP_EVERY EXISTS_TAC [`y0:real^N`; `lift t`] THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      USE_THEN "pinj" (MP_TAC o SPECL
        [`y0:real^N`; `lift t`;
         `(p:real^(N,1)finite_sum->real^N)(pastecart y0 (lift t))`; `vec 0:real^1`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC] THEN
        REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
        CONV_TAC SYM_CONV THEN USE_THEN "p0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^N->real`; `N DIFF j:real^N->bool`;
                 `(p:real^(N,1)finite_sum->real^N)(pastecart y0 (lift(--d)))`;
                 `(p:real^(N,1)finite_sum->real^N)(pastecart y0 (lift d))`]
    MOI_FSC_NK_CONNECTED_SIGN) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^N->bool` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(phi:real^N->real)
                    ((p:real^(N,1)finite_sum->real^N)(pastecart y0 (lift(--d)))) = --d`
    SUBST1_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `(phi:real^N->real)
                    ((p:real^(N,1)finite_sum->real^N)(pastecart y0 (lift d))) = d`
    SUBST1_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* Two PL arcs in UNIONS c with common ends and nothing else in common form a *)
(* curve with a bicollar inside UNIONS c, and a neighbourhood of the curve in *)
(* UNIONS c lies in the bicollar.                                            *)

let MOI_FSC_NK_JCIRCLE = prove
 (`!c:(real^N->bool)->bool (h1:real^1->real^N) h2.
     FINITE c /\ combinatorial_manifold 2 c /\ orientable_surface_complex c /\
     arc h1 /\ pl_map_on (interval[vec 0,vec 1]) h1 /\
     arc h2 /\ pl_map_on (interval[vec 0,vec 1]) h2 /\
     pathstart h2 = pathstart h1 /\ pathfinish h2 = pathfinish h1 /\
     path_image h1 INTER path_image h2 = {pathstart h1,pathfinish h1} /\
     path_image h1 SUBSET UNIONS c /\ path_image h2 SUBSET UNIONS c
     ==> ?w' (p':real^(N,1)finite_sum->real^N) q'.
           moi_s26_bicollar (path_image h1 UNION path_image h2) w' p' q' /\
           w' SUBSET UNIONS c /\
           ?U. open U /\ path_image h1 UNION path_image h2 SUBSET U /\
               U INTER UNIONS c SUBSET w'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` SURF_CHARTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_FBC_CM2_CMWB2]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R2") (CONJUNCTS_THEN2 (K ALL_TAC)
    (MP_TAC o C MP (ASSUME `combinatorial_manifold 2 (c:(real^N->bool)->bool)`)))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `pathstart(h1:real^1->real^N)`]
      MOI_S8CU_R2_DIMINDEX) THEN
    USE_THEN "R2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[DIFF_EMPTY] THEN
    UNDISCH_TAC `path_image (h1:real^1->real^N) SUBSET UNIONS c` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[PATHSTART_IN_PATH_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h1:real^1->real^N`; `h2:real^1->real^N`] MOI_SLV_ARCS_SPHERE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `path_image (h1:real^1->real^N) UNION path_image h2` POLYGON_COMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `UNIONS c:real^N->bool`] CURVE_BICOLLAR_ORIENTABLE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_FBC_CM2_CMWB2; OPEN_IN_REFL; DIFF_EMPTY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':real^N->bool` (X_CHOOSE_THEN
    `p':real^(N,1)finite_sum->real^N` (X_CHOOSE_THEN `q':real^N->real^(N,1)finite_sum`
      STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`w':real^N->bool`; `p':real^(N,1)finite_sum->real^N`;
                        `q':real^N->real^(N,1)finite_sum`] THEN
  ASM_REWRITE_TAC[moi_s26_bicollar] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS c:real^N->bool)`; `w':real^N->bool`]
    OPEN_IN_INTERIOR_OF) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS c:real^N->bool)`; `w':real^N->bool`]
    INTERIOR_OF_SUBSET) THEN
  ASM SET_TAC[]);;

(* The reference circle Z = relative_frontier std_triangle near vec 0. *)

let MOI_FSC_NK_ZFACTS = prove
 (`(!s. &0 <= s /\ s <= &1
        ==> vector[s; &0] IN relative_frontier std_triangle /\
            vector[&0; s] IN relative_frontier std_triangle) /\
   (vec 0:real^2) IN relative_frontier std_triangle /\
   compact (relative_frontier std_triangle) /\
   (!x r. x IN relative_frontier std_triangle /\ norm(x:real^2) < r /\ r <= &1 / &2
          ==> (x = vector[x$1; &0] /\ &0 <= x$1 /\ x$1 < r) \/
              (x = vector[&0; x$2] /\ &0 <= x$2 /\ x$2 < r)) /\
   (!s. norm(vector[s; &0]:real^2) <= abs s /\ norm(vector[&0; s]:real^2) <= abs s) /\
   (!s. vector[(vector[s; &0]:real^2)$2; (vector[s; &0]:real^2)$1] = vector[&0; s]:real^2 /\
        vector[(vector[&0; s]:real^2)$2; (vector[&0; s]:real^2)$1] = vector[s; &0]:real^2) /\
   vector[(vec 0:real^2)$2; (vec 0:real^2)$1] = vec 0:real^2`,
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[MOI_LSP_STD_FRONTIER_EXPLICIT; IN_ELIM_THM; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[MOI_LSP_STD_FRONTIER_EXPLICIT; IN_ELIM_THM; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[MOI_LSP_STD_FRONTIER_EXPLICIT; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`x:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`x:real^2`; `2`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `vector[s; &0]:real^2` NORM_LE_L1);
      MP_TAC(ISPEC `vector[&0; s]:real^2` NORM_LE_L1)] THEN
    REWRITE_TAC[DIMINDEX_2; SUM_2; VECTOR_2] THEN REAL_ARITH_TAC;
    REWRITE_TAC[VECTOR_2];
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT]]);;

(* Thin neighbourhoods: the parts of the two parametrizations over a small *)
(* arc of Z around vec 0 stay in any open neighbourhood of the curve.      *)

let MOI_FSC_NK_THIN = prove
 (`!(G:real^(2,1)finite_sum->real^N) P J U.
     G continuous_on (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]) /\
     P continuous_on (relative_frontier std_triangle PCROSS
                      interval[lift(--(&1 / &2)),lift(&1 / &2)]) /\
     compact J /\ open U /\ J SUBSET U /\
     (!t. &1 <= t /\ t <= &2 ==> G(pastecart (vec 0) (lift t)) IN J) /\
     (!t. abs t <= &1 / &2 ==> P(pastecart (vec 0) (lift t)) IN J)
     ==> ?d. &0 < d /\ d <= &1 / &4 /\
             (!x t. x IN relative_frontier std_triangle /\ norm x <= d /\ &1 <= t /\ t <= &2
                    ==> G(pastecart x (lift t)) IN U) /\
             (!x t. x IN relative_frontier std_triangle /\ norm x <= d /\ abs t <= &1 / &2
                    ==> P(pastecart x (lift t)) IN U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`J:real^N->bool`; `(:real^N) DIFF U`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SEP"))) THEN
  SUBGOAL_THEN
   `compact (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]) /\
    compact (relative_frontier std_triangle PCROSS
             interval[lift(--(&1 / &2)),lift(&1 / &2)])`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_PCROSS THEN
    REWRITE_TAC[COMPACT_INTERVAL; MOI_FSC_NK_ZFACTS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^(2,1)finite_sum->real^N`;
                 `relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UG"))) THEN
  MP_TAC(ISPECL [`P:real^(2,1)finite_sum->real^N`;
                 `relative_frontier std_triangle PCROSS
                  interval[lift(--(&1 / &2)),lift(&1 / &2)]`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UP"))) THEN
  EXISTS_TAC `min (min (d1 / &2) (d2 / &2)) (&1 / &4)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^2`; `t:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(G:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift t)) IN J`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!y U. ~((y:real^N) IN (:real^N) DIFF U) ==> y IN U`) THEN DISCH_TAC THEN
    USE_THEN "SEP" (MP_TAC o SPECL
      [`(G:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift t))`;
       `(G:real^(2,1)finite_sum->real^N)(pastecart x (lift t))`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_NOT_LE]] THEN
    USE_THEN "UG" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DIST_PASTECART_CANCEL;
                    DIST_0; MOI_FSC_NK_ZFACTS] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^2`; `t:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(P:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift t)) IN J`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!y U. ~((y:real^N) IN (:real^N) DIFF U) ==> y IN U`) THEN DISCH_TAC THEN
    USE_THEN "SEP" (MP_TAC o SPECL
      [`(P:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift t))`;
       `(P:real^(2,1)finite_sum->real^N)(pastecart x (lift t))`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_NOT_LE]] THEN
    USE_THEN "UP" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DIST_PASTECART_CANCEL;
                    DIST_0; MOI_FSC_NK_ZFACTS] THEN
    ASM_REAL_ARITH_TAC]);;

(* Off the fibres over vec 0, the two parametrizations miss the curve. *)

let MOI_FSC_NK_AVOID = prove
 (`!(G:real^(2,1)finite_sum->real^N) P S x.
     (!x t. x IN relative_frontier std_triangle /\ &1 <= t /\ t <= &2
            ==> ~(G(pastecart x (lift t)) IN S)) /\
     (!x t x' t'. x IN relative_frontier std_triangle /\ &1 <= t /\ t <= &2 /\
                  x' IN relative_frontier std_triangle /\ &1 <= t' /\ t' <= &2 /\
                  G(pastecart x (lift t)) = G(pastecart x' (lift t'))
                  ==> x = x' /\ t = t') /\
     (!x t. x IN relative_frontier std_triangle /\ abs t < &1 / &2
            ==> P(pastecart x (lift t)) IN S) /\
     (!x t x' t'. x IN relative_frontier std_triangle /\ abs t <= &1 / &2 /\
                  x' IN relative_frontier std_triangle /\ abs t' <= &1 / &2 /\
                  P(pastecart x (lift t)) = P(pastecart x' (lift t'))
                  ==> x = x' /\ t = t') /\
     (!x. x IN relative_frontier std_triangle
          ==> G(pastecart x (lift(&1))) = P(pastecart x (lift(--(&1 / &2)))) /\
              G(pastecart x (lift(&2))) = P(pastecart (vector[x$2; x$1]) (lift(&1 / &2)))) /\
     x IN relative_frontier std_triangle /\ ~(x = vec 0) /\
     vector[x$2; x$1] IN relative_frontier std_triangle /\
     vector[(vector[x$2; x$1]:real^2)$2; (vector[x$2; x$1]:real^2)$1] = x
     ==> (!t t'. &1 <= t /\ t <= &2 /\ &1 <= t' /\ t' <= &2
                 ==> ~(G(pastecart x (lift t)) = G(pastecart (vec 0) (lift t')))) /\
         (!t t'. &1 <= t /\ t <= &2 /\ abs t' <= &1 / &2
                 ==> ~(G(pastecart x (lift t)) = P(pastecart (vec 0) (lift t')))) /\
         (!t t'. abs t <= &1 / &2 /\ &1 <= t' /\ t' <= &2
                 ==> ~(P(pastecart x (lift t)) = G(pastecart (vec 0) (lift t')))) /\
         (!t t'. abs t <= &1 / &2 /\ abs t' <= &1 / &2
                 ==> ~(P(pastecart x (lift t)) = P(pastecart (vec 0) (lift t'))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GS") (CONJUNCTS_THEN2 (LABEL_TAC "GI")
   (CONJUNCTS_THEN2 (LABEL_TAC "PS") (CONJUNCTS_THEN2 (LABEL_TAC "PI")
   (CONJUNCTS_THEN2 (LABEL_TAC "M") STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `(vec 0:real^2) IN relative_frontier std_triangle` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_FSC_NK_ZFACTS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(G:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift(&1))) =
    (P:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift(--(&1 / &2)))) /\
    G(pastecart (vec 0) (lift(&2))) = P(pastecart (vec 0) (lift(&1 / &2)))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "M" (MP_TAC o C MP (ASSUME `(vec 0:real^2) IN relative_frontier std_triangle`) o
      SPEC `vec 0:real^2`) THEN
    REWRITE_TAC[MOI_FSC_NK_ZFACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(G:real^(2,1)finite_sum->real^N)(pastecart x (lift(&1))) =
    (P:real^(2,1)finite_sum->real^N)(pastecart x (lift(--(&1 / &2)))) /\
    G(pastecart (vector[x$2; x$1]) (lift(&2))) = P(pastecart x (lift(&1 / &2)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "M" (MP_TAC o C MP (ASSUME `(x:real^2) IN relative_frontier std_triangle`) o
        SPEC `x:real^2`) THEN SIMP_TAC[];
      USE_THEN "M" (MP_TAC o C MP (ASSUME `vector[(x:real^2)$2; x$1] IN
                                           relative_frontier std_triangle`) o
        SPEC `vector[(x:real^2)$2; x$1]:real^2`) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(vector[(x:real^2)$2; x$1] = vec 0:real^2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `vector[(vector[(x:real^2)$2; x$1]:real^2)$2;
                        (vector[x$2; x$1]:real^2)$1] = x` THEN
    ASM_REWRITE_TAC[MOI_FSC_NK_ZFACTS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [(* G against G *)
    DISCH_TAC THEN
    USE_THEN "GI" (MP_TAC o SPECL [`x:real^2`; `t:real`; `vec 0:real^2`; `t':real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    (* G against P *)
    ASM_CASES_TAC `abs t' < &1 / &2` THENL
     [DISCH_TAC THEN
      USE_THEN "PS" (MP_TAC o SPECL [`vec 0:real^2`; `t':real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      USE_THEN "GS" (MP_TAC o SPECL [`x:real^2`; `t:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `t' = --(&1 / &2) \/ t' = &1 / &2` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN DISCH_TAC THENL
     [USE_THEN "GI" (MP_TAC o SPECL [`x:real^2`; `t:real`; `vec 0:real^2`; `&1`]);
      USE_THEN "GI" (MP_TAC o SPECL [`x:real^2`; `t:real`; `vec 0:real^2`; `&2`])] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);
    (* P against G *)
    ASM_CASES_TAC `abs t < &1 / &2` THENL
     [DISCH_TAC THEN
      USE_THEN "PS" (MP_TAC o SPECL [`x:real^2`; `t:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      USE_THEN "GS" (MP_TAC o SPECL [`vec 0:real^2`; `t':real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(P:real^(2,1)finite_sum->real^N)(pastecart x (lift t)) =
                   (G:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift t'))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `t = --(&1 / &2) \/ t = &1 / &2` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN DISCH_TAC THENL
     [USE_THEN "GI" (MP_TAC o SPECL [`x:real^2`; `&1`; `vec 0:real^2`; `t':real`]) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);
      USE_THEN "GI" (MP_TAC o SPECL [`vector[(x:real^2)$2; x$1]:real^2`; `&2`;
                                     `vec 0:real^2`; `t':real`]) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[]])];
    (* P against P *)
    DISCH_TAC THEN
    USE_THEN "PI" (MP_TAC o SPECL [`x:real^2`; `t:real`; `vec 0:real^2`; `t':real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]);;

(* The two half-open edges of Z at vec 0. *)

let MOI_FSC_NK_HALF_EDGES = prove
 (`!d. &0 < d /\ d <= &1 / &4
       ==> (!x. x IN IMAGE (\s. vector[drop s; &0]:real^2) {s | &0 < drop s /\ drop s <= d} <=>
                &0 < x$1 /\ x$1 <= d /\ x = vector[x$1; &0]) /\
           (!x. x IN IMAGE (\s. vector[&0; drop s]:real^2) {s | &0 < drop s /\ drop s <= d} <=>
                &0 < x$2 /\ x$2 <= d /\ x = vector[&0; x$2]) /\
           connected (IMAGE (\s. vector[drop s; &0]:real^2) {s | &0 < drop s /\ drop s <= d}) /\
           connected (IMAGE (\s. vector[&0; drop s]:real^2) {s | &0 < drop s /\ drop s <= d}) /\
           IMAGE (\s. vector[drop s; &0]:real^2) {s | &0 < drop s /\ drop s <= d} SUBSET
           relative_frontier std_triangle /\
           IMAGE (\s. vector[&0; drop s]:real^2) {s | &0 < drop s /\ drop s <= d} SUBSET
           relative_frontier std_triangle`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected {s:real^1 | &0 < drop s /\ drop s <= d}` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_1; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linear (\s:real^1. vector[drop s; &0]:real^2) /\
                linear (\s:real^1. vector[&0; drop s]:real^2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; DROP_ADD; DROP_CMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_2];
      STRIP_TAC THEN EXISTS_TAC `lift((x:real^2)$1)` THEN
      REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    GEN_TAC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_2];
      STRIP_TAC THEN EXISTS_TAC `lift((x:real^2)$2)` THEN
      REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `drop(x:real^1)` (CONJUNCT1 MOI_FSC_NK_ZFACTS)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `drop(x:real^1)` (CONJUNCT1 MOI_FSC_NK_ZFACTS)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

let MOI_FSC_NK_RHO2 = prove
 (`!x:real^2. vector[(vector[x$2; x$1]:real^2)$2; (vector[x$2; x$1]:real^2)$1] = x`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

(* Points of the image of a product with an interval. *)

let MOI_FSC_NK_IN_IMAGE_PCROSS = prove
 (`!(ff:real^(M,1)finite_sum->real^N) (A:real^M->bool) a b y.
       y IN IMAGE ff (A PCROSS interval[lift a,lift b]) <=>
       ?x t. x IN A /\ a <= t /\ t <= b /\ y = ff(pastecart x (lift t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`x:real^M`; `drop(y':real^1)`] THEN ASM_REWRITE_TAC[LIFT_DROP];
    MAP_EVERY EXISTS_TAC [`x:real^M`; `lift t`] THEN ASM_REWRITE_TAC[LIFT_DROP]]);;

(* N minus J is connected: four connected pieces chained through the ends, *)
(* with the twist at level 1/2 (a Moebius band).                           *)

let MOI_FSC_NK_VEC2 = prove
 (`(!x:real^2. x = vector[x$1; &0] <=> x$2 = &0) /\
   (!x:real^2. x = vector[&0; x$2] <=> x$1 = &0) /\
   (!x:real^2. x = vec 0 <=> x$1 = &0 /\ x$2 = &0)`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT]);;

let MOI_FSC_NK_CONN = prove
 (`!(G:real^(2,1)finite_sum->real^N) P S d.
     G continuous_on (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]) /\
     P continuous_on (relative_frontier std_triangle PCROSS
                      interval[lift(--(&1 / &2)),lift(&1 / &2)]) /\
     (!x t. x IN relative_frontier std_triangle /\ &1 <= t /\ t <= &2
            ==> ~(G(pastecart x (lift t)) IN S)) /\
     (!x t x' t'. x IN relative_frontier std_triangle /\ &1 <= t /\ t <= &2 /\
                  x' IN relative_frontier std_triangle /\ &1 <= t' /\ t' <= &2 /\
                  G(pastecart x (lift t)) = G(pastecart x' (lift t'))
                  ==> x = x' /\ t = t') /\
     (!x t. x IN relative_frontier std_triangle /\ abs t < &1 / &2
            ==> P(pastecart x (lift t)) IN S) /\
     (!x t x' t'. x IN relative_frontier std_triangle /\ abs t <= &1 / &2 /\
                  x' IN relative_frontier std_triangle /\ abs t' <= &1 / &2 /\
                  P(pastecart x (lift t)) = P(pastecart x' (lift t'))
                  ==> x = x' /\ t = t') /\
     (!x. x IN relative_frontier std_triangle
          ==> G(pastecart x (lift(&1))) = P(pastecart x (lift(--(&1 / &2)))) /\
              G(pastecart x (lift(&2))) = P(pastecart (vector[x$2; x$1]) (lift(&1 / &2)))) /\
     &0 < d /\ d <= &1 / &4
     ==> connected
          ((IMAGE G {pastecart x (lift t) | x IN relative_frontier std_triangle /\
                                            norm x <= d /\ &1 <= t /\ t <= &2} UNION
            IMAGE P {pastecart x (lift t) | x IN relative_frontier std_triangle /\
                                            norm x <= d /\ abs t <= &1 / &2}) DIFF
           (IMAGE G {pastecart (vec 0) (lift t) | &1 <= t /\ t <= &2} UNION
            IMAGE P {pastecart (vec 0) (lift t) | abs t <= &1 / &2}))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP (MESON[]
    `(a /\ b /\ c /\ d /\ e /\ f /\ g /\ h) ==> (c /\ d /\ e /\ f /\ g)`) th)) THEN
  DISCH_THEN(LABEL_TAC "AV") THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "GS") (CONJUNCTS_THEN2 (LABEL_TAC "GI")
   (CONJUNCTS_THEN2 (LABEL_TAC "PS") (CONJUNCTS_THEN2 (LABEL_TAC "PI")
   (CONJUNCTS_THEN2 (LABEL_TAC "M") STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(SPEC `d:real` MOI_FSC_NK_HALF_EDGES) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A1 = IMAGE (\s. vector[drop s; &0]:real^2) {s | &0 < drop s /\ drop s <= d}` THEN
  ABBREV_TAC `A2 = IMAGE (\s. vector[&0; drop s]:real^2) {s | &0 < drop s /\ drop s <= d}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A1") (CONJUNCTS_THEN2 (LABEL_TAC "A2")
    STRIP_ASSUME_TAC)) THEN
  (* the points of the half edges: off vec 0, reflected into Z, short *)
  SUBGOAL_THEN
   `!x. x IN A1 \/ x IN A2
        ==> x IN relative_frontier std_triangle /\ ~(x = vec 0) /\
            vector[(x:real^2)$2; x$1] IN relative_frontier std_triangle /\ norm x <= d`
  (LABEL_TAC "AX") THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THENL
     [USE_THEN "A1" (MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `&0 < (x:real^2)$1` THEN
        ASM_REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_2] THEN CONJ_TAC THENL
       [MP_TAC(SPEC `(x:real^2)$1` (CONJUNCT1 MOI_FSC_NK_ZFACTS)) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MP_TAC(SPEC `(x:real^2)$1` (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2
          (CONJUNCT2 MOI_FSC_NK_ZFACTS)))))) THEN
        ASM_REAL_ARITH_TAC];
      USE_THEN "A2" (MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `&0 < (x:real^2)$2` THEN
        ASM_REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_2] THEN CONJ_TAC THENL
       [MP_TAC(SPEC `(x:real^2)$2` (CONJUNCT1 MOI_FSC_NK_ZFACTS)) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MP_TAC(SPEC `(x:real^2)$2` (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2
          (CONJUNCT2 MOI_FSC_NK_ZFACTS)))))) THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN A1 \/ x IN A2
        ==> (!t t'. &1 <= t /\ t <= &2 /\ &1 <= t' /\ t' <= &2
                    ==> ~((G:real^(2,1)finite_sum->real^N)(pastecart x (lift t)) =
                          G(pastecart (vec 0) (lift t')))) /\
            (!t t'. &1 <= t /\ t <= &2 /\ abs t' <= &1 / &2
                    ==> ~(G(pastecart x (lift t)) = P(pastecart (vec 0) (lift t')))) /\
            (!t t'. abs t <= &1 / &2 /\ &1 <= t' /\ t' <= &2
                    ==> ~(P(pastecart x (lift t)) = G(pastecart (vec 0) (lift t')))) /\
            (!t t'. abs t <= &1 / &2 /\ abs t' <= &1 / &2
                    ==> ~(P(pastecart x (lift t)) = P(pastecart (vec 0) (lift t'))))`
  (LABEL_TAC "OFF") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "AX" (MP_TAC o C MP (ASSUME `(x:real^2) IN A1 \/ x IN A2`) o SPEC `x:real^2`) THEN
    STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`G:real^(2,1)finite_sum->real^N`; `P:real^(2,1)finite_sum->real^N`;
                         `S:real^N->bool`; `x:real^2`] MOI_FSC_NK_AVOID) THEN
    USE_THEN "AV" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[MOI_FSC_NK_RHO2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(ff:real^(2,1)finite_sum->real^N) A a b y.
       y IN IMAGE ff (A PCROSS interval[lift a,lift b]) <=>
       ?x t. x IN A /\ a <= t /\ t <= b /\ y = ff(pastecart x (lift t))`
  (LABEL_TAC "PC") THENL
   [REWRITE_TAC[MOI_FSC_NK_IN_IMAGE_PCROSS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(IMAGE (G:real^(2,1)finite_sum->real^N)
       {pastecart x (lift t) | x IN relative_frontier std_triangle /\
                               norm x <= d /\ &1 <= t /\ t <= &2} UNION
     IMAGE (P:real^(2,1)finite_sum->real^N)
       {pastecart x (lift t) | x IN relative_frontier std_triangle /\
                               norm x <= d /\ abs t <= &1 / &2}) DIFF
    (IMAGE G {pastecart (vec 0) (lift t) | &1 <= t /\ t <= &2} UNION
     IMAGE P {pastecart (vec 0) (lift t) | abs t <= &1 / &2}) =
    ((IMAGE P (A1 PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)]) UNION
      IMAGE G (A1 PCROSS interval[lift(&1),lift(&2)])) UNION
     IMAGE P (A2 PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)])) UNION
    IMAGE G (A2 PCROSS interval[lift(&1),lift(&2)])`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `y:real^N` THEN USE_THEN "PC" (fun th -> REWRITE_TAC[th; IN_UNION; IN_DIFF]) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THENL
     [(* N minus J lies in the pieces *)
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "nJ")) THEN
      DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `z:real^(2,1)finite_sum`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `t:real`
          (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC)))))) THEN
      (ASM_CASES_TAC `x:real^2 = vec 0` THENL
        [USE_THEN "nJ" MP_TAC THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
         FIRST_X_ASSUM SUBST_ALL_TAC THEN
         ((DISJ1_TAC THEN EXISTS_TAC `pastecart (vec 0:real^2) (lift t)` THEN
           REWRITE_TAC[] THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[]) ORELSE
          (DISJ2_TAC THEN EXISTS_TAC `pastecart (vec 0:real^2) (lift t)` THEN
           REWRITE_TAC[] THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[]));
         ALL_TAC]) THEN
      MP_TAC(SPECL [`x:real^2`; `&1 / &2`] (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2
        MOI_FSC_NK_ZFACTS))))) THEN
      (ANTS_TAC THENL
        [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `norm(x:real^2) <= d` THEN
         UNDISCH_TAC `d <= &1 / &4` THEN REAL_ARITH_TAC;
         ALL_TAC]) THEN
      MP_TAC(ISPECL [`x:real^2`; `1`] COMPONENT_LE_NORM) THEN
      MP_TAC(ISPECL [`x:real^2`; `2`] COMPONENT_LE_NORM) THEN
      UNDISCH_TAC `~(x:real^2 = vec 0)` THEN UNDISCH_TAC `norm(x:real^2) <= d` THEN
      USE_THEN "A1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "A2" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[MOI_FSC_NK_VEC2] THEN
      REPEAT DISCH_TAC THEN
      (SUBGOAL_THEN `(&0 < (x:real^2)$1 /\ x$1 <= d /\ x$2 = &0) \/
                     (&0 < x$2 /\ x$2 <= d /\ x$1 = &0)` MP_TAC THENL
        [MAP_EVERY UNDISCH_TAC
          [`norm(x:real^2) <= d`; `~((x:real^2)$1 = &0 /\ x$2 = &0)`;
           `abs((x:real^2)$2) <= norm x`; `abs((x:real^2)$1) <= norm x`;
           `(x:real^2)$2 = &0 /\ &0 <= x$1 /\ x$1 < &1 / &2 \/
            x$1 = &0 /\ &0 <= x$2 /\ x$2 < &1 / &2`] THEN
         REAL_ARITH_TAC;
         ALL_TAC]) THEN
      STRIP_TAC THENL
       [DISJ1_TAC THEN DISJ1_TAC THEN DISJ2_TAC THEN
        MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN ASM_REWRITE_TAC[];
        DISJ1_TAC THEN DISJ1_TAC THEN DISJ1_TAC THEN
        MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `abs t <= &1 / &2` THEN REAL_ARITH_TAC;
        DISJ1_TAC THEN DISJ2_TAC THEN
        MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `abs t <= &1 / &2` THEN REAL_ARITH_TAC];
      (* the pieces lie in N minus J *)
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `t:real`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
           (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))))) THEN
      (SUBGOAL_THEN `(x:real^2) IN A1 \/ x IN A2` ASSUME_TAC THENL
        [(DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC) ORELSE (DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC);
         ALL_TAC]) THEN
      USE_THEN "AX" (STRIP_ASSUME_TAC o C MP (ASSUME `(x:real^2) IN A1 \/ x IN A2`) o
        SPEC `x:real^2`) THEN
      USE_THEN "OFF" (MP_TAC o C MP (ASSUME `(x:real^2) IN A1 \/ x IN A2`) o SPEC `x:real^2`) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "O1") (CONJUNCTS_THEN2 (LABEL_TAC "O2")
        (CONJUNCTS_THEN2 (LABEL_TAC "O3") (LABEL_TAC "O4")))) THEN
      FIRST
       [(* a point of a G piece *)
        CONJ_TAC THENL
         [DISJ1_TAC THEN EXISTS_TAC `pastecart (x:real^2) (lift t)` THEN REWRITE_TAC[] THEN
          MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
          DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `z:real^(2,1)finite_sum`
            (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real`
              (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC))))) THENL
           [USE_THEN "O1" (MP_TAC o SPECL [`t:real`; `s:real`]);
            USE_THEN "O2" (MP_TAC o SPECL [`t:real`; `s:real`])] THEN
          (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]) THEN NO_TAC];
        (* a point of a P piece *)
        SUBGOAL_THEN `abs t <= &1 / &2` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`--(&1 / &2) <= t`; `t <= &1 / &2`] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        CONJ_TAC THENL
         [DISJ2_TAC THEN EXISTS_TAC `pastecart (x:real^2) (lift t)` THEN REWRITE_TAC[] THEN
          MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN ASM_REWRITE_TAC[];
          DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `z:real^(2,1)finite_sum`
            (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real`
              (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC))))) THENL
           [USE_THEN "O3" (MP_TAC o SPECL [`t:real`; `s:real`]);
            USE_THEN "O4" (MP_TAC o SPECL [`t:real`; `s:real`])] THEN
          (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]])]]];
    ALL_TAC] THEN
  (* the chain of four connected pieces *)
  SUBGOAL_THEN
   `!(ff:real^(2,1)finite_sum->real^N) A a b.
       ff continuous_on (relative_frontier std_triangle PCROSS interval[lift a,lift b]) /\
       connected A /\ A SUBSET relative_frontier std_triangle
       ==> connected (IMAGE ff (A PCROSS interval[lift a,lift b]))`
  (LABEL_TAC "CI") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `relative_frontier std_triangle PCROSS interval[lift a,lift b]` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC CONNECTED_PCROSS THEN ASM_REWRITE_TAC[CONNECTED_INTERVAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vector[d; &0]:real^2) IN A1 /\ (vector[&0; d]:real^2) IN A2`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "A1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "A2" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VECTOR_2; REAL_LE_REFL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vector[d; &0]:real^2) IN relative_frontier std_triangle /\
                (vector[&0; d]:real^2) IN relative_frontier std_triangle`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `d:real` (CONJUNCT1 MOI_FSC_NK_ZFACTS)) THEN ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < d`; `d <= &1 / &4`] THEN REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(G:real^(2,1)finite_sum->real^N)(pastecart (vector[d; &0]) (lift(&1))) =
    (P:real^(2,1)finite_sum->real^N)(pastecart (vector[d; &0]) (lift(--(&1 / &2)))) /\
    G(pastecart (vector[d; &0]) (lift(&2))) = P(pastecart (vector[&0; d]) (lift(&1 / &2))) /\
    G(pastecart (vector[&0; d]) (lift(&1))) = P(pastecart (vector[&0; d]) (lift(--(&1 / &2))))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "M" (MP_TAC o C MP (ASSUME `(vector[d; &0]:real^2) IN
                                         relative_frontier std_triangle`) o
      SPEC `vector[d; &0]:real^2`) THEN
    USE_THEN "M" (MP_TAC o C MP (ASSUME `(vector[&0; d]:real^2) IN
                                         relative_frontier std_triangle`) o
      SPEC `vector[&0; d]:real^2`) THEN
    REWRITE_TAC[VECTOR_2] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
       [USE_THEN "CI" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "CI" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(G:real^(2,1)finite_sum->real^N)(pastecart (vector[d; &0]) (lift(&1)))` THEN
        USE_THEN "PC" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`vector[d; &0]:real^2`; `--(&1 / &2)`] THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          MAP_EVERY EXISTS_TAC [`vector[d; &0]:real^2`; `&1`] THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
      USE_THEN "CI" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
      EXISTS_TAC `(G:real^(2,1)finite_sum->real^N)(pastecart (vector[d; &0]) (lift(&2)))` THEN
      USE_THEN "PC" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
       [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`vector[d; &0]:real^2`; `&2`] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MAP_EVERY EXISTS_TAC [`vector[&0; d]:real^2`; `&1 / &2`] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    USE_THEN "CI" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
    EXISTS_TAC `(G:real^(2,1)finite_sum->real^N)(pastecart (vector[&0; d]) (lift(&1)))` THEN
    USE_THEN "PC" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`vector[&0; d]:real^2`; `--(&1 / &2)`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`vector[&0; d]:real^2`; `&1`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

(* A neighbourhood of the point P(vec 0,0) of J' inside N: the rest of the  *)
(* two pieces is the compact image of the parts with norm x >= d.          *)

let MOI_FSC_NK_NBHD = prove
 (`!(G:real^(2,1)finite_sum->real^N) P S s d.
     G continuous_on (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]) /\
     P continuous_on (relative_frontier std_triangle PCROSS
                      interval[lift(--(&1 / &2)),lift(&1 / &2)]) /\
     (!x t. x IN relative_frontier std_triangle /\ &1 <= t /\ t <= &2
            ==> ~(G(pastecart x (lift t)) IN S)) /\
     (!x t. x IN relative_frontier std_triangle /\ abs t < &1 / &2
            ==> P(pastecart x (lift t)) IN S) /\
     (!x t x' t'. x IN relative_frontier std_triangle /\ abs t <= &1 / &2 /\
                  x' IN relative_frontier std_triangle /\ abs t' <= &1 / &2 /\
                  P(pastecart x (lift t)) = P(pastecart x' (lift t'))
                  ==> x = x' /\ t = t') /\
     s SUBSET
     IMAGE G (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]) UNION
     IMAGE P (relative_frontier std_triangle PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)]) /\
     &0 < d
     ==> ?u. open u /\ P(pastecart (vec 0) (lift(&0))) IN u /\
             u INTER s SUBSET
             (IMAGE G {pastecart x (lift t) | x IN relative_frontier std_triangle /\
                                              norm x <= d /\ &1 <= t /\ t <= &2} UNION
              IMAGE P {pastecart x (lift t) | x IN relative_frontier std_triangle /\
                                              norm x <= d /\ abs t <= &1 / &2})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "GS") (CONJUNCTS_THEN2 (LABEL_TAC "PS")
   (CONJUNCTS_THEN2 (LABEL_TAC "PI") (CONJUNCTS_THEN2 (LABEL_TAC "SC") ASSUME_TAC)))))) THEN
  EXISTS_TAC
   `(:real^N) DIFF
    (IMAGE (G:real^(2,1)finite_sum->real^N)
       ((relative_frontier std_triangle DIFF ball(vec 0:real^2,d)) PCROSS
        interval[lift(&1),lift(&2)]) UNION
     IMAGE (P:real^(2,1)finite_sum->real^N)
       ((relative_frontier std_triangle DIFF ball(vec 0:real^2,d)) PCROSS
        interval[lift(--(&1 / &2)),lift(&1 / &2)]))` THEN
  REPEAT CONJ_TAC THENL
   [(* the complement is open *)
    REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL] THEN SET_TAC[];
      MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[OPEN_BALL; MOI_FSC_NK_ZFACTS];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `relative_frontier std_triangle PCROSS
                  interval[lift(--(&1 / &2)),lift(&1 / &2)]` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL] THEN SET_TAC[];
      MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[OPEN_BALL; MOI_FSC_NK_ZFACTS]];
    (* the point is not in the compact part *)
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNION; MOI_FSC_NK_IN_IMAGE_PCROSS; IN_BALL_0;
                TAUT `~(p \/ q) <=> ~p /\ ~q`; NOT_EXISTS_THM] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `t:real`] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `~((G:real^(2,1)finite_sum->real^N)(pastecart x (lift t)) IN S)` MP_TAC THENL
       [USE_THEN "GS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(P:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift(&0))) IN S`
      MP_TAC THENL
       [USE_THEN "PS" MATCH_MP_TAC THEN REWRITE_TAC[MOI_FSC_NK_ZFACTS] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      USE_THEN "PI" (MP_TAC o SPECL [`vec 0:real^2`; `&0`; `x:real^2`; `t:real`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[MOI_FSC_NK_ZFACTS] THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`--(&1 / &2) <= t`; `t <= &1 / &2`] THEN REAL_ARITH_TAC;
        DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT1) THEN
        UNDISCH_TAC `~(norm(vec 0:real^2) < d)` THEN ASM_REWRITE_TAC[NORM_0]]];
    (* the rest of s lies in N *)
    REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nK") ASSUME_TAC) THEN
    USE_THEN "SC" (MP_TAC o C MP (ASSUME `(y:real^N) IN s`) o SPEC `y:real^N` o
      REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_UNION; MOI_FSC_NK_IN_IMAGE_PCROSS] THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `t:real`
      STRIP_ASSUME_TAC))) THEN
    (SUBGOAL_THEN `norm(x:real^2) <= d` ASSUME_TAC THENL
      [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
       USE_THEN "nK" MP_TAC THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> F`) THEN
       REWRITE_TAC[IN_UNION; MOI_FSC_NK_IN_IMAGE_PCROSS; IN_DIFF; IN_BALL_0] THEN
       ((DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN
         ASM_REWRITE_TAC[] THEN UNDISCH_TAC `d < norm(x:real^2)` THEN REAL_ARITH_TAC) ORELSE
        (DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN
         ASM_REWRITE_TAC[] THEN UNDISCH_TAC `d < norm(x:real^2)` THEN REAL_ARITH_TAC));
       ALL_TAC]) THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THENL
     [DISJ1_TAC THEN EXISTS_TAC `pastecart (x:real^2) (lift t)` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `pastecart (x:real^2) (lift t)` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`--(&1 / &2) <= t`; `t <= &1 / &2`] THEN REAL_ARITH_TAC]]);;

(* A fibre of a PL map injective on the fibre gives a PL arc. *)

let MOI_FSC_NK_FIBRE_ARC = prove
 (`!(ff:real^(M,1)finite_sum->real^N) D (x0:real^M) a b.
     pl_map_on D ff /\
     (!t. a <= t /\ t <= b ==> pastecart x0 (lift t) IN D) /\
     (!t t'. a <= t /\ t <= b /\ a <= t' /\ t' <= b /\
             ff(pastecart x0 (lift t)) = ff(pastecart x0 (lift t')) ==> t = t') /\
     b = a + &1
     ==> arc (\s. ff(pastecart x0 (lift(a + drop s)))) /\
         pl_map_on (interval[vec 0,vec 1]) (\s. ff(pastecart x0 (lift(a + drop s)))) /\
         pathstart (\s. ff(pastecart x0 (lift(a + drop s)))) = ff(pastecart x0 (lift a)) /\
         pathfinish (\s. ff(pastecart x0 (lift(a + drop s)))) = ff(pastecart x0 (lift b)) /\
         path_image (\s. ff(pastecart x0 (lift(a + drop s)))) =
         IMAGE ff {pastecart x0 (lift t) | a <= t /\ t <= b}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inD")
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `pl_map_on (interval[vec 0,vec 1])
                  (\s:real^1. pastecart (x0:real^M) (lift(a + drop s)))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `linepath(pastecart (x0:real^M) (lift a),pastecart x0 (lift(a + &1)))` THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[linepath; GSYM PASTECART_CMUL; PASTECART_ADD; PASTECART_INJ] THEN
    CONJ_TAC THENL
     [VECTOR_ARITH_TAC;
      REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (interval[vec 0,vec 1])
                  (\s. (ff:real^(M,1)finite_sum->real^N)(pastecart (x0:real^M) (lift(a + drop s))))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\s. (ff:real^(M,1)finite_sum->real^N)(pastecart (x0:real^M) (lift(a + drop s)))) =
                  ff o (\s:real^1. pastecart x0 (lift(a + drop s)))` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `D:real^(M,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
    X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN USE_THEN "inD" MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= drop s`; `drop s <= &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[arc; path] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `s':real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    USE_THEN "inj" (MP_TAC o SPECL [`a + drop s`; `a + drop s'`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`&0 <= drop s`; `drop s <= &1`; `&0 <= drop s'`; `drop s' <= &1`] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EQ_ADD_LCANCEL; DROP_EQ]];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[pathstart; DROP_VEC; REAL_ADD_RID];
    REWRITE_TAC[pathfinish; DROP_VEC];
    REWRITE_TAC[path_image; EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `pastecart (x0:real^M) (lift(a + drop s))` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `a + drop s` THEN REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`&0 <= drop s`; `drop s <= &1`] THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `z:real^(M,1)finite_sum` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `t:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC)))) THEN
      EXISTS_TAC `lift(t - a)` THEN REWRITE_TAC[LIFT_DROP; REAL_SUB_ADD2] THEN
      MAP_EVERY UNDISCH_TAC [`a <= t`; `t <= a + &1`] THEN REAL_ARITH_TAC]]);;

(* The abstract core: the twisted gluing of G and P gives a contradiction  *)
(* once J' = |h1| UNION |h2| is a PL circle with a bicollar.               *)

let MOI_FSC_NK_CORE = prove
 (`!c:(real^N->bool)->bool (G:real^(2,1)finite_sum->real^N)
    (P:real^(2,1)finite_sum->real^N) (S:real^N->bool) (h1:real^1->real^N) h2.
     FINITE c /\ combinatorial_manifold 2 c /\ orientable_surface_complex c /\
     G continuous_on (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]) /\
     P continuous_on (relative_frontier std_triangle PCROSS
                      interval[lift(--(&1 / &2)),lift(&1 / &2)]) /\
     (!x t. x IN relative_frontier std_triangle /\ &1 <= t /\ t <= &2
            ==> ~(G(pastecart x (lift t)) IN S)) /\
     (!x t x' t'. x IN relative_frontier std_triangle /\ &1 <= t /\ t <= &2 /\
                  x' IN relative_frontier std_triangle /\ &1 <= t' /\ t' <= &2 /\
                  G(pastecart x (lift t)) = G(pastecart x' (lift t'))
                  ==> x = x' /\ t = t') /\
     (!x t. x IN relative_frontier std_triangle /\ abs t < &1 / &2
            ==> P(pastecart x (lift t)) IN S) /\
     (!x t x' t'. x IN relative_frontier std_triangle /\ abs t <= &1 / &2 /\
                  x' IN relative_frontier std_triangle /\ abs t' <= &1 / &2 /\
                  P(pastecart x (lift t)) = P(pastecart x' (lift t'))
                  ==> x = x' /\ t = t') /\
     (!x. x IN relative_frontier std_triangle
          ==> G(pastecart x (lift(&1))) = P(pastecart x (lift(--(&1 / &2)))) /\
              G(pastecart x (lift(&2))) = P(pastecart (vector[x$2; x$1]) (lift(&1 / &2)))) /\
     UNIONS c SUBSET
     IMAGE G (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]) UNION
     IMAGE P (relative_frontier std_triangle PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)]) /\
     IMAGE G (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]) SUBSET
     UNIONS c /\
     IMAGE P (relative_frontier std_triangle PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)])
     SUBSET UNIONS c /\
     arc h1 /\ pl_map_on (interval[vec 0,vec 1]) h1 /\
     arc h2 /\ pl_map_on (interval[vec 0,vec 1]) h2 /\
     pathstart h1 = G(pastecart (vec 0) (lift(&1))) /\
     pathfinish h1 = G(pastecart (vec 0) (lift(&2))) /\
     pathstart h2 = G(pastecart (vec 0) (lift(&1))) /\
     pathfinish h2 = G(pastecart (vec 0) (lift(&2))) /\
     path_image h1 = IMAGE G {pastecart (vec 0) (lift t) | &1 <= t /\ t <= &2} /\
     path_image h2 = IMAGE P {pastecart (vec 0) (lift t) | abs t <= &1 / &2}
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "GS") (CONJUNCTS_THEN2 (LABEL_TAC "GI")
   (CONJUNCTS_THEN2 (LABEL_TAC "PS") (CONJUNCTS_THEN2 (LABEL_TAC "PI")
   (CONJUNCTS_THEN2 (LABEL_TAC "M") (CONJUNCTS_THEN2 (LABEL_TAC "SC")
   (CONJUNCTS_THEN2 (LABEL_TAC "GC") (CONJUNCTS_THEN2 (LABEL_TAC "PC2")
   STRIP_ASSUME_TAC))))))))))))) THEN
  (* the matching at vec 0 *)
  SUBGOAL_THEN
   `(P:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift(--(&1 / &2)))) =
    (G:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift(&1))) /\
    P(pastecart (vec 0) (lift(&1 / &2))) = G(pastecart (vec 0) (lift(&2)))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "M" (MP_TAC o C MP (CONJUNCT1(CONJUNCT2 MOI_FSC_NK_ZFACTS)) o
      SPEC `vec 0:real^2`) THEN
    REWRITE_TAC[MOI_FSC_NK_ZFACTS] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the two arcs meet exactly in their ends *)
  SUBGOAL_THEN `path_image h1 INTER path_image (h2:real^1->real^N) =
                {pathstart h1,pathfinish h1}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_INSERT; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `z1:real^(2,1)finite_sum` (CONJUNCTS_THEN2 ASSUME_TAC
           (X_CHOOSE_THEN `t1:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC))))
        (X_CHOOSE_THEN `z2:real^(2,1)finite_sum` (CONJUNCTS_THEN2 ASSUME_TAC
           (X_CHOOSE_THEN `t2:real` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))))) THEN
      UNDISCH_TAC `(y:real^N) = (G:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift t1))` THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      ASM_CASES_TAC `abs t2 < &1 / &2` THENL
       [SUBGOAL_THEN `~((G:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift t1)) IN S)`
        MP_TAC THENL
         [USE_THEN "GS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MOI_FSC_NK_ZFACTS]; ALL_TAC] THEN
        SUBGOAL_THEN `(P:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift t2)) IN S`
        MP_TAC THENL
         [USE_THEN "PS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MOI_FSC_NK_ZFACTS]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        SUBGOAL_THEN `t2 = --(&1 / &2) \/ t2 = &1 / &2` (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
         [MAP_EVERY UNDISCH_TAC [`abs t2 <= &1 / &2`; `~(abs t2 < &1 / &2)`] THEN
          REAL_ARITH_TAC;
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]]];
      DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN CONJ_TAC THENL
       [EXISTS_TAC `pastecart (vec 0:real^2) (lift(&1))` THEN REWRITE_TAC[] THEN
        EXISTS_TAC `&1` THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
        EXISTS_TAC `pastecart (vec 0:real^2) (lift(--(&1 / &2)))` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `--(&1 / &2)` THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
        EXISTS_TAC `pastecart (vec 0:real^2) (lift(&2))` THEN REWRITE_TAC[] THEN
        EXISTS_TAC `&2` THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
        EXISTS_TAC `pastecart (vec 0:real^2) (lift(&1 / &2))` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `&1 / &2` THEN REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* both arcs lie in UNIONS c *)
  SUBGOAL_THEN `path_image h1 SUBSET UNIONS c /\
                path_image (h2:real^1->real^N) SUBSET UNIONS c` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (G:real^(2,1)finite_sum->real^N)
                    (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)])` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                  MOI_FSC_NK_ZFACTS] THEN SIMP_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (P:real^(2,1)finite_sum->real^N)
                    (relative_frontier std_triangle PCROSS
                     interval[lift(--(&1 / &2)),lift(&1 / &2)])` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                  MOI_FSC_NK_ZFACTS; REAL_ABS_BOUNDS] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* the bicollar of J' *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h1:real^1->real^N`; `h2:real^1->real^N`]
    MOI_FSC_NK_JCIRCLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':real^N->bool` (X_CHOOSE_THEN `p':real^(N,1)finite_sum->real^N`
    (X_CHOOSE_THEN `q':real^N->real^(N,1)finite_sum` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `compact(path_image h1 UNION path_image (h2:real^1->real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
    ASM_SIMP_TAC[ARC_IMP_PATH];
    ALL_TAC] THEN
  (* a thin neighbourhood N inside U *)
  MP_TAC(ISPECL [`G:real^(2,1)finite_sum->real^N`; `P:real^(2,1)finite_sum->real^N`;
                 `path_image h1 UNION path_image (h2:real^1->real^N)`; `U:real^N->bool`]
    MOI_FSC_NK_THIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNION] THENL [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "GU") (LABEL_TAC "PU"))))) THEN
  MP_TAC(ISPECL [`G:real^(2,1)finite_sum->real^N`; `P:real^(2,1)finite_sum->real^N`;
                 `S:real^N->bool`; `d:real`] MOI_FSC_NK_CONN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`G:real^(2,1)finite_sum->real^N`; `P:real^(2,1)finite_sum->real^N`;
                 `S:real^N->bool`; `UNIONS c:real^N->bool`; `d:real`] MOI_FSC_NK_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(P:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift(&0))) IN
                path_image h1 UNION path_image (h2:real^1->real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `&0` THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (G:real^(2,1)finite_sum->real^N)
      {pastecart x (lift t) | x IN relative_frontier std_triangle /\
                              norm x <= d /\ &1 <= t /\ t <= &2} UNION
    IMAGE (P:real^(2,1)finite_sum->real^N)
      {pastecart x (lift t) | x IN relative_frontier std_triangle /\
                              norm x <= d /\ abs t <= &1 / &2} SUBSET w'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U INTER UNIONS c:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_INTER; UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      USE_THEN "GU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (G:real^(2,1)finite_sum->real^N)
                    (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)])` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      SIMP_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      USE_THEN "PU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (P:real^(2,1)finite_sum->real^N)
                    (relative_frontier std_triangle PCROSS
                     interval[lift(--(&1 / &2)),lift(&1 / &2)])` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                  REAL_ABS_BOUNDS] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`UNIONS c:real^N->bool`; `path_image h1 UNION path_image (h2:real^1->real^N)`;
    `w':real^N->bool`; `p':real^(N,1)finite_sum->real^N`; `q':real^N->real^(N,1)finite_sum`;
    `IMAGE (G:real^(2,1)finite_sum->real^N)
       {pastecart x (lift t) | x IN relative_frontier std_triangle /\
                               norm x <= d /\ &1 <= t /\ t <= &2} UNION
     IMAGE (P:real^(2,1)finite_sum->real^N)
       {pastecart x (lift t) | x IN relative_frontier std_triangle /\
                               norm x <= d /\ abs t <= &1 / &2}`;
    `u:real^N->bool`; `(P:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift(&0)))`]
   MOI_FSC_NK_NOT_TWO_SIDED) THEN
  ASM_REWRITE_TAC[]);;

(* The theorem: the twisted matching contradicts orientability. *)

let MOI_FSC_NO_KLEIN = prove
 (`!c:(real^N->bool)->bool m w (p:real^(N,1)finite_sum->real^N) q sigma sigma' G G'.
     FINITE c /\ combinatorial_manifold 2 c /\ orientable_surface_complex c /\
     moi_s26_bicollar m w p q /\ w SUBSET UNIONS c /\
     pl_polyhedron m /\ pl_sphere 1 m /\
     pl_homeomorphism (relative_frontier std_triangle,m) (sigma,sigma') /\
     pl_homeomorphism
       (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)],
        UNIONS c DIFF moi_s26_strip m p (--(&1 / &2)) (&1 / &2)) (G,G') /\
     (!x. x IN relative_frontier std_triangle
          ==> G(pastecart x (lift(&1))) = p(pastecart (sigma x) (lift(--(&1 / &2))))) /\
     (!x. x IN relative_frontier std_triangle
          ==> G(pastecart x (lift(&2))) =
              p(pastecart (sigma(vector[x$2; x$1])) (lift(&1 / &2))))
     ==> F`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `S = moi_s26_strip (m:real^N->bool) (p:real^(N,1)finite_sum->real^N)
                    (--(&1 / &2)) (&1 / &2)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "BIC")
   (CONJUNCTS_THEN2 (LABEL_TAC "WS") (CONJUNCTS_THEN2 (K ALL_TAC)
   (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "SIG")
   (CONJUNCTS_THEN2 (LABEL_TAC "GH") (CONJUNCTS_THEN2 (LABEL_TAC "G1")
   (LABEL_TAC "G2"))))))))))) THEN
  USE_THEN "BIC" (MP_TAC o REWRITE_RULE[moi_s26_bicollar; pl_homeomorphism; homeomorphism]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "qp")
    (CONJUNCTS_THEN2 (LABEL_TAC "pw") (CONJUNCTS_THEN2 (LABEL_TAC "pc") (K ALL_TAC))))
    (CONJUNCTS_THEN2 (LABEL_TAC "ppl") (K ALL_TAC))) (K ALL_TAC)) THEN
  USE_THEN "SIG" (MP_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "S'S") (CONJUNCTS_THEN2 (LABEL_TAC "Sim")
    (CONJUNCTS_THEN2 (LABEL_TAC "Sc") (CONJUNCTS_THEN2 (LABEL_TAC "SS'")
    (CONJUNCTS_THEN2 (LABEL_TAC "S'im") (K ALL_TAC)))))) (K ALL_TAC)) THEN
  USE_THEN "GH" (MP_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "G'G") (CONJUNCTS_THEN2 (LABEL_TAC "Gim")
    (CONJUNCTS_THEN2 (LABEL_TAC "Gc") (K ALL_TAC)))) (CONJUNCTS_THEN2 (LABEL_TAC "Gpl") (K ALL_TAC))) THEN
  SUBGOAL_THEN `!x. x IN relative_frontier std_triangle ==> (sigma:real^2->real^N) x IN m`
  (LABEL_TAC "SIGM") THENL
   [USE_THEN "Sim" (SUBST1_TAC o SYM) THEN SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN m ==> (sigma':real^N->real^2) y IN relative_frontier std_triangle`
  (LABEL_TAC "SIGZ") THENL
   [USE_THEN "S'im" (SUBST1_TAC o SYM) THEN SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  (* the strip parametrised over Z *)
  ABBREV_TAC `P = \z:real^(2,1)finite_sum.
                    (p:real^(N,1)finite_sum->real^N)
                    (pastecart ((sigma:real^2->real^N)(fstcart z)) (sndcart z))` THEN
  SUBGOAL_THEN `!x t. (P:real^(2,1)finite_sum->real^N)(pastecart x (lift t)) =
                      (p:real^(N,1)finite_sum->real^N)
                      (pastecart ((sigma:real^2->real^N) x) (lift t))`
  (LABEL_TAC "Pd") THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^(2,1)finite_sum->real^N) continuous_on
                (relative_frontier std_triangle PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)])`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(P:real^(2,1)finite_sum->real^N) =
                  (p:real^(N,1)finite_sum->real^N) o
                  (\z. pastecart ((sigma:real^2->real^N)(fstcart z)) (sndcart z))`
    SUBST1_TAC THENL
     [EXPAND_TAC "P" THEN REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(\z. (sigma:real^2->real^N)(fstcart z)) =
                      sigma o (fstcart:real^(2,1)finite_sum->real^2)` SUBST1_TAC THENL
         [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `relative_frontier std_triangle` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                    FSTCART_PASTECART] THEN SIMP_TAC[];
        REWRITE_TAC[ETA_AX] THEN SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; DROP_NEG; DROP_VEC;
                  LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^1`] THEN STRIP_TAC THEN CONJ_TAC THENL
       [USE_THEN "SIGM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MAP_EVERY UNDISCH_TAC [`--(&1 / &2) <= drop(y:real^1)`; `drop(y:real^1) <= &1 / &2`] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the facts about G *)
  SUBGOAL_THEN `!x t. x IN relative_frontier std_triangle /\ &1 <= t /\ t <= &2
                      ==> pastecart x (lift t) IN
                          relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]`
  (LABEL_TAC "inGD") THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x t. x IN relative_frontier std_triangle /\ &1 <= t /\ t <= &2
                      ==> ~((G:real^(2,1)finite_sum->real^N)(pastecart x (lift t)) IN S)`
  (LABEL_TAC "GS") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(G:real^(2,1)finite_sum->real^N)(pastecart x (lift t)) IN UNIONS c DIFF S`
    MP_TAC THENL
     [USE_THEN "Gim" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      USE_THEN "inGD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[IN_DIFF]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x t x' t'. x IN relative_frontier std_triangle /\ &1 <= t /\ t <= &2 /\
                x' IN relative_frontier std_triangle /\ &1 <= t' /\ t' <= &2 /\
                (G:real^(2,1)finite_sum->real^N)(pastecart x (lift t)) =
                G(pastecart x' (lift t'))
                ==> x = x' /\ t = t'`
  (LABEL_TAC "GI") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `pastecart (x:real^2) (lift t) = pastecart x' (lift t')` MP_TAC THENL
     [SUBGOAL_THEN
       `(G':real^N->real^(2,1)finite_sum)
          ((G:real^(2,1)finite_sum->real^N)(pastecart x (lift t))) = pastecart x (lift t) /\
        G'(G(pastecart x' (lift t'))) = pastecart x' (lift t')` MP_TAC THENL
       [CONJ_TAC THEN USE_THEN "G'G" MATCH_MP_TAC THEN USE_THEN "inGD" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN MESON_TAC[]];
      REWRITE_TAC[PASTECART_INJ; LIFT_EQ]];
    ALL_TAC] THEN
  (* the facts about P *)
  SUBGOAL_THEN `!x t. x IN relative_frontier std_triangle /\ abs t < &1 / &2
                      ==> (P:real^(2,1)finite_sum->real^N)(pastecart x (lift t)) IN S`
  (LABEL_TAC "PS") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "Pd" (fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[moi_s26_strip] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM; LIFT_DROP] THEN CONJ_TAC THENL
     [USE_THEN "SIGM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `abs t < &1 / &2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x t x' t'. x IN relative_frontier std_triangle /\ abs t <= &1 / &2 /\
                x' IN relative_frontier std_triangle /\ abs t' <= &1 / &2 /\
                (P:real^(2,1)finite_sum->real^N)(pastecart x (lift t)) =
                P(pastecart x' (lift t'))
                ==> x = x' /\ t = t'`
  (LABEL_TAC "PI") THENL
   [REPEAT GEN_TAC THEN USE_THEN "Pd" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `pastecart ((sigma:real^2->real^N) x) (lift t) IN m PCROSS interval[--vec 1:real^1,vec 1] /\
      pastecart ((sigma:real^2->real^N) x') (lift t') IN m PCROSS interval[--vec 1:real^1,vec 1]`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "SIGM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `abs t <= &1 / &2` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `abs t <= &1 / &2` THEN REAL_ARITH_TAC;
        USE_THEN "SIGM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `abs t' <= &1 / &2` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `abs t' <= &1 / &2` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `pastecart ((sigma:real^2->real^N) x) (lift t) = pastecart (sigma x') (lift t')`
    MP_TAC THENL
     [SUBGOAL_THEN
       `(q:real^N->real^(N,1)finite_sum)((p:real^(N,1)finite_sum->real^N)
          (pastecart ((sigma:real^2->real^N) x) (lift t))) = pastecart (sigma x) (lift t) /\
        q(p(pastecart (sigma x') (lift t'))) = pastecart (sigma x') (lift t')` MP_TAC THENL
       [CONJ_TAC THEN USE_THEN "qp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN MESON_TAC[]];
      REWRITE_TAC[PASTECART_INJ; LIFT_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(sigma':real^N->real^2)((sigma:real^2->real^N) x) = x /\
                    sigma'(sigma x') = x'` MP_TAC THENL
       [CONJ_TAC THEN USE_THEN "S'S" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN MESON_TAC[]]];
    ALL_TAC] THEN
  (* the matching *)
  SUBGOAL_THEN
   `!x. x IN relative_frontier std_triangle
        ==> (G:real^(2,1)finite_sum->real^N)(pastecart x (lift(&1))) =
            (P:real^(2,1)finite_sum->real^N)(pastecart x (lift(--(&1 / &2)))) /\
            G(pastecart x (lift(&2))) = P(pastecart (vector[x$2; x$1]) (lift(&1 / &2)))`
  (LABEL_TAC "M") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN USE_THEN "Pd" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL [USE_THEN "G1" MATCH_MP_TAC; USE_THEN "G2" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* UNIONS c is covered by the two pieces, which lie in it *)
  SUBGOAL_THEN
   `UNIONS c SUBSET
    IMAGE (G:real^(2,1)finite_sum->real^N)
      (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]) UNION
    IMAGE (P:real^(2,1)finite_sum->real^N)
      (relative_frontier std_triangle PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)])`
  (LABEL_TAC "SC") THENL
   [REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN S` THENL
     [DISJ2_TAC THEN
      SUBGOAL_THEN `?y' (s:real^1). y' IN m /\ --(&1 / &2) < drop s /\ drop s < &1 / &2 /\
                                    y = (p:real^(N,1)finite_sum->real^N)(pastecart y' s)`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^N) IN S` THEN EXPAND_TAC "S" THEN
        REWRITE_TAC[moi_s26_strip; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
                    IN_ELIM_THM] THEN MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[MOI_FSC_NK_IN_IMAGE_PCROSS] THEN
      MAP_EVERY EXISTS_TAC [`(sigma':real^N->real^2) y'`; `drop s`] THEN
      USE_THEN "Pd" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[LIFT_DROP] THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "SIGZ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `--(&1 / &2) < drop s` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `drop s < &1 / &2` THEN REAL_ARITH_TAC;
        SUBGOAL_THEN `(sigma:real^2->real^N)((sigma':real^N->real^2) y') = y'`
          (fun th -> ASM_REWRITE_TAC[th]) THEN
        USE_THEN "SS'" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISJ1_TAC THEN USE_THEN "Gim" SUBST1_TAC THEN ASM_REWRITE_TAC[IN_DIFF]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (G:real^(2,1)finite_sum->real^N)
      (relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]) SUBSET UNIONS c`
  (LABEL_TAC "GC") THENL
   [USE_THEN "Gim" SUBST1_TAC THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (P:real^(2,1)finite_sum->real^N)
      (relative_frontier std_triangle PCROSS interval[lift(--(&1 / &2)),lift(&1 / &2)])
    SUBSET UNIONS c`
  (LABEL_TAC "PC2") THENL
   [REWRITE_TAC[SUBSET; MOI_FSC_NK_IN_IMAGE_PCROSS] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "WS" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    USE_THEN "pw" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "SIGM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `--(&1 / &2) <= t` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `t <= &1 / &2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the two arcs of J' *)
  MP_TAC(ISPECL [`G:real^(2,1)finite_sum->real^N`;
                 `relative_frontier std_triangle PCROSS interval[lift(&1),lift(&2)]`;
                 `vec 0:real^2`; `&1`; `&2`] MOI_FSC_NK_FIBRE_ARC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN USE_THEN "inGD" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[MOI_FSC_NK_ZFACTS];
      REPEAT STRIP_TAC THEN
      USE_THEN "GI" (MP_TAC o SPECL [`vec 0:real^2`; `t:real`; `vec 0:real^2`; `t':real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[MOI_FSC_NK_ZFACTS]; SIMP_TAC[]];
      REAL_ARITH_TAC];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `(p:real^(N,1)finite_sum->real^N)(pastecart ((sigma:real^2->real^N)(vec 0))
       (lift(--(&1 / &2)))) =
    (G:real^(2,1)finite_sum->real^N)(pastecart (vec 0) (lift(&1))) /\
    p(pastecart (sigma(vec 0)) (lift(&1 / &2))) = G(pastecart (vec 0) (lift(&2)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THENL
     [USE_THEN "G1" MATCH_MP_TAC THEN REWRITE_TAC[MOI_FSC_NK_ZFACTS];
      USE_THEN "G2" (MP_TAC o C MP (CONJUNCT1(CONJUNCT2 MOI_FSC_NK_ZFACTS)) o
        SPEC `vec 0:real^2`) THEN
      REWRITE_TAC[MOI_FSC_NK_ZFACTS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^(N,1)finite_sum->real^N`;
                 `(m:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]`;
                 `(sigma:real^2->real^N)(vec 0)`; `--(&1 / &2)`; `&1 / &2`]
    MOI_FSC_NK_FIBRE_ARC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "SIGM" MATCH_MP_TAC THEN REWRITE_TAC[MOI_FSC_NK_ZFACTS];
        UNDISCH_TAC `--(&1 / &2) <= t` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `t <= &1 / &2` THEN REAL_ARITH_TAC];
      REPEAT STRIP_TAC THEN
      USE_THEN "PI" (MP_TAC o SPECL [`vec 0:real^2`; `t:real`; `vec 0:real^2`; `t':real`]) THEN
      ANTS_TAC THENL
       [USE_THEN "Pd" (fun th -> REWRITE_TAC[th]) THEN
        ASM_REWRITE_TAC[MOI_FSC_NK_ZFACTS; REAL_ABS_BOUNDS];
        SIMP_TAC[]];
      REAL_ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2im")))))] THEN
  SUBGOAL_THEN
   `path_image (\s. (p:real^(N,1)finite_sum->real^N)
                    (pastecart ((sigma:real^2->real^N)(vec 0)) (lift(--(&1 / &2) + drop s)))) =
    IMAGE (P:real^(2,1)finite_sum->real^N)
      {pastecart (vec 0) (lift t) | abs t <= &1 / &2}`
  ASSUME_TAC THENL
   [REMOVE_THEN "h2im" SUBST1_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; REAL_ABS_BOUNDS] THEN
    USE_THEN "Pd" (fun th -> MESON_TAC[th]);
    REMOVE_THEN "h2im" (K ALL_TAC)] THEN
  MATCH_MP_TAC(ISPECL
   [`c:(real^N->bool)->bool`; `G:real^(2,1)finite_sum->real^N`;
    `P:real^(2,1)finite_sum->real^N`; `S:real^N->bool`;
    `\s:real^1. (G:real^(2,1)finite_sum->real^N)(pastecart (vec 0:real^2) (lift(&1 + drop s)))`;
    `\s:real^1. (p:real^(N,1)finite_sum->real^N)
                (pastecart ((sigma:real^2->real^N)(vec 0)) (lift(--(&1 / &2) + drop s)))`]
   MOI_FSC_NK_CORE) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The main theorem. The non-separating polygon (MOI_FSC_NONSEP_CLOSED), its *)
(* bicollar and the cut annulus (MOI_FSC_CUT_CHART), the product chart of    *)
(* the annulus matching the strip at both ends (MOI_FSC_ENDS, with ORIENT    *)
(* and COLLAR of pc_moi_s33_circ), the twisted case excluded by              *)
(* orientability (MOI_FSC_NO_KLEIN), and the torus assembly                  *)
(* MOI_FSC_TORUS_GLUE.                                                       *)
(* ========================================================================= *)

let SURFACE_EULER_TORUS = prove
 (MOI_FND_SURFACE_TORUS,
  GEN_TAC THEN STRIP_TAC THEN
  (* the non-separating polygon *)
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSC_NONSEP_CLOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* its bicollar *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FSC_BICOLLAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN
    `p:real^(N,1)finite_sum->real^N` (X_CHOOSE_THEN
    `q:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  (* the cut is a holed disk with one hole *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`]
    MOI_FSC_CUT_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `f':real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  (* a parametrisation of the polygon *)
  SUBGOAL_THEN `pl_polyhedron (UNIONS l:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4L_PL_POLYHEDRON_UNIONS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
    UNDISCH_TAC `combinatorial_manifold 1 (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold; lf_simplicial_complex] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `UNIONS l:real^N->bool` MOI_S8PL_SPHERE1_STD) THEN
  ASM_REWRITE_TAC[GSYM std_triangle] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:real^2->real^N` (X_CHOOSE_THEN
    `sigma':real^N->real^2` ASSUME_TAC)) THEN
  (* the two ends *)
  MP_TAC(SPECL
   [`UNIONS l:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
    `q:real^N->real^(N,1)finite_sum`; `sigma:real^2->real^N`; `sigma':real^N->real^2`;
    `UNIONS c DIFF moi_s26_strip (UNIONS l) (p:real^(N,1)finite_sum->real^N)
                                  (--(&1 / &2)) (&1 / &2)`;
    `f:real^2->real^N`; `f':real^N->real^2`] MOI_FSC_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^(2,1)finite_sum->real^N` (X_CHOOSE_THEN
    `G':real^N->real^(2,1)finite_sum` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)))) THENL
   [MATCH_MP_TAC MOI_FSC_TORUS_GLUE THEN
    MAP_EVERY EXISTS_TAC
     [`UNIONS l:real^N->bool`; `w:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
      `q:real^N->real^(N,1)finite_sum`; `sigma:real^2->real^N`; `sigma':real^N->real^2`;
      `G:real^(2,1)finite_sum->real^N`; `G':real^N->real^(2,1)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(TAUT `F ==> p`) THEN MATCH_MP_TAC MOI_FSC_NO_KLEIN THEN
    MAP_EVERY EXISTS_TAC
     [`c:(real^N->bool)->bool`; `UNIONS l:real^N->bool`; `w:real^N->bool`;
      `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`;
      `sigma:real^2->real^N`; `sigma':real^N->real^2`;
      `G:real^(2,1)finite_sum->real^N`; `G':real^N->real^(2,1)finite_sum`] THEN
    ASM_REWRITE_TAC[]]);;

